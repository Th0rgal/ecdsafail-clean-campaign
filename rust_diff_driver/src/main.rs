use alloy_primitives::U256;
use quantum_ecc::circuit::{
    analyze_ops, BitId, Op, OperationType, QubitId, QubitOrBit, RegisterId,
};
use quantum_ecc::sim::Simulator;
use quantum_ecc::weierstrass_elliptic_curve::WeierstrassEllipticCurve;
use sha3::{
    digest::{ExtendableOutput, Update, XofReader},
    Shake256,
};
use std::fs::File;
use std::io::{BufReader, BufWriter, Read, Write};

const MAGIC: &[u8; 8] = b"QECCOPSZ";
const ZSTD_WINDOW_LOG_MAX: u32 = 27;
const OP_BYTES: usize = 56;
const MAX_OPS: u64 = 4_000_000_000;

fn op_kind_from_u32(v: u32) -> Option<OperationType> {
    Some(match v {
        0 => OperationType::Neg,
        1 => OperationType::Register,
        2 => OperationType::AppendToRegister,
        3 => OperationType::BitInvert,
        4 => OperationType::BitStore0,
        5 => OperationType::BitStore1,
        6 => OperationType::X,
        7 => OperationType::Z,
        8 => OperationType::CX,
        9 => OperationType::CZ,
        10 => OperationType::Swap,
        11 => OperationType::R,
        12 => OperationType::Hmr,
        13 => OperationType::CCX,
        14 => OperationType::CCZ,
        15 => OperationType::PushCondition,
        16 => OperationType::PopCondition,
        17 => OperationType::DebugPrint,
        _ => return None,
    })
}

fn read_u64(bytes: &[u8], off: usize) -> u64 {
    u64::from_le_bytes(bytes[off..off + 8].try_into().unwrap())
}

fn serialize_op(op: &Op) -> [u8; OP_BYTES] {
    let mut rec = [0u8; OP_BYTES];
    rec[0..4].copy_from_slice(&(op.kind as u32).to_le_bytes());
    rec[8..16].copy_from_slice(&op.q_control2.0.to_le_bytes());
    rec[16..24].copy_from_slice(&op.q_control1.0.to_le_bytes());
    rec[24..32].copy_from_slice(&op.q_target.0.to_le_bytes());
    rec[32..40].copy_from_slice(&op.c_target.0.to_le_bytes());
    rec[40..48].copy_from_slice(&op.c_condition.0.to_le_bytes());
    rec[48..56].copy_from_slice(&op.r_target.0.to_le_bytes());
    rec
}

fn load_ops(path: &str) -> Result<Vec<Op>, String> {
    let mut file = File::open(path).map_err(|e| format!("open {path}: {e}"))?;
    let mut header = [0u8; MAGIC.len() + 8];
    file.read_exact(&mut header)
        .map_err(|e| format!("{path}: too short to read header: {e}"))?;
    if &header[..MAGIC.len()] != MAGIC {
        return Err(format!("{path}: bad magic"));
    }
    let n = u64::from_le_bytes(header[MAGIC.len()..].try_into().unwrap());
    if n > MAX_OPS {
        return Err(format!("{path}: op count {n} exceeds cap {MAX_OPS}"));
    }
    let n = n as usize;

    let mut dec = zstd::stream::read::Decoder::new(BufReader::new(file))
        .map_err(|e| format!("{path}: zstd init: {e}"))?;
    dec.window_log_max(ZSTD_WINDOW_LOG_MAX)
        .map_err(|e| format!("{path}: zstd window cap: {e}"))?;

    let mut ops = Vec::with_capacity(n);
    let mut rec = [0u8; OP_BYTES];
    for i in 0..n {
        dec.read_exact(&mut rec)
            .map_err(|e| format!("op {i}: short read from compressed body: {e}"))?;
        let kind_raw = u32::from_le_bytes(rec[0..4].try_into().unwrap());
        let kind =
            op_kind_from_u32(kind_raw).ok_or_else(|| format!("op {i}: unknown kind {kind_raw}"))?;
        let op = Op {
            kind,
            q_control2: QubitId(read_u64(&rec, 8)),
            q_control1: QubitId(read_u64(&rec, 16)),
            q_target: QubitId(read_u64(&rec, 24)),
            c_target: BitId(read_u64(&rec, 32)),
            c_condition: BitId(read_u64(&rec, 40)),
            r_target: RegisterId(read_u64(&rec, 48)),
        };
        let validated = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| op.validate()));
        if validated.is_err() {
            return Err(format!("op {i}: validation panic"));
        }
        ops.push(op);
    }
    let mut extra = [0u8; 1];
    match dec.read(&mut extra) {
        Ok(0) => {}
        Ok(_) => return Err(format!("{path}: trailing data after {n} ops")),
        Err(e) => return Err(format!("{path}: error checking trailing data: {e}")),
    }
    Ok(ops)
}

fn secp256k1() -> WeierstrassEllipticCurve {
    WeierstrassEllipticCurve {
        modulus: U256::from_str_radix(
            "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F",
            16,
        )
        .unwrap(),
        a: U256::from(0),
        b: U256::from(7),
        gx: U256::from_str_radix(
            "79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798",
            16,
        )
        .unwrap(),
        gy: U256::from_str_radix(
            "483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8",
            16,
        )
        .unwrap(),
        order: U256::from_str_radix(
            "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141",
            16,
        )
        .unwrap(),
    }
}

fn fiat_shamir_seed(ops: &[Op]) -> sha3::Shake256Reader {
    let mut hasher = Shake256::default();
    hasher.update(b"quantum_ecc-fiat-shamir-v2");
    hasher.update(&(ops.len() as u64).to_le_bytes());
    for op in ops {
        hasher.update(&[op.kind as u8]);
        hasher.update(&op.q_control2.0.to_le_bytes());
        hasher.update(&op.q_control1.0.to_le_bytes());
        hasher.update(&op.q_target.0.to_le_bytes());
        hasher.update(&op.c_target.0.to_le_bytes());
        hasher.update(&op.c_condition.0.to_le_bytes());
        hasher.update(&op.r_target.0.to_le_bytes());
    }
    hasher.finalize_xof()
}

struct SliceXofReader {
    words: Vec<u64>,
    idx: usize,
}

impl sha3::digest::XofReader for SliceXofReader {
    fn read(&mut self, buffer: &mut [u8]) {
        assert_eq!(buffer.len(), 8);
        let w = self.words[self.idx];
        self.idx += 1;
        buffer.copy_from_slice(&w.to_le_bytes());
    }
}

fn write_diff_case<W: Write>(
    w: &mut W,
    name: &str,
    init_phase: u64,
    init_qubits: &[u64],
    init_bits: &[u64],
    ops: &[Op],
    seed_tag: &[u8],
) -> std::io::Result<()> {
    for op in ops {
        op.validate();
    }
    let (ana_q, ana_b, ana_r, ana_regs) = analyze_ops(ops.iter());
    let num_q = (ana_q as usize).max(init_qubits.len());
    let num_b = (ana_b as usize).max(init_bits.len());

    let mut q_init = vec![0u64; num_q];
    q_init[..init_qubits.len()].copy_from_slice(init_qubits);
    let mut b_init = vec![0u64; num_b];
    b_init[..init_bits.len()].copy_from_slice(init_bits);

    let rng_count = ops
        .iter()
        .filter(|op| matches!(op.kind, OperationType::R | OperationType::Hmr))
        .count();

    let mut hasher = Shake256::default();
    hasher.update(b"ecdsa-lean-diff-suite-v1");
    hasher.update(seed_tag);
    let mut xof = hasher.finalize_xof();
    let mut rng_words = Vec::with_capacity(rng_count);
    for _ in 0..rng_count {
        let mut buf = [0u8; 8];
        XofReader::read(&mut xof, &mut buf);
        rng_words.push(u64::from_le_bytes(buf));
    }

    let mut slice_xof = SliceXofReader {
        words: rng_words.clone(),
        idx: 0,
    };
    let mut sim = Simulator::new(num_q, num_b, &mut slice_xof);
    sim.phase = init_phase;
    sim.qubits.copy_from_slice(&q_init);
    sim.bits.copy_from_slice(&b_init);
    sim.apply_iter(ops.iter());
    let final_phase = sim.phase;
    let final_toffoli = sim.stats.toffoli_gates;
    let final_clifford = sim.stats.clifford_gates;
    let final_qubits = sim.qubits.clone();
    let final_bits = sim.bits.clone();
    drop(sim);
    assert_eq!(slice_xof.idx, rng_count);

    // Flatten register items as (reg_idx, is_bit, id)
    let mut reg_items: Vec<(u64, u64, u64)> = Vec::new();
    for (r_idx, reg) in ana_regs.iter().enumerate() {
        for item in reg {
            match *item {
                QubitOrBit::Qubit(qid) => reg_items.push((r_idx as u64, 0, qid.0)),
                QubitOrBit::Bit(bid) => reg_items.push((r_idx as u64, 1, bid.0)),
            }
        }
    }

    let name_bytes = name.as_bytes();
    w.write_all(&(name_bytes.len() as u64).to_le_bytes())?;
    w.write_all(name_bytes)?;
    w.write_all(&init_phase.to_le_bytes())?;
    w.write_all(&(q_init.len() as u64).to_le_bytes())?;
    w.write_all(&(b_init.len() as u64).to_le_bytes())?;
    for &v in &q_init {
        w.write_all(&v.to_le_bytes())?;
    }
    for &v in &b_init {
        w.write_all(&v.to_le_bytes())?;
    }
    w.write_all(&(ops.len() as u64).to_le_bytes())?;
    for op in ops {
        w.write_all(&serialize_op(op))?;
    }
    w.write_all(&(rng_words.len() as u64).to_le_bytes())?;
    for &rw in &rng_words {
        w.write_all(&rw.to_le_bytes())?;
    }
    w.write_all(&ana_q.to_le_bytes())?;
    w.write_all(&ana_b.to_le_bytes())?;
    w.write_all(&ana_r.to_le_bytes())?;
    w.write_all(&final_phase.to_le_bytes())?;
    w.write_all(&final_toffoli.to_le_bytes())?;
    w.write_all(&final_clifford.to_le_bytes())?;
    w.write_all(&(final_qubits.len() as u64).to_le_bytes())?;
    w.write_all(&(final_bits.len() as u64).to_le_bytes())?;
    w.write_all(&(reg_items.len() as u64).to_le_bytes())?;
    for &v in &final_qubits {
        w.write_all(&v.to_le_bytes())?;
    }
    for &v in &final_bits {
        w.write_all(&v.to_le_bytes())?;
    }
    for &(ri, is_b, id) in &reg_items {
        w.write_all(&ri.to_le_bytes())?;
        w.write_all(&is_b.to_le_bytes())?;
        w.write_all(&id.to_le_bytes())?;
    }
    Ok(())
}

fn mk_op(
    kind: OperationType,
    qc2: u64,
    qc1: u64,
    qt: u64,
    ct: u64,
    cc: u64,
    rt: u64,
) -> Op {
    Op {
        kind,
        q_control2: QubitId(qc2),
        q_control1: QubitId(qc1),
        q_target: QubitId(qt),
        c_target: BitId(ct),
        c_condition: BitId(cc),
        r_target: RegisterId(rt),
    }
}

fn generate_diff_suite(out_path: &str) -> std::io::Result<()> {
    let u = u64::MAX;
    let mut out = BufWriter::new(File::create(out_path)?);
    let num_cases: u64 = 20;
    out.write_all(b"QECCDIFF")?;
    out.write_all(&num_cases.to_le_bytes())?;

    // Case 0: All 18 OperationType variants
    let ops0 = vec![
        mk_op(OperationType::Register, u, u, u, u, u, 0),
        mk_op(OperationType::Register, u, u, u, u, u, 1),
        mk_op(OperationType::AppendToRegister, u, u, 0, u, u, 0),
        mk_op(OperationType::AppendToRegister, u, u, 1, u, u, 0),
        mk_op(OperationType::AppendToRegister, u, u, u, 0, u, 1),
        mk_op(OperationType::AppendToRegister, u, u, u, 1, u, 1),
        mk_op(OperationType::BitStore1, u, u, u, 0, u, u),
        mk_op(OperationType::BitInvert, u, u, u, 1, 0, u),
        mk_op(OperationType::BitStore0, u, u, u, 2, u, u),
        mk_op(OperationType::X, u, u, 0, u, u, u),
        mk_op(OperationType::Z, u, u, 0, u, 0, u),
        mk_op(OperationType::Neg, u, u, u, u, 1, u),
        mk_op(OperationType::CX, u, 0, 1, u, u, u),
        mk_op(OperationType::CZ, u, 0, 1, u, 0, u),
        mk_op(OperationType::Swap, u, 1, 2, u, 0, u),
        mk_op(OperationType::CCX, 0, 2, 3, u, u, u),
        mk_op(OperationType::CCZ, 0, 2, 3, u, 1, u),
        mk_op(OperationType::PushCondition, u, u, u, u, 0, u),
        mk_op(OperationType::R, u, u, 2, u, 1, u),
        mk_op(OperationType::Hmr, u, u, 3, 2, u, u),
        mk_op(OperationType::PopCondition, u, u, u, u, u, u),
        mk_op(OperationType::DebugPrint, u, u, 0, 0, u, 0),
    ];
    write_diff_case(
        &mut out,
        "all_18_op_kinds_canonical",
        0x0123_4567_89AB_CDEF,
        &[0x5555_5555_5555_5555, 0x3333_3333_3333_3333, 0x0F0F_0F0F_0F0F_0F0F, 0],
        &[0xFFFF_0000_FFFF_0000, 0x00FF_00FF_00FF_00FF, 0],
        &ops0,
        b"case0",
    )?;

    // Case 1: Deep nested PushCondition / PopCondition + empty stack PopCondition
    let ops1 = vec![
        mk_op(OperationType::PopCondition, u, u, u, u, u, u), // empty stack pop = no-op
        mk_op(OperationType::PushCondition, u, u, u, u, 0, u),
        mk_op(OperationType::X, u, u, 0, u, u, u),
        mk_op(OperationType::PushCondition, u, u, u, u, 1, u),
        mk_op(OperationType::CX, u, 0, 1, u, u, u),
        mk_op(OperationType::PushCondition, u, u, u, u, 2, u),
        mk_op(OperationType::CCX, 0, 1, 2, u, 3, u),
        mk_op(OperationType::Hmr, u, u, 2, 4, u, u),
        mk_op(OperationType::PopCondition, u, u, u, u, u, u),
        mk_op(OperationType::Z, u, u, 1, u, u, u),
        mk_op(OperationType::PopCondition, u, u, u, u, u, u),
        mk_op(OperationType::R, u, u, 0, u, u, u),
        mk_op(OperationType::PopCondition, u, u, u, u, u, u),
        mk_op(OperationType::PopCondition, u, u, u, u, u, u), // extra pop
        mk_op(OperationType::CCZ, 0, 1, 2, u, u, u),
    ];
    write_diff_case(
        &mut out,
        "deep_condition_stack_and_empty_pop",
        0,
        &[u64::MAX, 0xAAAA_AAAA_AAAA_AAAA, 0x1234_5678_9ABC_DEF0],
        &[
            0xFFFF_FFFF_0000_0000,
            0xFFFF_0000_FFFF_0000,
            0xFF00_FF00_FF00_FF00,
            0xF0F0_F0F0_F0F0_F0F0,
            0,
        ],
        &ops1,
        b"case1",
    )?;

    // Case 2: R and Hmr phase kickback and reset under partial masks
    let ops2 = vec![
        mk_op(OperationType::R, u, u, 0, u, 0, u),
        mk_op(OperationType::Hmr, u, u, 1, 2, 1, u),
        mk_op(OperationType::R, u, u, 2, u, u, u),
        mk_op(OperationType::Hmr, u, u, 3, 3, u, u),
        mk_op(OperationType::Hmr, u, u, 0, 0, 2, u),
    ];
    write_diff_case(
        &mut out,
        "resets_and_hmr_phase_randomization",
        0xDEAD_BEEF_CAFE_BABE,
        &[
            0xFFFF_FFFF_FFFF_FFFF,
            0x8000_0000_0000_0001,
            0x5555_AAAA_5555_AAAA,
            0x0102_0304_0506_0708,
        ],
        &[
            0x0F0F_0F0F_0F0F_0F0F,
            0x3333_3333_3333_3333,
            0xAAAA_5555_AAAA_5555,
            0xFFFF_0000_0000_FFFF,
        ],
        &ops2,
        b"case2",
    )?;

    // Case 3: Swap under partial condition masks
    let ops3 = vec![
        mk_op(OperationType::Swap, u, 0, 1, u, 0, u),
        mk_op(OperationType::Swap, u, 1, 2, u, 1, u),
        mk_op(OperationType::Swap, u, 2, 3, u, u, u),
        mk_op(OperationType::Swap, u, 3, 0, u, 2, u),
    ];
    write_diff_case(
        &mut out,
        "conditional_swap_masks",
        0,
        &[
            0x1111_2222_3333_4444,
            0x5555_6666_7777_8888,
            0x9999_AAAA_BBBB_CCCC,
            0xDDDD_EEEE_FFFF_0000,
        ],
        &[0, u64::MAX, 0x5555_5555_5555_5555],
        &ops3,
        b"case3",
    )?;

    // Case 4: Popcount64 gate counting across all bit patterns
    let mut ops4 = Vec::new();
    for b in 0..8u64 {
        ops4.push(mk_op(OperationType::CCX, 0, 1, 2, u, b, u));
        ops4.push(mk_op(OperationType::CCZ, 1, 2, 3, u, b, u));
        ops4.push(mk_op(OperationType::CX, u, 2, 0, u, b, u));
        ops4.push(mk_op(OperationType::CZ, u, 0, 3, u, b, u));
    }
    write_diff_case(
        &mut out,
        "popcount64_toffoli_clifford_accounting",
        0,
        &[u64::MAX, 0xAAAA_AAAA_AAAA_AAAA, 0x5555_5555_5555_5555, 0xF0F0_F0F0_0F0F_0F0F],
        &[
            0,
            1,
            0x8000_0000_0000_0000,
            0x8000_0000_0000_0001,
            0x5555_5555_5555_5555,
            0x3333_3333_3333_3333,
            0x0F0F_0F0F_0F0F_0F0F,
            u64::MAX,
        ],
        &ops4,
        b"case4",
    )?;

    // Cases 5..19: 15 deterministic pseudo-random stress circuits (200..500 ops each)
    for idx in 5..20u64 {
        let mut seed_hasher = Shake256::default();
        seed_hasher.update(b"stress-circuit-gen");
        seed_hasher.update(&idx.to_le_bytes());
        let mut rng = seed_hasher.finalize_xof();
        let mut next_u64 = || -> u64 {
            let mut b = [0u8; 8];
            XofReader::read(&mut rng, &mut b);
            u64::from_le_bytes(b)
        };

        let n_qubits = 16u64 + (idx % 16);
        let n_bits = 12u64 + (idx % 12);
        let mut init_q = Vec::with_capacity(n_qubits as usize);
        for _ in 0..n_qubits {
            init_q.push(next_u64());
        }
        let mut init_b = Vec::with_capacity(n_bits as usize);
        for _ in 0..n_bits {
            init_b.push(next_u64());
        }
        let init_phase = next_u64();

        let mut ops = Vec::new();
        // Declare 2 registers and append some qubits/bits
        ops.push(mk_op(OperationType::Register, u, u, u, u, u, 0));
        ops.push(mk_op(OperationType::Register, u, u, u, u, u, 1));
        for q in 0..4 {
            ops.push(mk_op(OperationType::AppendToRegister, u, u, q, u, u, 0));
        }
        for b in 0..4 {
            ops.push(mk_op(OperationType::AppendToRegister, u, u, u, b, u, 1));
        }

        let n_random_ops = 200 + (idx as usize) * 20;
        for _ in 0..n_random_ops {
            let choice = next_u64() % 15;
            let q0 = next_u64() % n_qubits;
            let q1 = (q0 + 1 + (next_u64() % (n_qubits - 1))) % n_qubits;
            let mut q2 = (q1 + 1 + (next_u64() % (n_qubits - 2))) % n_qubits;
            if q2 == q0 || q2 == q1 {
                q2 = (0..n_qubits).find(|&x| x != q0 && x != q1).unwrap();
            }
            let c_t = next_u64() % n_bits;
            let c_cond = if next_u64() % 2 == 0 {
                next_u64() % n_bits
            } else {
                u
            };
            let op = match choice {
                0 => mk_op(OperationType::Neg, u, u, u, u, c_cond, u),
                1 => mk_op(OperationType::BitInvert, u, u, u, c_t, c_cond, u),
                2 => mk_op(OperationType::BitStore0, u, u, u, c_t, c_cond, u),
                3 => mk_op(OperationType::BitStore1, u, u, u, c_t, c_cond, u),
                4 => mk_op(OperationType::X, u, u, q0, u, c_cond, u),
                5 => mk_op(OperationType::Z, u, u, q0, u, c_cond, u),
                6 => mk_op(OperationType::CX, u, q1, q0, u, c_cond, u),
                7 => mk_op(OperationType::CZ, u, q1, q0, u, c_cond, u),
                8 => mk_op(OperationType::Swap, u, q1, q0, u, c_cond, u),
                9 => mk_op(OperationType::R, u, u, q0, u, c_cond, u),
                10 => mk_op(OperationType::Hmr, u, u, q0, c_t, c_cond, u),
                11 => mk_op(OperationType::CCX, q2, q1, q0, u, c_cond, u),
                12 => mk_op(OperationType::CCZ, q2, q1, q0, u, c_cond, u),
                13 => mk_op(OperationType::PushCondition, u, u, u, u, next_u64() % n_bits, u),
                _ => mk_op(OperationType::PopCondition, u, u, u, u, u, u),
            };
            ops.push(op);
        }

        let name = format!("random_stress_circuit_{idx}");
        let tag = format!("stress_{idx}");
        write_diff_case(
            &mut out,
            &name,
            init_phase,
            &init_q,
            &init_b,
            &ops,
            tag.as_bytes(),
        )?;
    }

    out.flush()?;
    println!("Generated {num_cases} differential test cases in {out_path}");
    Ok(())
}

fn export_batch(ops_path: &str, out_batch_path: &str, target_shots: usize) -> Result<(), String> {
    let ops = load_ops(ops_path)?;
    let (total_qubits, num_bits, _num_regs, regs) = analyze_ops(ops.iter());
    if regs.len() != 4 || regs.iter().any(|r| r.len() != 256) {
        return Err("invalid register layout in ops.bin".to_string());
    }

    let mut xof = fiat_shamir_seed(&ops);
    let curve = secp256k1();

    let mut targets = Vec::with_capacity(target_shots);
    let mut offsets = Vec::with_capacity(target_shots);
    let mut expected = Vec::with_capacity(target_shots);
    for _ in 0..target_shots {
        let mut rb = [[0u8; 32]; 2];
        XofReader::read(&mut xof, &mut rb[0]);
        XofReader::read(&mut xof, &mut rb[1]);
        let k1 = U256::from_le_bytes(rb[0]);
        let k2 = U256::from_le_bytes(rb[1]);
        let t = curve.mul(curve.gx, curve.gy, k1);
        let o = curve.mul(curve.gx, curve.gy, k2);
        if t.0 == o.0 {
            continue;
        }
        if t.0.is_zero() && t.1.is_zero() {
            continue;
        }
        if o.0.is_zero() && o.1.is_zero() {
            continue;
        }
        let e = curve.add(t.0, t.1, o.0, o.1);
        targets.push(t);
        offsets.push(o);
        expected.push(e);
    }

    let bs = targets.len().min(64);
    let rng_words_needed = ops
        .iter()
        .filter(|op| matches!(op.kind, OperationType::R | OperationType::Hmr))
        .count();

    let mut xof_for_export = xof.clone();
    let mut rng_words = Vec::with_capacity(rng_words_needed);
    for _ in 0..rng_words_needed {
        let mut buf = [0u8; 8];
        XofReader::read(&mut xof_for_export, &mut buf);
        rng_words.push(u64::from_le_bytes(buf));
    }

    // Also run the 64-shot batch in Rust Simulator to record reference stats
    let mut sim = Simulator::new(total_qubits as usize, num_bits as usize, &mut xof);
    sim.clear_for_shot();
    for shot in 0..bs {
        sim.set_register(&regs[0], targets[shot].0, shot);
        sim.set_register(&regs[1], targets[shot].1, shot);
        sim.set_register(&regs[2], offsets[shot].0, shot);
        sim.set_register(&regs[3], offsets[shot].1, shot);
    }
    sim.apply_iter(ops.iter());

    let mut out =
        BufWriter::new(File::create(out_batch_path).map_err(|e| format!("create batch: {e}"))?);
    out.write_all(b"QECCBAT1").map_err(|e| e.to_string())?;
    let mode_tag: u64 = if target_shots == 9024 { 1 } else { 0 };
    out.write_all(&mode_tag.to_le_bytes())
        .map_err(|e| e.to_string())?;
    out.write_all(&(bs as u64).to_le_bytes())
        .map_err(|e| e.to_string())?;

    for shot in 0..bs {
        out.write_all(&targets[shot].0.to_le_bytes::<32>())
            .map_err(|e| e.to_string())?;
        out.write_all(&targets[shot].1.to_le_bytes::<32>())
            .map_err(|e| e.to_string())?;
        out.write_all(&offsets[shot].0.to_le_bytes::<32>())
            .map_err(|e| e.to_string())?;
        out.write_all(&offsets[shot].1.to_le_bytes::<32>())
            .map_err(|e| e.to_string())?;
        out.write_all(&expected[shot].0.to_le_bytes::<32>())
            .map_err(|e| e.to_string())?;
        out.write_all(&expected[shot].1.to_le_bytes::<32>())
            .map_err(|e| e.to_string())?;
    }

    out.write_all(&(rng_words.len() as u64).to_le_bytes())
        .map_err(|e| e.to_string())?;
    for &w in &rng_words {
        out.write_all(&w.to_le_bytes()).map_err(|e| e.to_string())?;
    }
    out.write_all(&sim.stats.toffoli_gates.to_le_bytes())
        .map_err(|e| e.to_string())?;
    out.write_all(&sim.stats.clifford_gates.to_le_bytes())
        .map_err(|e| e.to_string())?;
    out.write_all(&sim.phase.to_le_bytes())
        .map_err(|e| e.to_string())?;
    out.flush().map_err(|e| e.to_string())?;

    println!(
        "Exported {bs}-shot batch + {} XOF words for {} ops to {out_batch_path}",
        rng_words.len(),
        ops.len()
    );
    Ok(())
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() >= 3 && args[1] == "gen-diff-suite" {
        if let Err(e) = generate_diff_suite(&args[2]) {
            eprintln!("gen-diff-suite failed: {e}");
            std::process::exit(1);
        }
    } else if args.len() >= 4 && args[1] == "export-batch" {
        let shots = if args.len() >= 5 {
            args[4].parse::<usize>().unwrap_or(64)
        } else {
            64
        };
        if let Err(e) = export_batch(&args[2], &args[3], shots) {
            eprintln!("export-batch failed: {e}");
            std::process::exit(1);
        }
    } else {
        eprintln!("Usage:");
        eprintln!("  rust_diff_driver gen-diff-suite <out_suite.bin>");
        eprintln!("  rust_diff_driver export-batch <ops.bin> <out_batch.bin> [shots]");
        std::process::exit(1);
    }
}
