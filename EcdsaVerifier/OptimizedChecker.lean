import EcdsaVerifier.CanonicalSpec

namespace EcdsaVerifier

/-- Fixed byte width of a serialized `Op` record (`OP_BYTES = 56` in `eval_circuit.rs`). -/
def OP_BYTES : Nat := 56

/-- Maximum allowed operation count (`MAX_OPS = 4_000_000_000` in `eval_circuit.rs`). -/
def MAX_OPS : UInt64 := 4000000000

/-- Optimized single-step checker matching `stepCanonical`. -/
@[inline]
def stepOptimized (st : SimState) (op : Op) (rngVal : UInt64) : SimState :=
  stepCanonical st op rngVal

/-- Optimized step with RNG cursor matching `stepWithRngCursor`. -/
@[inline]
def stepOptimizedWithRng (st : SimState) (op : Op) (rngWords : Array UInt64) (rngIdx : Nat) : SimState × Nat :=
  stepWithRngCursor st op rngWords rngIdx

/-- Tail-recursive list runner for `stepOptimizedWithRng`. -/
def runOptimizedList (st : SimState) (ops : List Op) (rngWords : Array UInt64) (rngIdx : Nat) : SimState × Nat :=
  match ops with
  | [] => (st, rngIdx)
  | op :: rest =>
    let (st', rngIdx') := stepOptimizedWithRng st op rngWords rngIdx
    runOptimizedList st' rest rngWords rngIdx'

/-- Optimized execution of an operation array. -/
def runOptimized (st : SimState) (ops : Array Op) (rngWords : Array UInt64) (rngIdx : Nat := 0) : SimState × Nat :=
  let stInit := { st with condStack := [], currentBaseCond := 0xFFFFFFFFFFFFFFFF }
  runOptimizedList stInit ops.toList rngWords rngIdx

/-- Optimized post-simulation batch check. -/
def checkBatchOptimized
    (stAfter : SimState)
    (regs : Array (Array QubitOrBit))
    (expectedX : Array U256Val)
    (expectedY : Array U256Val)
    (totalQubits : UInt64)
    (batchShots : Nat) : BatchCheckResult :=
  checkBatchCanonical stAfter regs expectedX expectedY totalQubits batchShots

/-- Combined gate decision returning `(PreGateAccept cand base, PromotionGateAccept cand base)`. -/
def evalGateDecision (cand base : Cert) : Bool × Bool :=
  (PreGateAccept cand base, PromotionGateAccept cand base)

/-- Read a 32-bit little-endian unsigned integer from `bs` at byte offset `off`. -/
@[inline]
def readU32LE (bs : ByteArray) (off : Nat) : UInt32 :=
  let b0 := (bs.get! off).toUInt32
  let b1 := (bs.get! (off + 1)).toUInt32 <<< (8 : UInt32)
  let b2 := (bs.get! (off + 2)).toUInt32 <<< (16 : UInt32)
  let b3 := (bs.get! (off + 3)).toUInt32 <<< (24 : UInt32)
  b0 ||| b1 ||| b2 ||| b3

/-- Read a 64-bit little-endian unsigned integer from `bs` at byte offset `off`. -/
@[inline]
def readU64LE (bs : ByteArray) (off : Nat) : UInt64 :=
  let b0 := (bs.get! off).toUInt64
  let b1 := (bs.get! (off + 1)).toUInt64 <<< (8 : UInt64)
  let b2 := (bs.get! (off + 2)).toUInt64 <<< (16 : UInt64)
  let b3 := (bs.get! (off + 3)).toUInt64 <<< (24 : UInt64)
  let b4 := (bs.get! (off + 4)).toUInt64 <<< (32 : UInt64)
  let b5 := (bs.get! (off + 5)).toUInt64 <<< (40 : UInt64)
  let b6 := (bs.get! (off + 6)).toUInt64 <<< (48 : UInt64)
  let b7 := (bs.get! (off + 7)).toUInt64 <<< (56 : UInt64)
  b0 ||| b1 ||| b2 ||| b3 ||| b4 ||| b5 ||| b6 ||| b7

/-- Read a 256-bit little-endian unsigned integer (4 `UInt64` limbs) from `bs` at byte offset `off`. -/
@[inline]
def readU256LE (bs : ByteArray) (off : Nat) : U256Val :=
  { limb0 := readU64LE bs off
    limb1 := readU64LE bs (off + 8)
    limb2 := readU64LE bs (off + 16)
    limb3 := readU64LE bs (off + 24) }

/-- Verify the 16-byte `QECCOPSZ` header and return the declared operation count `n`. -/
def parseOpsHeader (hdr : ByteArray) : Except String Nat :=
  if hdr.size < 16 then
    .error "header shorter than 16 bytes"
  else
    let m0 := hdr.get! 0 == 0x51 -- 'Q'
    let m1 := hdr.get! 1 == 0x45 -- 'E'
    let m2 := hdr.get! 2 == 0x43 -- 'C'
    let m3 := hdr.get! 3 == 0x43 -- 'C'
    let m4 := hdr.get! 4 == 0x4F -- 'O'
    let m5 := hdr.get! 5 == 0x50 -- 'P'
    let m6 := hdr.get! 6 == 0x53 -- 'S'
    let m7 := hdr.get! 7 == 0x5A -- 'Z'
    if !(m0 && m1 && m2 && m3 && m4 && m5 && m6 && m7) then
      .error "bad magic (expected QECCOPSZ)"
    else
      let n := readU64LE hdr 8
      if n > MAX_OPS then
        .error s!"op count {n} exceeds cap {MAX_OPS}"
      else
        .ok n.toNat

/-- Decode and validate a single 56-byte operation record at offset `off` in `bs`. -/
@[inline]
def decodeAndValidateOpAt (bs : ByteArray) (off : Nat) (idx : Nat) : Except String Op :=
  let kindRaw := readU32LE bs off
  match opKindFromU32 kindRaw with
  | none => .error s!"op {idx}: unknown kind {kindRaw}"
  | some kind =>
    let op : Op :=
      { kind       := kind
        qControl2  := readU64LE bs (off + 8)
        qControl1  := readU64LE bs (off + 16)
        qTarget    := readU64LE bs (off + 24)
        cTarget    := readU64LE bs (off + 32)
        cCondition := readU64LE bs (off + 40)
        rTarget    := readU64LE bs (off + 48) }
    if validateOp op then
      .ok op
    else
      .error s!"op {idx}: failed Op::validate()"

/-- Decode a 56-byte operation record at offset `off` assuming `kindRaw` was already validated. -/
@[inline]
def decodeValidatedOpAt (bs : ByteArray) (off : Nat) : Op :=
  let kindRaw := readU32LE bs off
  let kind := (opKindFromU32 kindRaw).getD .neg
  { kind       := kind
    qControl2  := readU64LE bs (off + 8)
    qControl1  := readU64LE bs (off + 16)
    qTarget    := readU64LE bs (off + 24)
    cTarget    := readU64LE bs (off + 32)
    cCondition := readU64LE bs (off + 40)
    rTarget    := readU64LE bs (off + 48) }

/-- Parse and validate an unpacked `ByteArray` of `numOps` 56-byte records into `Array Op`. -/
def parseOpsByteArray (bs : ByteArray) (numOps : Nat) : Except String (Array Op) := do
  if bs.size != numOps * OP_BYTES then
    throw s!"unpacked byte size {bs.size} != expected {numOps * OP_BYTES}"
  let mut ops := Array.mkEmpty numOps
  for i in [0:numOps] do
    let op ← decodeAndValidateOpAt bs (i * OP_BYTES) i
    ops := ops.push op
  return ops

/-- Parse an array of little-endian `UInt64` RNG words from a `ByteArray`. -/
def parseRngWordsByteArray (bs : ByteArray) : Array UInt64 :=
  let n := bs.size / 8
  Id.run do
    let mut out := Array.mkEmpty n
    for i in [0:n] do
      out := out.push (readU64LE bs (i * 8))
    return out

private def analyzeByteArrayLoop
    (bs : ByteArray) (numOps : Nat) (i : Nat) (acc : CircuitAnalysis)
    : Except String CircuitAnalysis :=
  if _ : i < numOps then
    match decodeAndValidateOpAt bs (i * OP_BYTES) i with
    | .error e => .error e
    | .ok op   => analyzeByteArrayLoop bs numOps (i + 1) (analyzeOpStep acc op)
  else
    .ok acc
termination_by numOps - i

/-- Stream-validate all `numOps` 56-byte records in `bs` and compute `CircuitAnalysis`. -/
def analyzeAndValidateByteArray (bs : ByteArray) (numOps : Nat) : Except String CircuitAnalysis :=
  if bs.size != numOps * OP_BYTES then
    .error s!"unpacked byte size {bs.size} != expected {numOps * OP_BYTES}"
  else
    analyzeByteArrayLoop bs numOps 0 { numQubits := 0, numBits := 0, numRegisters := 0, registers := #[] }

private def runByteArrayLoop
    (bs : ByteArray) (numOps : Nat) (i : Nat)
    (st : SimState) (rngWords : Array UInt64) (rngIdx : Nat)
    : SimState × Nat :=
  if _ : i < numOps then
    let op := decodeValidatedOpAt bs (i * OP_BYTES)
    let (st', rngIdx') := stepOptimizedWithRng st op rngWords rngIdx
    runByteArrayLoop bs numOps (i + 1) st' rngWords rngIdx'
  else
    (st, rngIdx)
termination_by numOps - i

/-- Execute `numOps` validated 56-byte records directly from `bs` without allocating `Array Op`. -/
def runByteArrayOptimized
    (st : SimState) (bs : ByteArray) (numOps : Nat)
    (rngWords : Array UInt64) (rngIdx : Nat := 0)
    : SimState × Nat :=
  let stInit := { st with condStack := [], currentBaseCond := 0xFFFFFFFFFFFFFFFF }
  runByteArrayLoop bs numOps 0 stInit rngWords rngIdx

end EcdsaVerifier
