namespace EcdsaVerifier

/-- Sentinel value for unused qubit operand (`u64::MAX` in `src/circuit.rs`). -/
def NO_QUBIT : UInt64 := 0xFFFFFFFFFFFFFFFF

/-- Sentinel value for unused classical bit operand (`u64::MAX` in `src/circuit.rs`). -/
def NO_BIT : UInt64 := 0xFFFFFFFFFFFFFFFF

/-- Sentinel value for unused register operand (`u64::MAX` in `src/circuit.rs`). -/
def NO_REG : UInt64 := 0xFFFFFFFFFFFFFFFF

/-- Exact 18 operation types matching `OperationType` (`0..=17`) in `src/circuit.rs`. -/
inductive OpKind where
  | neg              -- 0
  | register         -- 1
  | appendToRegister -- 2
  | bitInvert        -- 3
  | bitStore0        -- 4
  | bitStore1        -- 5
  | x                -- 6
  | z                -- 7
  | cx               -- 8
  | cz               -- 9
  | swap             -- 10
  | r                -- 11
  | hmr              -- 12
  | ccx              -- 13
  | ccz              -- 14
  | pushCondition    -- 15
  | popCondition     -- 16
  | debugPrint       -- 17
  deriving Repr, DecidableEq, Inhabited

/-- Convert `OpKind` to its wire `UInt32` tag (`0..17`). -/
def OpKind.toU32 (k : OpKind) : UInt32 :=
  match k with
  | .neg              => 0
  | .register         => 1
  | .appendToRegister => 2
  | .bitInvert        => 3
  | .bitStore0        => 4
  | .bitStore1        => 5
  | .x                => 6
  | .z                => 7
  | .cx               => 8
  | .cz               => 9
  | .swap             => 10
  | .r                => 11
  | .hmr              => 12
  | .ccx              => 13
  | .ccz              => 14
  | .pushCondition    => 15
  | .popCondition     => 16
  | .debugPrint       => 17

/-- Decode `OpKind` from its wire `UInt32` tag (`op_kind_from_u32` in `eval_circuit.rs`). -/
def opKindFromU32 (v : UInt32) : Option OpKind :=
  if v == 0 then some .neg
  else if v == 1 then some .register
  else if v == 2 then some .appendToRegister
  else if v == 3 then some .bitInvert
  else if v == 4 then some .bitStore0
  else if v == 5 then some .bitStore1
  else if v == 6 then some .x
  else if v == 7 then some .z
  else if v == 8 then some .cx
  else if v == 9 then some .cz
  else if v == 10 then some .swap
  else if v == 11 then some .r
  else if v == 12 then some .hmr
  else if v == 13 then some .ccx
  else if v == 14 then some .ccz
  else if v == 15 then some .pushCondition
  else if v == 16 then some .popCondition
  else if v == 17 then some .debugPrint
  else none

/-- Decoded circuit operation matching `Op` in `src/circuit.rs`. -/
structure Op where
  kind       : OpKind
  qControl2  : UInt64
  qControl1  : UInt64
  qTarget    : UInt64
  cTarget    : UInt64
  cCondition : UInt64
  rTarget    : UInt64
  deriving Repr, DecidableEq, Inhabited

/-- Empty operation matching `Op::empty()` in `src/circuit.rs`. -/
def Op.empty : Op :=
  { kind       := .neg
    qControl2  := NO_QUBIT
    qControl1  := NO_QUBIT
    qTarget    := NO_QUBIT
    cTarget    := NO_BIT
    cCondition := NO_BIT
    rTarget    := NO_REG }

/-- Per-operand requirement flag matching `BANNED`/`ALLOWED`/`REQUIRED` in `Op::validate`. -/
inductive OperandFlag where
  | banned
  | allowed
  | required
  deriving Repr, DecidableEq, Inhabited

/-- Check whether an operand value satisfies its `OperandFlag` wrt `sentinel`. -/
def checkOperandFlag (flag : OperandFlag) (val : UInt64) (sentinel : UInt64) : Bool :=
  match flag with
  | .banned   => val == sentinel
  | .allowed  => true
  | .required => val != sentinel

/-- Check qubit aliasing rules from `Op::validate()` in `src/circuit.rs`. -/
def hasNoQubitAliasing (op : Op) : Bool :=
  !(op.qTarget == op.qControl1 && op.qTarget != NO_QUBIT) &&
  !(op.qTarget == op.qControl2 && op.qTarget != NO_QUBIT) &&
  !(op.qControl1 == op.qControl2 && op.qControl1 != NO_QUBIT)

/-- Exact model of `Op::validate()` in `src/circuit.rs`. -/
def validateOp (op : Op) : Bool :=
  if !hasNoQubitAliasing op then
    false
  else
    match op.kind with
    | .debugPrint => true
    | .register =>
      checkOperandFlag .banned   op.cCondition NO_BIT &&
      checkOperandFlag .banned   op.qTarget    NO_QUBIT &&
      checkOperandFlag .banned   op.qControl1  NO_QUBIT &&
      checkOperandFlag .banned   op.qControl2  NO_QUBIT &&
      checkOperandFlag .banned   op.cTarget    NO_BIT &&
      checkOperandFlag .required op.rTarget    NO_REG
    | .appendToRegister =>
      if (op.qTarget == NO_QUBIT) == (op.cTarget == NO_BIT) then
        false
      else
        checkOperandFlag .banned   op.cCondition NO_BIT &&
        checkOperandFlag .allowed  op.qTarget    NO_QUBIT &&
        checkOperandFlag .banned   op.qControl1  NO_QUBIT &&
        checkOperandFlag .banned   op.qControl2  NO_QUBIT &&
        checkOperandFlag .allowed  op.cTarget    NO_BIT &&
        checkOperandFlag .required op.rTarget    NO_REG
    | .ccx | .ccz =>
      checkOperandFlag .allowed  op.cCondition NO_BIT &&
      checkOperandFlag .required op.qTarget    NO_QUBIT &&
      checkOperandFlag .required op.qControl1  NO_QUBIT &&
      checkOperandFlag .required op.qControl2  NO_QUBIT &&
      checkOperandFlag .banned   op.cTarget    NO_BIT &&
      checkOperandFlag .banned   op.rTarget    NO_REG
    | .cx | .cz | .swap =>
      checkOperandFlag .allowed  op.cCondition NO_BIT &&
      checkOperandFlag .required op.qTarget    NO_QUBIT &&
      checkOperandFlag .required op.qControl1  NO_QUBIT &&
      checkOperandFlag .banned   op.qControl2  NO_QUBIT &&
      checkOperandFlag .banned   op.cTarget    NO_BIT &&
      checkOperandFlag .banned   op.rTarget    NO_REG
    | .x | .z | .r =>
      checkOperandFlag .allowed  op.cCondition NO_BIT &&
      checkOperandFlag .required op.qTarget    NO_QUBIT &&
      checkOperandFlag .banned   op.qControl1  NO_QUBIT &&
      checkOperandFlag .banned   op.qControl2  NO_QUBIT &&
      checkOperandFlag .banned   op.cTarget    NO_BIT &&
      checkOperandFlag .banned   op.rTarget    NO_REG
    | .neg =>
      checkOperandFlag .allowed  op.cCondition NO_BIT &&
      checkOperandFlag .banned   op.qTarget    NO_QUBIT &&
      checkOperandFlag .banned   op.qControl1  NO_QUBIT &&
      checkOperandFlag .banned   op.qControl2  NO_QUBIT &&
      checkOperandFlag .banned   op.cTarget    NO_BIT &&
      checkOperandFlag .banned   op.rTarget    NO_REG
    | .hmr =>
      checkOperandFlag .allowed  op.cCondition NO_BIT &&
      checkOperandFlag .required op.qTarget    NO_QUBIT &&
      checkOperandFlag .banned   op.qControl1  NO_QUBIT &&
      checkOperandFlag .banned   op.qControl2  NO_QUBIT &&
      checkOperandFlag .required op.cTarget    NO_BIT &&
      checkOperandFlag .banned   op.rTarget    NO_REG
    | .bitInvert | .bitStore0 | .bitStore1 =>
      checkOperandFlag .allowed  op.cCondition NO_BIT &&
      checkOperandFlag .banned   op.qTarget    NO_QUBIT &&
      checkOperandFlag .banned   op.qControl1  NO_QUBIT &&
      checkOperandFlag .banned   op.qControl2  NO_QUBIT &&
      checkOperandFlag .required op.cTarget    NO_BIT &&
      checkOperandFlag .banned   op.rTarget    NO_REG
    | .pushCondition =>
      checkOperandFlag .required op.cCondition NO_BIT &&
      checkOperandFlag .banned   op.qTarget    NO_QUBIT &&
      checkOperandFlag .banned   op.qControl1  NO_QUBIT &&
      checkOperandFlag .banned   op.qControl2  NO_QUBIT &&
      checkOperandFlag .banned   op.cTarget    NO_BIT &&
      checkOperandFlag .banned   op.rTarget    NO_REG
    | .popCondition =>
      checkOperandFlag .banned   op.cCondition NO_BIT &&
      checkOperandFlag .banned   op.qTarget    NO_QUBIT &&
      checkOperandFlag .banned   op.qControl1  NO_QUBIT &&
      checkOperandFlag .banned   op.qControl2  NO_QUBIT &&
      checkOperandFlag .banned   op.cTarget    NO_BIT &&
      checkOperandFlag .banned   op.rTarget    NO_REG

/-- Validate an entire array of operations. -/
def validateOps (ops : Array Op) : Bool :=
  ops.all validateOp

/-- Register element matching `QubitOrBit` in `src/circuit.rs`. -/
inductive QubitOrBit where
  | qubit (id : UInt64)
  | bit   (id : UInt64)
  deriving Repr, DecidableEq, Inhabited

/-- Circuit resource and register layout analysis matching `analyze_ops` in `src/circuit.rs`. -/
structure CircuitAnalysis where
  numQubits    : UInt64
  numBits      : UInt64
  numRegisters : UInt64
  registers    : Array (Array QubitOrBit)
  deriving Repr, DecidableEq, Inhabited

private def maxU64 (a b : UInt64) : UInt64 :=
  if a >= b then a else b

private def ensureRegSize (regs : Array (Array QubitOrBit)) (targetLen : Nat) : Array (Array QubitOrBit) :=
  if regs.size >= targetLen then
    regs
  else
    let missing := targetLen - regs.size
    Id.run do
      let mut r := regs
      for _ in [0:missing] do
        r := r.push #[]
      return r

/-- Step of `analyze_ops` on a single `Op`. -/
def analyzeOpStep (acc : CircuitAnalysis) (op : Op) : CircuitAnalysis :=
  let nq0 := acc.numQubits
  let nq1 := if op.qControl2 != NO_QUBIT then maxU64 nq0 (op.qControl2 + 1) else nq0
  let nq2 := if op.qControl1 != NO_QUBIT then maxU64 nq1 (op.qControl1 + 1) else nq1
  let nq3 := if op.qTarget   != NO_QUBIT then maxU64 nq2 (op.qTarget + 1)   else nq2

  let nb0 := acc.numBits
  let nb1 := if op.cTarget    != NO_BIT then maxU64 nb0 (op.cTarget + 1)    else nb0
  let nb2 := if op.cCondition != NO_BIT then maxU64 nb1 (op.cCondition + 1) else nb1

  let (nr1, regs1) :=
    if op.rTarget != NO_REG then
      let nr := maxU64 acc.numRegisters (op.rTarget + 1)
      let rIdx := op.rTarget.toNat
      (nr, ensureRegSize acc.registers (rIdx + 1))
    else
      (acc.numRegisters, acc.registers)

  let regs2 :=
    if op.kind == .appendToRegister then
      let rIdx := op.rTarget.toNat
      let regsA :=
        if op.qTarget != NO_QUBIT then
          let cur := regs1.getD rIdx #[]
          regs1.setIfInBounds rIdx (cur.push (.qubit op.qTarget))
        else
          regs1
      if op.cTarget != NO_BIT then
        let cur := regsA.getD rIdx #[]
        regsA.setIfInBounds rIdx (cur.push (.bit op.cTarget))
      else
        regsA
    else
      regs1

  { numQubits := nq3, numBits := nb2, numRegisters := nr1, registers := regs2 }

/-- Exact model of `analyze_ops` in `src/circuit.rs`. -/
def analyzeOps (ops : Array Op) : CircuitAnalysis :=
  ops.foldl analyzeOpStep { numQubits := 0, numBits := 0, numRegisters := 0, registers := #[] }

/-- Check that the register layout matches the 4x256 secp256k1 point_add ABI in `eval_circuit.rs`. -/
def validateRegisterLayout (regs : Array (Array QubitOrBit)) : Bool :=
  if regs.size != 4 then
    false
  else
    let r0 := regs.getD 0 #[]
    let r1 := regs.getD 1 #[]
    let r2 := regs.getD 2 #[]
    let r3 := regs.getD 3 #[]
    (r0.size == 256) &&
    (r1.size == 256) &&
    (r2.size == 256) &&
    (r3.size == 256) &&
    r0.all (fun x => match x with | .qubit _ => true | .bit _ => false) &&
    r1.all (fun x => match x with | .qubit _ => true | .bit _ => false) &&
    r2.all (fun x => match x with | .qubit _ => false | .bit _ => true) &&
    r3.all (fun x => match x with | .qubit _ => false | .bit _ => true)

/-- Exact 64-bit population count (`u64::count_ones() as u64` in `src/sim.rs`). -/
def popcount64 (x : UInt64) : UInt64 :=
  let m1 : UInt64 := 0x5555555555555555
  let m2 : UInt64 := 0x3333333333333333
  let m4 : UInt64 := 0x0F0F0F0F0F0F0F0F
  let h01 : UInt64 := 0x0101010101010101
  let x1 := x - ((x >>> (1 : UInt64)) &&& m1)
  let x2 := (x1 &&& m2) + ((x1 >>> (2 : UInt64)) &&& m2)
  let x3 := (x2 + (x2 >>> (4 : UInt64))) &&& m4
  (x3 * h01) >>> (56 : UInt64)

/-- Simulator state tracking 64 shots in parallel (`Simulator` in `src/sim.rs`). -/
structure SimState where
  phase           : UInt64
  qubits          : Array UInt64
  bits            : Array UInt64
  condStack       : List UInt64
  currentBaseCond : UInt64
  cliffordGates   : UInt64
  toffoliGates    : UInt64
  deriving Repr, DecidableEq, Inhabited

/-- Initialize simulator state with `numQubits` and `numBits` (`Simulator::new` in `src/sim.rs`). -/
def SimState.init (numQubits numBits : Nat) : SimState :=
  { phase           := 0
    qubits          := Array.replicate numQubits 0
    bits            := Array.replicate numBits 0
    condStack       := []
    currentBaseCond := 0xFFFFFFFFFFFFFFFF
    cliffordGates   := 0
    toffoliGates    := 0 }

/-- Clear qubits, bits, phase, and reset condition stack for a new 64-shot batch. -/
def SimState.clearForShot (st : SimState) : SimState :=
  { st with
    phase           := 0
    qubits          := Array.replicate st.qubits.size 0
    bits            := Array.replicate st.bits.size 0
    condStack       := []
    currentBaseCond := 0xFFFFFFFFFFFFFFFF }

@[inline]
def SimState.getQubit (st : SimState) (id : UInt64) : UInt64 :=
  st.qubits.getD id.toNat 0

@[inline]
def SimState.setQubit (st : SimState) (id : UInt64) (v : UInt64) : SimState :=
  { st with qubits := st.qubits.setIfInBounds id.toNat v }

@[inline]
def SimState.getBit (st : SimState) (id : UInt64) : UInt64 :=
  st.bits.getD id.toNat 0

@[inline]
def SimState.setBit (st : SimState) (id : UInt64) (v : UInt64) : SimState :=
  { st with bits := st.bits.setIfInBounds id.toNat v }

/-- Effective 64-shot execution mask for `op` in state `st`. -/
@[inline]
def effectiveCond (st : SimState) (op : Op) : UInt64 :=
  if op.cCondition != NO_BIT then
    st.currentBaseCond &&& st.getBit op.cCondition
  else
    st.currentBaseCond

/-- Whether `op.kind` consumes an 8-byte word from the XOF stream (`R` and `Hmr` only). -/
@[inline]
def opConsumesRng (k : OpKind) : Bool :=
  match k with
  | .hmr | .r => true
  | _ => false

/-- Canonical single-operation transition matching `Simulator::apply_iter` in `src/sim.rs`. -/
def stepCanonical (st : SimState) (op : Op) (rngVal : UInt64) : SimState :=
  let cond := effectiveCond st op
  let executedShots := popcount64 cond
  match op.kind with
  | .ccx =>
    let v := cond &&& st.getQubit op.qControl1 &&& st.getQubit op.qControl2
    let qt := st.getQubit op.qTarget ^^^ v
    { st with
      toffoliGates := st.toffoliGates + executedShots
      qubits := st.qubits.setIfInBounds op.qTarget.toNat qt }
  | .cx =>
    let v := cond &&& st.getQubit op.qControl1
    let qt := st.getQubit op.qTarget ^^^ v
    { st with
      cliffordGates := st.cliffordGates + executedShots
      qubits := st.qubits.setIfInBounds op.qTarget.toNat qt }
  | .swap =>
    let qc1_0 := st.getQubit op.qControl1
    let qt_0  := st.getQubit op.qTarget
    let qc1_1 := qc1_0 ^^^ qt_0
    let qt_1  := qt_0 ^^^ (cond &&& qc1_1)
    let qc1_2 := qc1_1 ^^^ qt_1
    let qArr1 := st.qubits.setIfInBounds op.qControl1.toNat qc1_2
    let qArr2 := qArr1.setIfInBounds op.qTarget.toNat qt_1
    { st with
      cliffordGates := st.cliffordGates + executedShots
      qubits := qArr2 }
  | .x =>
    let qt := st.getQubit op.qTarget ^^^ cond
    { st with qubits := st.qubits.setIfInBounds op.qTarget.toNat qt }
  | .ccz =>
    let v := cond &&& st.getQubit op.qTarget &&& st.getQubit op.qControl1 &&& st.getQubit op.qControl2
    { st with
      toffoliGates := st.toffoliGates + executedShots
      phase := st.phase ^^^ v }
  | .cz =>
    let v := cond &&& st.getQubit op.qTarget &&& st.getQubit op.qControl1
    { st with
      cliffordGates := st.cliffordGates + executedShots
      phase := st.phase ^^^ v }
  | .z =>
    let v := cond &&& st.getQubit op.qTarget
    { st with phase := st.phase ^^^ v }
  | .neg =>
    { st with phase := st.phase ^^^ cond }
  | .hmr =>
    let bt0 := st.getBit op.cTarget
    let bt1 := (bt0 &&& ~~~cond) ^^^ (rngVal &&& cond)
    let qt0 := st.getQubit op.qTarget
    let ph1 := st.phase ^^^ (qt0 &&& rngVal &&& cond)
    let qt1 := qt0 &&& ~~~cond
    { st with
      cliffordGates := st.cliffordGates + executedShots
      phase := ph1
      bits := st.bits.setIfInBounds op.cTarget.toNat bt1
      qubits := st.qubits.setIfInBounds op.qTarget.toNat qt1 }
  | .r =>
    let qt0 := st.getQubit op.qTarget
    let ph1 := st.phase ^^^ (qt0 &&& rngVal &&& cond)
    let qt1 := qt0 &&& ~~~cond
    { st with
      cliffordGates := st.cliffordGates + executedShots
      phase := ph1
      qubits := st.qubits.setIfInBounds op.qTarget.toNat qt1 }
  | .bitInvert =>
    let bt := st.getBit op.cTarget ^^^ cond
    { st with bits := st.bits.setIfInBounds op.cTarget.toNat bt }
  | .bitStore0 =>
    let bt := st.getBit op.cTarget &&& ~~~cond
    { st with bits := st.bits.setIfInBounds op.cTarget.toNat bt }
  | .bitStore1 =>
    let bt := st.getBit op.cTarget ||| cond
    { st with bits := st.bits.setIfInBounds op.cTarget.toNat bt }
  | .appendToRegister | .register | .debugPrint =>
    st
  | .pushCondition =>
    let nextBase := st.currentBaseCond &&& st.getBit op.cCondition
    { st with
      condStack := st.currentBaseCond :: st.condStack
      currentBaseCond := nextBase }
  | .popCondition =>
    match st.condStack with
    | top :: rest => { st with condStack := rest, currentBaseCond := top }
    | []          => st

/-- Step function that threads the RNG word cursor alongside `SimState`. -/
def stepWithRngCursor (st : SimState) (op : Op) (rngWords : Array UInt64) (rngIdx : Nat) : SimState × Nat :=
  if opConsumesRng op.kind then
    let rngVal := rngWords.getD rngIdx 0
    (stepCanonical st op rngVal, rngIdx + 1)
  else
    (stepCanonical st op 0, rngIdx)

/-- Canonical recursive execution over a list of operations. -/
def runCanonicalList (st : SimState) (ops : List Op) (rngWords : Array UInt64) (rngIdx : Nat) : SimState × Nat :=
  match ops with
  | [] => (st, rngIdx)
  | op :: rest =>
    let (st', rngIdx') := stepWithRngCursor st op rngWords rngIdx
    runCanonicalList st' rest rngWords rngIdx'

/-- Canonical execution of an operation sequence starting with an empty condition stack and `u64::MAX` base condition. -/
def runCanonical (st : SimState) (ops : Array Op) (rngWords : Array UInt64) (rngIdx : Nat := 0) : SimState × Nat :=
  let stInit := { st with condStack := [], currentBaseCond := 0xFFFFFFFFFFFFFFFF }
  runCanonicalList stInit ops.toList rngWords rngIdx

/-- 256-bit unsigned integer represented as 4 little-endian 64-bit limbs. -/
structure U256Val where
  limb0 : UInt64
  limb1 : UInt64
  limb2 : UInt64
  limb3 : UInt64
  deriving Repr, DecidableEq, Inhabited

/-- Extract bit `i` (`0..255`) from `U256Val`. -/
def U256Val.getBit (v : U256Val) (i : Nat) : Bool :=
  let limbIdx := i / 64
  let bitIdx  := (i % 64).toUInt64
  let word :=
    match limbIdx with
    | 0 => v.limb0
    | 1 => v.limb1
    | 2 => v.limb2
    | 3 => v.limb3
    | _ => 0
  ((word >>> bitIdx) &&& (1 : UInt64)) != 0

/-- Set bit `i` (`0..255`) in `U256Val`. -/
def U256Val.setBit (v : U256Val) (i : Nat) (b : Bool) : U256Val :=
  let limbIdx := i / 64
  let mask : UInt64 := (1 : UInt64) <<< (i % 64).toUInt64
  let upd (w : UInt64) : UInt64 := if b then w ||| mask else w &&& ~~~mask
  match limbIdx with
  | 0 => { v with limb0 := upd v.limb0 }
  | 1 => { v with limb1 := upd v.limb1 }
  | 2 => { v with limb2 := upd v.limb2 }
  | 3 => { v with limb3 := upd v.limb3 }
  | _ => v

/-- Write a `U256Val` into a register for `shotIdx` (`Simulator::set_register` in `src/sim.rs`). -/
def setRegister (st : SimState) (reg : Array QubitOrBit) (val : U256Val) (shotIdx : Nat) : SimState :=
  let mask : UInt64 := (1 : UInt64) <<< shotIdx.toUInt64
  Id.run do
    let mut s := st
    for i in [0:reg.size] do
      let bitVal := val.getBit i
      match reg[i]! with
      | .qubit qId =>
        let cur := s.getQubit qId
        let next := if bitVal then cur ||| mask else cur &&& ~~~mask
        s := s.setQubit qId next
      | .bit bId =>
        let cur := s.getBit bId
        let next := if bitVal then cur ||| mask else cur &&& ~~~mask
        s := s.setBit bId next
    return s

/-- Read a `U256Val` from a register for `shotIdx` (`Simulator::get_register` in `src/sim.rs`). -/
def getRegister (st : SimState) (reg : Array QubitOrBit) (shotIdx : Nat) : U256Val :=
  let shift := shotIdx.toUInt64
  Id.run do
    let mut v : U256Val := { limb0 := 0, limb1 := 0, limb2 := 0, limb3 := 0 }
    for i in [0:reg.size] do
      let bitVal : Bool :=
        match reg[i]! with
        | .qubit qId => ((st.getQubit qId >>> shift) &&& (1 : UInt64)) != 0
        | .bit bId   => ((st.getBit bId >>> shift) &&& (1 : UInt64)) != 0
      v := v.setBit i bitVal
    return v

/-- Clear all qubits belonging to any register in `regs` (`eval_circuit.rs` lines 326-332). -/
def clearRegisterQubits (st : SimState) (regs : Array (Array QubitOrBit)) : SimState :=
  Id.run do
    let mut qArr := st.qubits
    for reg in regs do
      for item in reg do
        match item with
        | .qubit qId => qArr := qArr.setIfInBounds qId.toNat 0
        | .bit _     => pure ()
    return { st with qubits := qArr }

/-- Batch check outcome matching `eval_circuit.rs` lines 297-354. -/
structure BatchCheckResult where
  classicalFailures  : Nat
  phaseGarbage       : Bool
  ancillaGarbage     : Bool
  firstGarbageQubit  : Option UInt64
  deriving Repr, DecidableEq, Inhabited

/-- Compute active shot mask (`cond_mask` in `eval_circuit.rs`). -/
def batchCondMask (batchShots : Nat) : UInt64 :=
  if batchShots >= 64 then
    0xFFFFFFFFFFFFFFFF
  else
    ((1 : UInt64) <<< batchShots.toUInt64) - 1

/-- Canonical post-simulation batch check matching `eval_circuit.rs`. -/
def checkBatchCanonical
    (stAfter : SimState)
    (regs : Array (Array QubitOrBit))
    (expectedX : Array U256Val)
    (expectedY : Array U256Val)
    (totalQubits : UInt64)
    (batchShots : Nat) : BatchCheckResult :=
  let condMask := batchCondMask batchShots
  let reg0 := regs.getD 0 #[]
  let reg1 := regs.getD 1 #[]
  let classicalFailures := Id.run do
    let mut fails := 0
    for shot in [0:batchShots] do
      let gx := getRegister stAfter reg0 shot
      let gy := getRegister stAfter reg1 shot
      let ex := expectedX.getD shot default
      let ey := expectedY.getD shot default
      if gx != ex || gy != ey then
        fails := fails + 1
    return fails
  let phaseGarbage := (stAfter.phase &&& condMask) != 0
  let stCleared := clearRegisterQubits stAfter regs
  let firstGarbageQubit : Option UInt64 := Id.run do
    let mut found : Option UInt64 := none
    for q in [0:totalQubits.toNat] do
      if found.isNone then
        let qId := q.toUInt64
        if (stCleared.getQubit qId &&& condMask) != 0 then
          found := some qId
    return found
  { classicalFailures := classicalFailures
    phaseGarbage      := phaseGarbage
    ancillaGarbage    := firstGarbageQubit.isSome
    firstGarbageQubit := firstGarbageQubit }

/-- Evaluation mode distinguishing 64-shot pre-gate estimates from full 9024-shot official runs. -/
inductive RunMode where
  | estimate64
  | official9024
  deriving Repr, DecidableEq, Inhabited

/-- Verification certificate for a circuit evaluation run (`MetaGate` contract). -/
structure Cert where
  mode                   : RunMode
  numShots               : Nat
  opsValid               : Bool
  registersValid         : Bool
  frozenHarnessHashMatch : Bool
  classicalFailures      : Nat
  phaseGarbageBatches    : Nat
  ancillaGarbageBatches  : Nat
  qubits                 : Nat
  toffoliTotal           : Nat
  toffoliRounded         : Nat
  cliffordTotal          : Nat
  deriving Repr, DecidableEq, Inhabited

/-- Score metric `toffoli * qubits` (`write_score` in `eval_circuit.rs`). -/
def Cert.score (c : Cert) : Nat :=
  c.toffoliRounded * c.qubits

/-- Non-vacuous validity predicate for a run certificate. -/
def CertValid (c : Cert) : Bool :=
  c.opsValid &&
  c.registersValid &&
  c.frozenHarnessHashMatch &&
  (c.classicalFailures == 0) &&
  (c.phaseGarbageBatches == 0) &&
  (c.ancillaGarbageBatches == 0) &&
  (c.qubits >= 512) &&
  (c.toffoliRounded > 0)

/-- Pre-gate acceptance predicate: requires valid certificates, at least 64 shots, and strict score improvement. -/
def PreGateAccept (cand base : Cert) : Bool :=
  CertValid cand &&
  CertValid base &&
  (cand.numShots >= 64) &&
  (cand.toffoliRounded * cand.qubits < base.toffoliRounded * base.qubits)

/-- Official promotion gate predicate: strictly requires `RunMode.official9024` with `numShots == 9024` and strict score improvement. -/
def PromotionGateAccept (cand base : Cert) : Bool :=
  CertValid cand &&
  CertValid base &&
  (cand.mode == .official9024) &&
  (cand.numShots == 9024) &&
  (base.mode == .official9024) &&
  (base.numShots == 9024) &&
  (cand.toffoliRounded * cand.qubits < base.toffoliRounded * base.qubits)

end EcdsaVerifier
