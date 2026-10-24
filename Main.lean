import EcdsaVerifier

open EcdsaVerifier

/-- Decompress the zstd body of `ops.bin` (starting at byte 16) via `tail` + `zstd -dc`. -/
def decompressOpsBody (opsBinPath : String) : IO ByteArray := do
  let tmpPath := s!"{opsBinPath}.unpacked.tmp"
  let cmd := s!"tail -c +17 '{opsBinPath}' | zstd -dc > '{tmpPath}'"
  let exitCode ← IO.Process.spawn { cmd := "bash", args := #["-c", cmd] } >>= (·.wait)
  if exitCode != 0 then
    try IO.FS.removeFile tmpPath catch _ => pure ()
    throw (IO.userError s!"zstd decompression failed for {opsBinPath} with exit code {exitCode}")
  let bs ← IO.FS.readBinFile tmpPath
  try IO.FS.removeFile tmpPath catch _ => pure ()
  return bs

/-- Verify the 5 frozen harness SHA-256 hashes in `ecdsafail-clean-campaign`. -/
def checkFrozenHarnessHashes (campaignDir : String) : IO Bool := do
  let checkCmd :=
    s!"cd '{campaignDir}' && sha256sum -c --quiet << 'EOF'\n" ++
    "b35314bc47a5f8eecbf60459e6c76c9b43aa034eeb9b7ec3421655d74f9e890b  src/bin/eval_circuit.rs\n" ++
    "f0c72f2a280cd68acee1dbf8282098f72d6b3bf4311e0abf96d122fe002256d7  src/sim.rs\n" ++
    "ac2255f6bcb6895c9da2dfe21c3a051a0ef8fc4e0af9598634fec0035dbf35c6  src/circuit.rs\n" ++
    "ecfca15ee3b831c243fbea559ff4b8937be47fe591a4f14786ec2b9bfb30bded  src/weierstrass_elliptic_curve.rs\n" ++
    "3c80178b08d29a158abb29a7dcb8eefc67c66f60f2c3bd14483b65eeca0740dc  Cargo.toml\n" ++
    "EOF"
  let exitCode ← IO.Process.spawn { cmd := "bash", args := #["-c", checkCmd] } >>= (·.wait)
  return (exitCode == 0)

/-- Run the end-to-end Lean 4 pre-gate evaluator on `<ops.bin>` and `<batch.bin>`. -/
def runPreGate (opsBinPath : String) (batchBinPath : String) (campaignDir : String) : IO UInt32 := do
  IO.println "=== Lean 4 Verified ECDSA Circuit Simulator & Pre-Gate Checker ==="
  let t0 ← IO.monoMsNow

  -- 1. Check frozen harness hashes
  let hashesOk ← checkFrozenHarnessHashes campaignDir
  IO.println s!"  frozen harness SHA-256 : {if hashesOk then "OK (5/5 matched)" else "MISMATCH"}"
  if !hashesOk then
    IO.eprintln "!! Frozen harness SHA-256 check failed"
    return 1

  -- 2. Read and validate 16-byte QECCOPSZ header of ops.bin
  let hFile ← IO.FS.Handle.mk opsBinPath .read
  let hdrBytes ← hFile.read 16
  let numOps ← match parseOpsHeader hdrBytes with
    | .ok n => pure n
    | .error e =>
      IO.eprintln s!"!! ops.bin header validation failed: {e}"
      return 1
  IO.println s!"  ops.bin header         : QECCOPSZ (declared ops = {numOps})"

  -- 3. Decompress zstd record stream and verify exact size (no trailing data)
  let tDec0 ← IO.monoMsNow
  let opsBytes ← decompressOpsBody opsBinPath
  let tDec1 ← IO.monoMsNow
  IO.println s!"  decompressed body      : {opsBytes.size} bytes in {tDec1 - tDec0} ms"

  -- 4. Validate all operations (`Op::validate`) and run `analyzeOps` in Lean
  let tAna0 ← IO.monoMsNow
  let analysis ← match analyzeAndValidateByteArray opsBytes numOps with
    | .ok a => pure a
    | .error e =>
      IO.eprintln s!"!! Lean Op::validate / analyzeOps failed: {e}"
      return 1
  let regsValid := validateRegisterLayout analysis.registers
  let tAna1 ← IO.monoMsNow
  IO.println s!"  validateOp + analyzeOps: OK ({numOps} ops validated in {tAna1 - tAna0} ms)"
  IO.println s!"  analyzed qubits        : {analysis.numQubits}"
  IO.println s!"  analyzed bits          : {analysis.numBits}"
  IO.println s!"  analyzed registers     : {analysis.numRegisters} (layout valid = {regsValid})"
  if !regsValid then
    IO.eprintln "!! Register layout validation failed"
    return 1

  -- 5. Parse batch.bin (64-shot secp256k1 test points + Fiat-Shamir XOF stream)
  let batchBs ← IO.FS.readBinFile batchBinPath
  if batchBs.size < 24 then
    IO.eprintln "!! batch.bin too short"
    return 1
  let bMagic := String.fromUTF8! (batchBs.extract 0 8)
  if bMagic != "QECCBAT1" then
    IO.eprintln s!"!! bad batch.bin magic '{bMagic}'"
    return 1
  let modeTag := readU64LE batchBs 8
  let numShots := (readU64LE batchBs 16).toNat
  let runMode : RunMode := if modeTag == 1 && numShots == 9024 then .official9024 else .estimate64

  let mut off := 24
  let mut targetX := Array.mkEmpty numShots
  let mut targetY := Array.mkEmpty numShots
  let mut offsetX := Array.mkEmpty numShots
  let mut offsetY := Array.mkEmpty numShots
  let mut expectedX := Array.mkEmpty numShots
  let mut expectedY := Array.mkEmpty numShots
  for _ in [0:numShots] do
    targetX := targetX.push (readU256LE batchBs off)
    targetY := targetY.push (readU256LE batchBs (off + 32))
    offsetX := offsetX.push (readU256LE batchBs (off + 64))
    offsetY := offsetY.push (readU256LE batchBs (off + 96))
    expectedX := expectedX.push (readU256LE batchBs (off + 128))
    expectedY := expectedY.push (readU256LE batchBs (off + 160))
    off := off + 192

  let numRngWords := (readU64LE batchBs off).toNat
  off := off + 8
  let rngByteSlice := batchBs.extract off (off + numRngWords * 8)
  let rngWords := parseRngWordsByteArray rngByteSlice
  off := off + numRngWords * 8
  let rustToffoli := readU64LE batchBs off
  let rustClifford := readU64LE batchBs (off + 8)
  let rustPhase := readU64LE batchBs (off + 16)

  -- 6. Initialize simulator state and load input registers for the 64-shot batch
  let tSim0 ← IO.monoMsNow
  let mut st := SimState.init analysis.numQubits.toNat analysis.numBits.toNat
  let r0 := analysis.registers.getD 0 #[]
  let r1 := analysis.registers.getD 1 #[]
  let r2 := analysis.registers.getD 2 #[]
  let r3 := analysis.registers.getD 3 #[]
  for shot in [0:numShots] do
    st := setRegister st r0 (targetX.getD shot default) shot
    st := setRegister st r1 (targetY.getD shot default) shot
    st := setRegister st r2 (offsetX.getD shot default) shot
    st := setRegister st r3 (offsetY.getD shot default) shot

  -- 7. Execute all 10,161,125 operations in Lean
  let (stAfter, rngConsumed) := runByteArrayOptimized st opsBytes numOps rngWords 0
  let tSim1 ← IO.monoMsNow

  -- 8. Run checkBatchOptimized in Lean
  let batchCheck := checkBatchOptimized stAfter analysis.registers expectedX expectedY analysis.numQubits numShots
  let toffoliRounded := (stAfter.toffoliGates.toNat + numShots / 2) / numShots
  let avgTofF := stAfter.toffoliGates.toFloat / numShots.toFloat
  let avgCliffF := stAfter.cliffordGates.toFloat / numShots.toFloat

  IO.println s!"  simulation time (Lean) : {tSim1 - tSim0} ms ({numShots} shots in parallel)"
  IO.println s!"  XOF words consumed     : {rngConsumed} / {numRngWords}"
  IO.println s!"  classical mismatches   : {batchCheck.classicalFailures}"
  IO.println s!"  phase garbage          : {batchCheck.phaseGarbage}"
  IO.println s!"  ancilla garbage        : {batchCheck.ancillaGarbage}"
  IO.println s!"  Lean total Toffoli     : {stAfter.toffoliGates} (Rust ref: {rustToffoli})"
  IO.println s!"  Lean total Clifford    : {stAfter.cliffordGates} (Rust ref: {rustClifford})"
  IO.println s!"  Lean final phase       : {stAfter.phase} (Rust ref: {rustPhase})"
  IO.println s!"  avg executed Toffoli   : {avgTofF} (rounded = {toffoliRounded})"
  IO.println s!"  avg executed Clifford  : {avgCliffF}"

  if rngConsumed != numRngWords ||
     stAfter.toffoliGates != rustToffoli ||
     stAfter.cliffordGates != rustClifford ||
     stAfter.phase != rustPhase then
    IO.eprintln "!! Lean vs Rust metric/state mismatch on batch"
    return 1

  -- 9. Construct Certificate and evaluate MetaGate predicates
  let baseCert : Cert :=
    { mode                   := .official9024
      numShots               := 9024
      opsValid               := true
      registersValid         := true
      frozenHarnessHashMatch := true
      classicalFailures      := 0
      phaseGarbageBatches    := 0
      ancillaGarbageBatches  := 0
      qubits                 := 1234
      toffoliTotal           := 6696602112
      toffoliRounded         := 742088
      cliffordTotal          := 0 }
  let candCert : Cert :=
    { mode                   := runMode
      numShots               := numShots
      opsValid               := true
      registersValid         := regsValid
      frozenHarnessHashMatch := hashesOk
      classicalFailures      := batchCheck.classicalFailures
      phaseGarbageBatches    := if batchCheck.phaseGarbage then 1 else 0
      ancillaGarbageBatches  := if batchCheck.ancillaGarbage then 1 else 0
      qubits                 := analysis.numQubits.toNat
      toffoliTotal           := stAfter.toffoliGates.toNat
      toffoliRounded         := toffoliRounded
      cliffordTotal          := stAfter.cliffordGates.toNat }

  let certOk := CertValid candCert
  let (preGateOk, promoGateOk) := evalGateDecision candCert baseCert
  let t1 ← IO.monoMsNow

  IO.println s!"  candidate CertValid    : {certOk}"
  IO.println s!"  candidate score        : {candCert.score} (toffoli={candCert.toffoliRounded} * qubits={candCert.qubits})"
  IO.println s!"  baseline score         : {baseCert.score} (toffoli={baseCert.toffoliRounded} * qubits={baseCert.qubits})"
  IO.println s!"  PreGateAccept          : {preGateOk} (strict improvement over baseline required for promotion)"
  IO.println s!"  PromotionGateAccept    : {promoGateOk} (requires RunMode.official9024 & 9024 shots)"
  IO.println s!"  total wall-clock (Lean): {t1 - t0} ms"

  if !certOk then
    IO.eprintln "!! Certificate validation FAILED"
    return 1

  IO.println "=== Lean 4 Pre-Gate Verification PASSED (CertValid = true, 64/64 shots verified) ==="
  return 0

def main (args : List String) : IO UInt32 := do
  match args with
  | ["self-test"] =>
    let ok ← runInternalSelfTests
    if ok then
      IO.println "=== Lean 4 internal self-tests PASSED ==="
      return 0
    else
      return 1
  | ["diff-test", suitePath] =>
    let ok1 ← runInternalSelfTests
    if !ok1 then return 1
    let ok2 ← runDiffTestSuiteFile suitePath
    return if ok2 then 0 else 1
  | ["pregate", opsPath, batchPath, campaignDir] =>
    runPreGate opsPath batchPath campaignDir
  | ["pregate", opsPath, batchPath] =>
    runPreGate opsPath batchPath "/var/lib/sandboxed-node/3bcb57a6-0a96-404c-bb04-1b1e22180951/ecdsafail-clean-campaign"
  | _ =>
    IO.eprintln "Usage:"
    IO.eprintln "  lean-verifier self-test"
    IO.eprintln "  lean-verifier diff-test <suite.bin>"
    IO.eprintln "  lean-verifier pregate <ops.bin> <batch.bin> [campaign_dir]"
    return 1
