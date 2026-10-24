import Std.Tactic.BVDecide
import EcdsaVerifier.CanonicalSpec
import EcdsaVerifier.OptimizedChecker

namespace EcdsaVerifier

/-- `stepOptimized` is extensionally equal to `stepCanonical` on all valid inputs. -/
theorem stepOptimized_eq_stepCanonical
    (st : SimState) (op : Op) (rngVal : UInt64)
    (hValid : validateOp op = true) :
    stepOptimized st op rngVal = stepCanonical st op rngVal := by
  have _ := hValid
  rfl

/-- `runOptimizedList` is extensionally equal to `runCanonicalList`. -/
theorem runOptimizedList_eq_runCanonicalList
    (st : SimState) (ops : List Op) (rngWords : Array UInt64) (rngIdx : Nat) :
    runOptimizedList st ops rngWords rngIdx = runCanonicalList st ops rngWords rngIdx := by
  induction ops generalizing st rngIdx with
  | nil => rfl
  | cons op rest ih =>
    simp only [runOptimizedList, runCanonicalList, stepOptimizedWithRng]
    exact ih _ _

/-- `runOptimized` is extensionally equal to `runCanonical` on all valid circuits. -/
theorem runOptimized_eq_runCanonical
    (st : SimState) (ops : Array Op) (rngWords : Array UInt64) (rngIdx : Nat)
    (hValid : validateOps ops = true) :
    runOptimized st ops rngWords rngIdx = runCanonical st ops rngWords rngIdx := by
  have _ := hValid
  unfold runOptimized runCanonical
  exact runOptimizedList_eq_runCanonicalList
    { st with condStack := [], currentBaseCond := 0xFFFFFFFFFFFFFFFF }
    ops.toList rngWords rngIdx

/-- `checkBatchOptimized` is extensionally equal to `checkBatchCanonical`. -/
theorem checkBatchOptimized_eq_checkBatchCanonical
    (stAfter : SimState) (regs : Array (Array QubitOrBit))
    (expectedX expectedY : Array U256Val) (totalQubits : UInt64) (batchShots : Nat)
    (hShots : batchShots <= 64) :
    checkBatchOptimized stAfter regs expectedX expectedY totalQubits batchShots =
      checkBatchCanonical stAfter regs expectedX expectedY totalQubits batchShots := by
  have _ := hShots
  rfl

/-- `evalGateDecision` computes both `PreGateAccept` and `PromotionGateAccept`. -/
theorem evalGateDecision_eq_canonical
    (cand base : Cert)
    (hBaseValid : CertValid base = true) :
    evalGateDecision cand base = (PreGateAccept cand base, PromotionGateAccept cand base) := by
  have _ := hBaseValid
  rfl

/-- `validateOp` rejects any operation where `qTarget == qControl1` and `qTarget != NO_QUBIT`. -/
theorem validateOp_rejects_qTarget_qControl1_alias
    (op : Op)
    (hAlias : op.qTarget = op.qControl1)
    (hNotNo : op.qTarget != NO_QUBIT) :
    validateOp op = false := by
  unfold validateOp hasNoQubitAliasing
  simp [hAlias] at hNotNo ⊢
  simp [hNotNo]

/-- `validateOp` rejects any operation where `qTarget == qControl2` and `qTarget != NO_QUBIT`. -/
theorem validateOp_rejects_qTarget_qControl2_alias
    (op : Op)
    (hAlias : op.qTarget = op.qControl2)
    (hNotNo : op.qTarget != NO_QUBIT) :
    validateOp op = false := by
  unfold validateOp hasNoQubitAliasing
  have hEq : (op.qTarget == op.qControl2) = true := by simp [hAlias]
  simp [hEq, hNotNo]

/-- `validateOp` rejects any operation where `qControl1 == qControl2` and `qControl1 != NO_QUBIT`. -/
theorem validateOp_rejects_qControl1_qControl2_alias
    (op : Op)
    (hAlias : op.qControl1 = op.qControl2)
    (hNotNo : op.qControl1 != NO_QUBIT) :
    validateOp op = false := by
  unfold validateOp hasNoQubitAliasing
  have hEq : (op.qControl1 == op.qControl2) = true := by simp [hAlias]
  simp [hEq, hNotNo]

/-- `CCX` increments `toffoliGates` by `popcount64 (effectiveCond st op)` and preserves `cliffordGates`. -/
theorem stepCanonical_toffoliGates_ccx
    (st : SimState) (op : Op) (rngVal : UInt64)
    (hKind : op.kind = .ccx) :
    (stepCanonical st op rngVal).toffoliGates = st.toffoliGates + popcount64 (effectiveCond st op) ∧
    (stepCanonical st op rngVal).cliffordGates = st.cliffordGates := by
  unfold stepCanonical
  simp [hKind]

/-- `CCZ` increments `toffoliGates` by `popcount64 (effectiveCond st op)` and preserves `cliffordGates`. -/
theorem stepCanonical_toffoliGates_ccz
    (st : SimState) (op : Op) (rngVal : UInt64)
    (hKind : op.kind = .ccz) :
    (stepCanonical st op rngVal).toffoliGates = st.toffoliGates + popcount64 (effectiveCond st op) ∧
    (stepCanonical st op rngVal).cliffordGates = st.cliffordGates := by
  unfold stepCanonical
  simp [hKind]

/-- `CX` increments `cliffordGates` by `popcount64 (effectiveCond st op)` and preserves `toffoliGates`. -/
theorem stepCanonical_cliffordGates_cx
    (st : SimState) (op : Op) (rngVal : UInt64)
    (hKind : op.kind = .cx) :
    (stepCanonical st op rngVal).cliffordGates = st.cliffordGates + popcount64 (effectiveCond st op) ∧
    (stepCanonical st op rngVal).toffoliGates = st.toffoliGates := by
  unfold stepCanonical
  simp [hKind]

/-- `Swap` increments `cliffordGates` by `popcount64 (effectiveCond st op)` and preserves `toffoliGates`. -/
theorem stepCanonical_cliffordGates_swap
    (st : SimState) (op : Op) (rngVal : UInt64)
    (hKind : op.kind = .swap) :
    (stepCanonical st op rngVal).cliffordGates = st.cliffordGates + popcount64 (effectiveCond st op) ∧
    (stepCanonical st op rngVal).toffoliGates = st.toffoliGates := by
  unfold stepCanonical
  simp [hKind]

/-- `R` increments `cliffordGates` by `popcount64 (effectiveCond st op)` and preserves `toffoliGates`. -/
theorem stepCanonical_cliffordGates_r
    (st : SimState) (op : Op) (rngVal : UInt64)
    (hKind : op.kind = .r) :
    (stepCanonical st op rngVal).cliffordGates = st.cliffordGates + popcount64 (effectiveCond st op) ∧
    (stepCanonical st op rngVal).toffoliGates = st.toffoliGates := by
  unfold stepCanonical
  simp [hKind]

/-- `Hmr` increments `cliffordGates` by `popcount64 (effectiveCond st op)` and preserves `toffoliGates`. -/
theorem stepCanonical_cliffordGates_hmr
    (st : SimState) (op : Op) (rngVal : UInt64)
    (hKind : op.kind = .hmr) :
    (stepCanonical st op rngVal).cliffordGates = st.cliffordGates + popcount64 (effectiveCond st op) ∧
    (stepCanonical st op rngVal).toffoliGates = st.toffoliGates := by
  unfold stepCanonical
  simp [hKind]

/-- Pauli `X` is tracked classically and does not increment `toffoliGates` or `cliffordGates`. -/
theorem stepCanonical_gates_preserved_x
    (st : SimState) (op : Op) (rngVal : UInt64)
    (hKind : op.kind = .x) :
    (stepCanonical st op rngVal).toffoliGates = st.toffoliGates ∧
    (stepCanonical st op rngVal).cliffordGates = st.cliffordGates := by
  unfold stepCanonical
  simp [hKind]

/-- `PushCondition` followed by `PopCondition` restores both `condStack` and `currentBaseCond`. -/
theorem stepCanonical_push_pop_roundtrip
    (st : SimState) (pushOp popOp : Op) (r1 r2 : UInt64)
    (hPush : pushOp.kind = .pushCondition)
    (hPop  : popOp.kind = .popCondition) :
    let st1 := stepCanonical st pushOp r1
    let st2 := stepCanonical st1 popOp r2
    st2.condStack = st.condStack ∧ st2.currentBaseCond = st.currentBaseCond := by
  dsimp only
  unfold stepCanonical
  simp [hPush, hPop]

/-- Bitwise masking `(q &&& ~~~cond) &&& cond = 0` guarantees reset operations zero all active shots. -/
theorem reset_mask_clears_active_shots
    (q cond : UInt64)
    (hActive : cond != 0) :
    (q &&& ~~~cond) &&& cond = 0 := by
  have _ := hActive
  bv_decide

/-- PromotionGate strictly rejects any candidate evaluated in `RunMode.estimate64`. -/
theorem promotionGate_rejects_estimate
    (cand base : Cert)
    (hMode : cand.mode = .estimate64) :
    PromotionGateAccept cand base = false := by
  unfold PromotionGateAccept
  simp [hMode]

/-- PromotionGate strictly rejects any candidate whose `numShots` is not `9024`. -/
theorem promotionGate_rejects_wrong_shots
    (cand base : Cert)
    (hShots : cand.numShots != 9024) :
    PromotionGateAccept cand base = false := by
  unfold PromotionGateAccept
  have hNe : (cand.numShots == 9024) = false := by
    cases h : cand.numShots == 9024
    · rfl
    · rw [bne_iff_ne, ne_eq] at hShots
      rw [beq_iff_eq] at h
      exact False.elim (hShots h)
  simp [hNe]

/-- PreGate strictly rejects any candidate with nonzero `classicalFailures`. -/
theorem preGate_rejects_classical_failure
    (cand base : Cert)
    (hFail : cand.classicalFailures > 0) :
    PreGateAccept cand base = false := by
  unfold PreGateAccept CertValid
  have hNe : (cand.classicalFailures == 0) = false := by
    rw [beq_eq_false_iff_ne]
    omega
  simp [hNe]

/-- PreGate strictly rejects any candidate with nonzero `phaseGarbageBatches`. -/
theorem preGate_rejects_phase_garbage
    (cand base : Cert)
    (hPhase : cand.phaseGarbageBatches > 0) :
    PreGateAccept cand base = false := by
  unfold PreGateAccept CertValid
  have hNe : (cand.phaseGarbageBatches == 0) = false := by
    rw [beq_eq_false_iff_ne]
    omega
  simp [hNe]

/-- PreGate strictly rejects any candidate with nonzero `ancillaGarbageBatches`. -/
theorem preGate_rejects_ancilla_garbage
    (cand base : Cert)
    (hAnc : cand.ancillaGarbageBatches > 0) :
    PreGateAccept cand base = false := by
  unfold PreGateAccept CertValid
  have hNe : (cand.ancillaGarbageBatches == 0) = false := by
    rw [beq_eq_false_iff_ne]
    omega
  simp [hNe]

/-- PreGate strictly rejects any candidate when the frozen harness SHA-256 hash check fails. -/
theorem preGate_rejects_unverified_harness
    (cand base : Cert)
    (hHash : cand.frozenHarnessHashMatch = false) :
    PreGateAccept cand base = false := by
  unfold PreGateAccept CertValid
  simp [hHash]

/-- PreGate requires strict score improvement (`cand.toffoliRounded * cand.qubits < base.toffoliRounded * base.qubits`). -/
theorem preGate_requires_strict_score_improvement
    (cand base : Cert)
    (hNoImprove : base.toffoliRounded * base.qubits <= cand.toffoliRounded * cand.qubits) :
    PreGateAccept cand base = false := by
  unfold PreGateAccept
  have hNotLt : decide (cand.toffoliRounded * cand.qubits < base.toffoliRounded * base.qubits) = false := by
    rw [decide_eq_false_iff_not]
    omega
  simp [hNotLt]

end EcdsaVerifier
