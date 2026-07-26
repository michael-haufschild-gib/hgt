import GaloisForLFunctions.HilbertMetric.CCRPowerConcavity
import GaloisForLFunctions.HilbertMetric.GaussianJetPositivity

/-!
# The finite canonical-commutation obstruction and its invariant-block realization

The unrestricted finite canonical commutation relation `T Tᵀ = 1 + Tᵀ T` has no solution in
positive dimension: both sides have the same trace, so the relation forces
`Fintype.card (n ⊕ m) = 0`.  Consequently every statement carrying `IsFullCCRMatrixTuple` is empty
as soon as one mode and one coordinate exist.

The invariant-block relation `IsBlockCCRMatrixTuple` is the exact surviving form.  Under
`IsInvariantFullCompression` it is equivalent to the rectangular completion `IsCCRCompletion` of the
compression and leakage blocks, and it is satisfiable in every mode count and every finite
compression dimension: the block tuple `Matrix.fromBlocks (A i) (B i) 0 0` realizes any commuting
compression with a rectangular completion, and the mode-indexed unit leakage realizes the zero
compression unconditionally.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HilbertMetric

noncomputable section

variable {I n m : Type*} [Fintype I] [DecidableEq I]
  [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-! ## The trace obstruction -/

omit [Fintype I] in
/-- **Finite CCR trace obstruction.**  The unrestricted matrix commutation relation equates the
traces of `T Tᵀ` and `Tᵀ T`, hence annihilates the trace of the identity. -/
theorem card_add_card_eq_zero_of_isFullCCRMatrixTuple
    (T : I → Matrix (n ⊕ m) (n ⊕ m) ℝ) (hccr : IsFullCCRMatrixTuple T) (i : I) :
    Fintype.card n + Fintype.card m = 0 := by
  have h : T i * (T i).transpose = 1 + (T i).transpose * T i := by
    simpa using hccr i i
  have htr := congrArg Matrix.trace h
  rw [Matrix.trace_mul_comm, Matrix.trace_add, Matrix.trace_one] at htr
  have hcard : (Fintype.card (n ⊕ m) : ℝ) = 0 := by linarith
  have hzero : Fintype.card (n ⊕ m) = 0 := by exact_mod_cast hcard
  simpa [Fintype.card_sum] using hzero

/-- In the presence of one mode the unrestricted relation empties the whole coordinate space. -/
theorem isEmpty_of_isFullCCRMatrixTuple [Nonempty I]
    (T : I → Matrix (n ⊕ m) (n ⊕ m) ℝ) (hccr : IsFullCCRMatrixTuple T) :
    IsEmpty n ∧ IsEmpty m := by
  have h := card_add_card_eq_zero_of_isFullCCRMatrixTuple T hccr (Classical.arbitrary I)
  have hn : Fintype.card n = 0 := by omega
  have hm : Fintype.card m = 0 := by omega
  exact ⟨Fintype.card_eq_zero_iff.mp hn, Fintype.card_eq_zero_iff.mp hm⟩

/-- **No finite CCR tuple.**  In positive compression dimension the unrestricted interface is
uninhabited, so every theorem carrying it is vacuous. -/
theorem not_isFullCCRMatrixTuple [Nonempty I] [Nonempty n]
    (T : I → Matrix (n ⊕ m) (n ⊕ m) ℝ) : ¬ IsFullCCRMatrixTuple T := by
  intro hccr
  exact (isEmpty_of_isFullCCRMatrixTuple T hccr).1.elim (Classical.arbitrary n)

theorem not_exists_isFullCCRMatrixTuple [Nonempty I] [Nonempty n] :
    ¬ ∃ T : I → Matrix (n ⊕ m) (n ⊕ m) ℝ, IsFullCCRMatrixTuple T := by
  rintro ⟨T, hT⟩
  exact not_isFullCCRMatrixTuple T hT

/-! ## Realization of the invariant-block interface -/

/-- The block tuple assembled from a compression and a rectangular completion. -/
def blockCCRTuple (A : I → Matrix n n ℝ) (B : I → Matrix n m ℝ) :
    I → Matrix (n ⊕ m) (n ⊕ m) ℝ :=
  fun i => Matrix.fromBlocks (A i) (B i) 0 0

omit [Fintype I] [DecidableEq I] [Fintype n] [DecidableEq n] [Fintype m]
  [DecidableEq m] in
theorem blockCCRTuple_compressionBlock (A : I → Matrix n n ℝ) (B : I → Matrix n m ℝ) :
    fullCCRCompressionBlock (blockCCRTuple A B) = A := by
  funext i
  ext a b
  simp [fullCCRCompressionBlock, blockCCRTuple]

omit [Fintype I] [DecidableEq I] [Fintype n] [DecidableEq n] [Fintype m]
  [DecidableEq m] in
theorem blockCCRTuple_leakageBlock (A : I → Matrix n n ℝ) (B : I → Matrix n m ℝ) :
    fullCCRLeakageBlock (blockCCRTuple A B) = B := by
  funext i
  ext a b
  simp [fullCCRLeakageBlock, blockCCRTuple]

omit [Fintype I] [DecidableEq I] [Fintype n] [DecidableEq n] [Fintype m]
  [DecidableEq m] in
/-- The lower block row vanishes, so the first coordinate summand is invariant. -/
theorem blockCCRTuple_isInvariantFullCompression
    (A : I → Matrix n n ℝ) (B : I → Matrix n m ℝ) :
    IsInvariantFullCompression (blockCCRTuple A B) := by
  intro i a b
  simp [blockCCRTuple]

omit [Fintype I] in
/-- A rectangular CCR completion is exactly the block commutation relation of its block tuple. -/
theorem blockCCRTuple_isBlockCCRMatrixTuple
    (A : I → Matrix n n ℝ) (B : I → Matrix n m ℝ) (hccr : IsCCRCompletion A B) :
    IsBlockCCRMatrixTuple (blockCCRTuple A B) := by
  rw [isBlockCCRMatrixTuple_iff_isCCRCompletion _
    (blockCCRTuple_isInvariantFullCompression A B),
    blockCCRTuple_compressionBlock, blockCCRTuple_leakageBlock]
  exact hccr

omit [Fintype I] in
/-- **Invariant-block realization.**  Every commuting compression with a rectangular completion is
the invariant block of a single matrix tuple satisfying the replacement interfaces. -/
theorem exists_invariantBlockCCRTuple_of_isCCRCompletion
    (A : I → Matrix n n ℝ) (B : I → Matrix n m ℝ)
    (hcomm : IsCommutingCCRCompression A) (hccr : IsCCRCompletion A B) :
    ∃ T : I → Matrix (n ⊕ m) (n ⊕ m) ℝ,
      IsInvariantFullCompression T ∧
        IsCommutingCCRCompression (fullCCRCompressionBlock T) ∧
          IsBlockCCRMatrixTuple T ∧
            fullCCRCompressionBlock T = A ∧ fullCCRLeakageBlock T = B := by
  refine ⟨blockCCRTuple A B, blockCCRTuple_isInvariantFullCompression A B, ?_,
    blockCCRTuple_isBlockCCRMatrixTuple A B hccr,
    blockCCRTuple_compressionBlock A B, blockCCRTuple_leakageBlock A B⟩
  rw [blockCCRTuple_compressionBlock]
  exact hcomm

/-! ## An unconditional witness -/

/-- Mode-indexed unit leakage: mode `i` sends the coordinate `a` to the label `(i, a)`. -/
def unitModeLeakage : I → Matrix n (I × n) ℝ :=
  fun i a p => if p = (i, a) then 1 else 0

/-- The mode-indexed unit leakage is a rectangular CCR completion of the zero compression:
distinct modes leak into orthogonal label blocks. -/
theorem unitModeLeakage_isCCRCompletion :
    IsCCRCompletion (0 : I → Matrix n n ℝ) (unitModeLeakage (I := I) (n := n)) := by
  intro i j
  ext a b
  have hsum :
      (unitModeLeakage (I := I) (n := n) i *
          (unitModeLeakage (I := I) (n := n) j).transpose) a b =
        ∑ p : I × n, (if p = (i, a) then (1 : ℝ) else 0) *
          (if p = (j, b) then (1 : ℝ) else 0) := by
    simp [Matrix.mul_apply, unitModeLeakage, Matrix.transpose_apply]
  rw [hsum, Finset.sum_eq_single (i, a)]
  · by_cases hij : i = j
    · subst hij
      by_cases hab : a = b <;> simp [hab, Prod.ext_iff]
    · simp [hij, Prod.ext_iff]
  · intro p _ hp
    simp [hp]
  · intro h
    exact absurd (Finset.mem_univ (i, a)) h

omit [Fintype I] [DecidableEq I] [DecidableEq n] [DecidableEq m] in
/-- Every product of two zero-compression block tuples vanishes, so the tuple commutes. -/
theorem blockCCRTuple_zero_isCommutingFullTuple (B : I → Matrix n m ℝ) :
    IsCommutingFullTuple (blockCCRTuple (0 : I → Matrix n n ℝ) B) := by
  intro i j
  have hzero : ∀ k l : I,
      blockCCRTuple (0 : I → Matrix n n ℝ) B k *
        blockCCRTuple (0 : I → Matrix n n ℝ) B l = 0 := by
    intro k l
    ext a b
    cases a with
    | inl a =>
      cases b with
      | inl b => simp [blockCCRTuple, Matrix.mul_apply, Fintype.sum_sum_type]
      | inr b => simp [blockCCRTuple, Matrix.mul_apply, Fintype.sum_sum_type]
    | inr a =>
      cases b with
      | inl b => simp [blockCCRTuple, Matrix.mul_apply, Fintype.sum_sum_type]
      | inr b => simp [blockCCRTuple, Matrix.mul_apply, Fintype.sum_sum_type]
  rw [hzero i j, hzero j i]

/-- **Unconditional realization.**  For every finite mode set and every finite compression
dimension the invariance, full commutation, and invariant-block CCR interfaces are simultaneously
satisfied on the coordinate space `n ⊕ (I × n)`. -/
theorem exists_invariant_commuting_blockCCRTuple :
    ∃ T : I → Matrix (n ⊕ (I × n)) (n ⊕ (I × n)) ℝ,
      IsInvariantFullCompression T ∧
        IsCommutingFullTuple T ∧
          IsCommutingCCRCompression (fullCCRCompressionBlock T) ∧
            IsBlockCCRMatrixTuple T := by
  refine ⟨blockCCRTuple (0 : I → Matrix n n ℝ) unitModeLeakage,
    blockCCRTuple_isInvariantFullCompression _ _,
    blockCCRTuple_zero_isCommutingFullTuple _, ?_,
    blockCCRTuple_isBlockCCRMatrixTuple _ _ unitModeLeakage_isCCRCompletion⟩
  rw [blockCCRTuple_compressionBlock]
  intro i j
  simp

/-- **Interface classification.**  In positive dimension the unrestricted finite CCR interface is
uninhabited, while its invariant-block replacement is inhabited. -/
theorem isFullCCRMatrixTuple_empty_and_isBlockCCRMatrixTuple_inhabited
    [Nonempty I] [Nonempty n] :
    (¬ ∃ T : I → Matrix (n ⊕ (I × n)) (n ⊕ (I × n)) ℝ, IsFullCCRMatrixTuple T) ∧
      ∃ T : I → Matrix (n ⊕ (I × n)) (n ⊕ (I × n)) ℝ,
        IsInvariantFullCompression T ∧
          IsCommutingFullTuple T ∧
            IsCommutingCCRCompression (fullCCRCompressionBlock T) ∧
              IsBlockCCRMatrixTuple T :=
  ⟨not_exists_isFullCCRMatrixTuple, exists_invariant_commuting_blockCCRTuple⟩

/-! ## The Gaussian coherent witness -/

/-- The finite coherent Gaussian compression, together with its canonical leakage, is the invariant
block of a matrix tuple satisfying the replacement interfaces.  This carries the whole
`CCRPowerConcavity` surface on a genuinely nonzero compression. -/
theorem exists_gaussianCoherentInvariantBlockCCRTuple {n d : ℕ}
    (y : Fin n → Fin d → ℝ) (hG : (gaussianCoherentGram y).PosDef) :
    ∃ T : Fin d → Matrix (Fin n ⊕ Fin d × Fin n) (Fin n ⊕ Fin d × Fin n) ℝ,
      IsInvariantFullCompression T ∧
        IsCommutingCCRCompression (fullCCRCompressionBlock T) ∧
          IsBlockCCRMatrixTuple T ∧
            fullCCRCompressionBlock T = gaussianCoherentCompression y ∧
              fullCCRLeakageBlock T = gaussianCoherentLeakage y hG :=
  exists_invariantBlockCCRTuple_of_isCCRCompletion
    (gaussianCoherentCompression y) (gaussianCoherentLeakage y hG)
    (gaussianCoherentCompression_commutes y hG)
    (gaussianCoherentLeakage_isCCRCompletion y hG)

end

end GaloisForLFunctions.HilbertMetric
