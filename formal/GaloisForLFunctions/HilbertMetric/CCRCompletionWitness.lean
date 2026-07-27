import GaloisForLFunctions.HilbertMetric.CCRFiniteBlockObstruction

/-!
# Commuting compressions with a CCR completion

The block-CCR layer consumes `IsCommutingCCRCompression A` together with `IsCCRCompletion A B`.
The corpus proves the second on the zero compression, via the mode-indexed unit leakage, but never
records the first on the same object, so the pair is nowhere realized jointly.

Scalar compressions do both, and not only in the degenerate case: for any weights `c`, the family
`A i = c i • 1` commutes, and the two correction terms of the completion identity coincide —
`(c j • 1)ᵀ (c i • 1) = (c i • 1) (c j • 1)ᵀ = (c i c j) • 1` — so they cancel and the identity
reduces to the one the unit leakage already satisfies.

* **`isCCRCompletion_scalar`**, `isCommutingCCRCompression_scalar`;
* **`exists_commuting_ccrCompletion`** — the pair, jointly realized, with a nonzero compression.
-/

namespace GaloisForLFunctions.HilbertMetric

variable {I n : Type*} [Fintype I] [DecidableEq I] [Fintype n] [DecidableEq n]

omit [Fintype I] [DecidableEq I] in
/-- Scalar compressions commute. -/
theorem isCommutingCCRCompression_scalar (c : I → ℝ) :
    IsCommutingCCRCompression (fun i => c i • (1 : Matrix n n ℝ)) := by
  intro i j
  simp [smul_smul, mul_comm]

/-- **The mode-indexed unit leakage completes every scalar compression.**  The two correction terms
are equal, so they cancel and the identity is the one the leakage already satisfies. -/
theorem isCCRCompletion_scalar (c : I → ℝ) :
    IsCCRCompletion (fun i => c i • (1 : Matrix n n ℝ)) (unitModeLeakage (I := I) (n := n)) := by
  intro i j
  have h := unitModeLeakage_isCCRCompletion (I := I) (n := n) i j
  simp only [Pi.zero_apply, Matrix.transpose_zero, Matrix.mul_zero, sub_zero,
    add_zero] at h
  have hZ : (c j • (1 : Matrix n n ℝ)).transpose * (c i • (1 : Matrix n n ℝ))
      = (c i • (1 : Matrix n n ℝ)) * (c j • (1 : Matrix n n ℝ)).transpose := by
    simp [Matrix.transpose_smul, smul_smul, mul_comm]
  rw [h, hZ, add_sub_cancel_right]

/-- **Joint realization.**  A commuting compression with a CCR completion exists, and the
compression need not be zero. -/
theorem exists_commuting_ccrCompletion (c : I → ℝ) :
    ∃ (A : I → Matrix n n ℝ) (B : I → Matrix n (I × n) ℝ),
      IsCommutingCCRCompression A ∧ IsCCRCompletion A B ∧ A = fun i => c i • (1 : Matrix n n ℝ) :=
  ⟨fun i => c i • (1 : Matrix n n ℝ), unitModeLeakage,
    isCommutingCCRCompression_scalar c, isCCRCompletion_scalar c, rfl⟩

end GaloisForLFunctions.HilbertMetric
