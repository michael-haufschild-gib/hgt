import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicRecoveryPositivity

/-!
# The moments of the recovery shift

The operator induced by multiplication by `u` on the graded defect is the weighted shift with
weights `w_k = δ_(k+1)/δ_k`. Its moments — the squared norms of the powers applied to the first
basis vector, equivalently the diagonal values of `(U^n)^* U^n` there — are exactly the normalized
squared recovery gaps `γ_n = (δ_n/δ_0)²`. Since every weight is at most `1/4`, these moments are
positive and bounded by `16^(-n)`: any compact representing measure for them, as required by the
classical Berger criterion for subnormality, would have to be supported in `[0,1/16]`. Existence of
such a measure is not claimed here.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor

noncomputable section
open Set Polynomial
attribute [local instance] cubicGradedLineNormedGroup cubicGradedLineInnerProductSpace
  cubicGradedLine_complete

/-- The product of the first `n` shift weights. -/
def cubicRecoveryMomentWeight (n : ℕ) : ℝ := ∏ j ∈ Finset.range n, cubicRecoveryShiftWeight j

theorem cubicRecoveryMomentWeight_eq (n : ℕ) :
    cubicRecoveryMomentWeight n = cubicGradedRecoveryGap n / cubicGradedRecoveryGap 0 := by
  induction n with
  | zero =>
    rw [cubicRecoveryMomentWeight, Finset.range_zero, Finset.prod_empty,
      div_self (ne_of_gt (cubicGradedRecoveryGap_positive 0))]
  | succ m ih =>
    have hm : cubicGradedRecoveryGap m ≠ 0 := ne_of_gt (cubicGradedRecoveryGap_positive m)
    have h0 : cubicGradedRecoveryGap 0 ≠ 0 := ne_of_gt (cubicGradedRecoveryGap_positive 0)
    rw [cubicRecoveryMomentWeight, Finset.prod_range_succ, ← cubicRecoveryMomentWeight, ih,
      cubicRecoveryShiftWeight]
    field_simp

theorem cubicRecoveryMomentWeight_pos (n : ℕ) : 0 < cubicRecoveryMomentWeight n :=
  Finset.prod_pos (fun j _ => (cubicRecoveryShiftWeight_bounds j).1)

theorem cubicRecoveryMomentWeight_le (n : ℕ) : cubicRecoveryMomentWeight n ≤ (1/4:ℝ) ^ n := by
  have h1 : cubicRecoveryMomentWeight n ≤ ∏ _j ∈ Finset.range n, (1/4:ℝ) := by
    refine Finset.prod_le_prod (fun j _ => (cubicRecoveryShiftWeight_bounds j).1.le)
      (fun j _ => (cubicRecoveryShiftWeight_bounds j).2)
  simpa using h1

/-- The iterates of the recovery shift on the first basis vector. -/
theorem cubicRecoveryShiftIterate_basis (n : ℕ) :
    (⇑cubicHilbertRecoveryShift)^[n] (cubicHilbertBasis 0)
      = cubicRecoveryMomentWeight n • cubicHilbertBasis n := by
  induction n with
  | zero =>
    rw [Function.iterate_zero_apply, cubicRecoveryMomentWeight, Finset.range_zero,
      Finset.prod_empty, one_smul]
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, map_smul, cubicHilbertRecoveryShift_basis, smul_smul]
    congr 1
    simp only [cubicRecoveryMomentWeight, Finset.prod_range_succ]

theorem cubicRecoveryShiftIterate_basis_norm (n : ℕ) :
    ‖(⇑cubicHilbertRecoveryShift)^[n] (cubicHilbertBasis 0)‖
      = cubicGradedRecoveryGap n / cubicGradedRecoveryGap 0 := by
  rw [cubicRecoveryShiftIterate_basis, norm_smul, Real.norm_eq_abs,
    abs_of_pos (cubicRecoveryMomentWeight_pos n), cubicHilbertBasis.orthonormal.1 n, mul_one,
    cubicRecoveryMomentWeight_eq]

/-- The `n`-th moment of the recovery shift. -/
def cubicRecoveryMoment (n : ℕ) : ℝ := (cubicGradedRecoveryGap n / cubicGradedRecoveryGap 0) ^ 2

/-- **The moment identity.** The `n`-th moment of the recovery shift is the normalized squared
recovery gap. -/
theorem cubicRecoveryMoment_eq_norm_sq (n : ℕ) :
    cubicRecoveryMoment n = ‖(⇑cubicHilbertRecoveryShift)^[n] (cubicHilbertBasis 0)‖ ^ 2 := by
  rw [cubicRecoveryMoment, cubicRecoveryShiftIterate_basis_norm]

/-- The same moment in inner-product form. -/
theorem cubicRecoveryMoment_eq_inner (n : ℕ) :
    cubicRecoveryMoment n
      = inner ℝ ((⇑cubicHilbertRecoveryShift)^[n] (cubicHilbertBasis 0))
          ((⇑cubicHilbertRecoveryShift)^[n] (cubicHilbertBasis 0)) := by
  rw [cubicRecoveryMoment_eq_norm_sq, real_inner_self_eq_norm_sq]

theorem cubicRecoveryMoment_zero : cubicRecoveryMoment 0 = 1 := by
  rw [cubicRecoveryMoment, div_self (ne_of_gt (cubicGradedRecoveryGap_positive 0)), one_pow]

theorem cubicRecoveryMoment_succ (n : ℕ) :
    cubicRecoveryMoment (n + 1) = cubicRecoveryShiftWeight n ^ 2 * cubicRecoveryMoment n := by
  have hn : cubicGradedRecoveryGap n ≠ 0 := ne_of_gt (cubicGradedRecoveryGap_positive n)
  have h0 : cubicGradedRecoveryGap 0 ≠ 0 := ne_of_gt (cubicGradedRecoveryGap_positive 0)
  rw [cubicRecoveryMoment, cubicRecoveryMoment, cubicRecoveryShiftWeight]
  field_simp

theorem cubicRecoveryMoment_pos (n : ℕ) : 0 < cubicRecoveryMoment n := by
  rw [cubicRecoveryMoment, ← cubicRecoveryMomentWeight_eq]
  exact pow_pos (cubicRecoveryMomentWeight_pos n) 2

/-- Every moment is at most `16^(-n)`: a compact representing measure would be supported in
`[0,1/16]`. -/
theorem cubicRecoveryMoment_le (n : ℕ) : cubicRecoveryMoment n ≤ ((16:ℝ)⁻¹) ^ n := by
  have h1 := cubicRecoveryMomentWeight_le n
  have h2 := cubicRecoveryMomentWeight_pos n
  rw [cubicRecoveryMoment, ← cubicRecoveryMomentWeight_eq]
  have h3 : cubicRecoveryMomentWeight n ^ 2 ≤ ((1/4:ℝ) ^ n) ^ 2 := by
    exact pow_le_pow_left₀ h2.le h1 2
  calc cubicRecoveryMomentWeight n ^ 2 ≤ ((1/4:ℝ) ^ n) ^ 2 := h3
    _ = ((16:ℝ)⁻¹) ^ n := by
        rw [← pow_mul, mul_comm, pow_mul]
        norm_num

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
