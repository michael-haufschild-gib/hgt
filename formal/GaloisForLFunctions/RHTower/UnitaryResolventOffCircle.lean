import Mathlib

/-!
# The unitary resolvent off the unit circle

A unitary operator on a Hilbert space is invertible after subtracting any scalar off the unit
circle, with the quantitative lower bound

`| |λ| - 1 | · ‖y‖ ≤ ‖(U - λ) y‖`.

Both halves are elementary: the bound is the reverse triangle inequality, and invertibility is a
Neumann series in `λ U⁻¹` (for `|λ| < 1`) or `λ⁻¹ U` (for `|λ| > 1`).
-/

noncomputable section

namespace RHTower

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The operator underlying a surjective linear isometry — a unitary operator. -/
def unitaryOp (U : H ≃ₗᵢ[ℂ] H) : H →L[ℂ] H :=
  U.toLinearIsometry.toContinuousLinearMap

@[simp]
theorem unitaryOp_apply (U : H ≃ₗᵢ[ℂ] H) (x : H) : unitaryOp U x = U x := rfl

theorem unitaryOp_mul_symm (U : H ≃ₗᵢ[ℂ] H) :
    unitaryOp U * unitaryOp U.symm = 1 := by
  ext x
  simp

theorem unitaryOp_symm_mul (U : H ≃ₗᵢ[ℂ] H) :
    unitaryOp U.symm * unitaryOp U = 1 := by
  ext x
  simp

theorem isUnit_unitaryOp (U : H ≃ₗᵢ[ℂ] H) : IsUnit (unitaryOp U) :=
  ⟨⟨unitaryOp U, unitaryOp U.symm, unitaryOp_mul_symm U, unitaryOp_symm_mul U⟩, rfl⟩

theorem norm_smul_unitaryOp_le (U : H ≃ₗᵢ[ℂ] H) (c : ℂ) :
    ‖c • unitaryOp U‖ ≤ ‖c‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg c) (fun x => ?_)
  show ‖c • unitaryOp U x‖ ≤ ‖c‖ * ‖x‖
  rw [norm_smul, unitaryOp_apply, U.norm_map]

/-- **The reverse-triangle lower bound.**  Off the unit circle a unitary minus a scalar is bounded
below by `| |λ| - 1 |`. -/
theorem norm_sub_smul_lower_bound (U : H ≃ₗᵢ[ℂ] H) (lam : ℂ) (y : H) :
    |‖lam‖ - 1| * ‖y‖ ≤ ‖unitaryOp U y - lam • y‖ := by
  have h3 : |‖unitaryOp U y‖ - ‖lam • y‖| ≤ ‖unitaryOp U y - lam • y‖ :=
    abs_norm_sub_norm_le _ _
  rw [unitaryOp_apply, U.norm_map, norm_smul] at h3
  have h4 : |‖y‖ - ‖lam‖ * ‖y‖| = |‖lam‖ - 1| * ‖y‖ := by
    rw [show ‖y‖ - ‖lam‖ * ‖y‖ = -((‖lam‖ - 1) * ‖y‖) by ring, abs_neg, abs_mul,
      abs_of_nonneg (norm_nonneg y)]
  rw [h4] at h3
  exact h3

/-- The quantitative resolvent bound: the inverse moves norms by at most `1/| |λ| - 1 |`. -/
theorem norm_le_of_unitaryOp_sub_smul (U : H ≃ₗᵢ[ℂ] H) {lam : ℂ} (hlam : ‖lam‖ ≠ 1)
    (y x : H) (hxy : unitaryOp U y - lam • y = x) :
    ‖y‖ ≤ ‖x‖ / |‖lam‖ - 1| := by
  have hpos : 0 < |‖lam‖ - 1| := abs_pos.mpr (sub_ne_zero.mpr hlam)
  rw [le_div_iff₀ hpos, mul_comm]
  rw [← hxy]
  exact norm_sub_smul_lower_bound U lam y

variable [CompleteSpace H]

/-- **The unitary resolvent exists off the unit circle.** -/
theorem isUnit_unitaryOp_sub_smul (U : H ≃ₗᵢ[ℂ] H) {lam : ℂ} (hlam : ‖lam‖ ≠ 1) :
    IsUnit (unitaryOp U - lam • (1 : H →L[ℂ] H)) := by
  rcases lt_or_gt_of_ne hlam with hlt | hgt
  · -- `U - λ = U · (1 - λ U⁻¹)`
    have hnorm : ‖lam • unitaryOp U.symm‖ < 1 :=
      lt_of_le_of_lt (norm_smul_unitaryOp_le U.symm lam) hlt
    have hfac : unitaryOp U - lam • (1 : H →L[ℂ] H)
        = unitaryOp U * (1 - lam • unitaryOp U.symm) := by
      rw [mul_sub, mul_one, mul_smul_comm, unitaryOp_mul_symm]
    rw [hfac]
    exact (isUnit_unitaryOp U).mul ((Units.oneSub _ hnorm).isUnit)
  · -- `U - λ = (-λ) · (1 - λ⁻¹ U)`
    have hlam0 : lam ≠ 0 := by
      intro h
      rw [h, norm_zero] at hgt
      linarith
    have hnorm : ‖lam⁻¹ • unitaryOp U‖ < 1 := by
      refine lt_of_le_of_lt (norm_smul_unitaryOp_le U lam⁻¹) ?_
      rw [norm_inv, inv_lt_one_iff₀]
      exact Or.inr hgt
    have hfac : unitaryOp U - lam • (1 : H →L[ℂ] H)
        = (-lam) • (1 : H →L[ℂ] H) * (1 - lam⁻¹ • unitaryOp U) := by
      rw [mul_sub, mul_one, smul_mul_smul_comm, one_mul]
      rw [show (-lam) * lam⁻¹ = -1 by field_simp]
      module
    have hneg0 : (-lam) ≠ 0 := neg_ne_zero.mpr hlam0
    have hunit : IsUnit ((-lam) • (1 : H →L[ℂ] H)) := by
      refine ⟨⟨(-lam) • (1 : H →L[ℂ] H), (-lam)⁻¹ • (1 : H →L[ℂ] H), ?_, ?_⟩, rfl⟩
      · rw [smul_mul_smul_comm, one_mul, mul_inv_cancel₀ hneg0, one_smul]
      · rw [smul_mul_smul_comm, one_mul, inv_mul_cancel₀ hneg0, one_smul]
    rw [hfac]
    exact hunit.mul ((Units.oneSub _ hnorm).isUnit)

end RHTower
