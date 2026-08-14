import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Algebra.Exponential

/-!
# The shifted-symbol resolvent of a bounded operator

For a bounded operator `T` and a real shift `c` exceeding `‖T‖/2`, the operator

`B(c, T) = c - T/2`

is invertible, and its inverse obeys the sharp Neumann bound `‖B(c,T)⁻¹‖ ≤ (c - ‖T‖/2)⁻¹`.  This is
the operator half of the frequency transport: on the high-frequency ray the shift `c = L + r(η)/2`
grows with the frequency `L`, so the inverse is `O(1/L)` uniformly in the symbol `r ≥ 0`.
-/

open Complex NormedSpace

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]

/-- The shifted symbol operator `c - T/2`. -/
def shiftedSymbolOp (c : ℝ) (T : 𝔸) : 𝔸 := ((c : ℂ)) • (1 : 𝔸) - ((2⁻¹ : ℂ)) • T

/-- The explicit Neumann inverse of the shifted symbol operator. -/
def shiftedSymbolInv (c : ℝ) (T : 𝔸) : 𝔸 :=
  ((c : ℂ))⁻¹ • Ring.inverse (1 - (((2 * c : ℝ) : ℂ))⁻¹ • T)

variable {c : ℝ} {T : 𝔸}

omit [CompleteSpace 𝔸] [NormOneClass 𝔸] in
theorem norm_neumann_arg_lt_one (hT : ‖T‖ / 2 < c) :
    ‖(((2 * c : ℝ) : ℂ))⁻¹ • T‖ < 1 := by
  have hc : 0 < c := lt_of_le_of_lt (by positivity) hT
  have h2c : (0:ℝ) < 2 * c := by linarith
  rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h2c]
  rw [inv_mul_lt_one₀ h2c]
  linarith

omit [CompleteSpace 𝔸] [NormOneClass 𝔸] in
theorem shiftedSymbolOp_eq_smul (hc : 0 < c) :
    shiftedSymbolOp c T = ((c : ℂ)) • ((1 : 𝔸) - (((2 * c : ℝ) : ℂ))⁻¹ • T) := by
  have hcne : ((c : ℂ)) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]; exact ne_of_gt hc
  rw [shiftedSymbolOp, smul_sub, smul_smul]
  congr 2
  push_cast
  field_simp

omit [NormOneClass 𝔸] in
theorem shiftedSymbolOp_mul_inv (hT : ‖T‖ / 2 < c) :
    shiftedSymbolOp c T * shiftedSymbolInv c T = 1 := by
  have hc : 0 < c := lt_of_le_of_lt (by positivity) hT
  have hcne : ((c : ℂ)) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]; exact ne_of_gt hc
  have hlt := norm_neumann_arg_lt_one hT
  have hunit : IsUnit ((1 : 𝔸) - (((2 * c : ℝ) : ℂ))⁻¹ • T) := by
    have := (Units.oneSub ((((2 * c : ℝ) : ℂ))⁻¹ • T) hlt).isUnit
    simpa [Units.val_oneSub] using this
  rw [shiftedSymbolOp_eq_smul hc, shiftedSymbolInv, smul_mul_smul_comm,
    Ring.mul_inverse_cancel _ hunit, mul_inv_cancel₀ hcne, one_smul]

omit [NormOneClass 𝔸] in
theorem inv_mul_shiftedSymbolOp (hT : ‖T‖ / 2 < c) :
    shiftedSymbolInv c T * shiftedSymbolOp c T = 1 := by
  have hc : 0 < c := lt_of_le_of_lt (by positivity) hT
  have hcne : ((c : ℂ)) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]; exact ne_of_gt hc
  have hlt := norm_neumann_arg_lt_one hT
  have hunit : IsUnit ((1 : 𝔸) - (((2 * c : ℝ) : ℂ))⁻¹ • T) := by
    have := (Units.oneSub ((((2 * c : ℝ) : ℂ))⁻¹ • T) hlt).isUnit
    simpa [Units.val_oneSub] using this
  rw [shiftedSymbolOp_eq_smul hc, shiftedSymbolInv, smul_mul_smul_comm,
    Ring.inverse_mul_cancel _ hunit, inv_mul_cancel₀ hcne, one_smul]

omit [NormOneClass 𝔸] in
theorem isUnit_shiftedSymbolOp (hT : ‖T‖ / 2 < c) : IsUnit (shiftedSymbolOp c T) :=
  ⟨⟨shiftedSymbolOp c T, shiftedSymbolInv c T, shiftedSymbolOp_mul_inv hT,
    inv_mul_shiftedSymbolOp hT⟩, rfl⟩

/-- **The Neumann bound for the shifted-symbol resolvent.** -/
theorem norm_shiftedSymbolInv_le (hT : ‖T‖ / 2 < c) :
    ‖shiftedSymbolInv c T‖ ≤ (c - ‖T‖ / 2)⁻¹ := by
  have hc : 0 < c := lt_of_le_of_lt (by positivity) hT
  have h2c : (0:ℝ) < 2 * c := by linarith
  have hlt := norm_neumann_arg_lt_one hT
  set t : 𝔸 := (((2 * c : ℝ) : ℂ))⁻¹ • T with ht
  have hnt : ‖t‖ = ‖T‖ / (2 * c) := by
    rw [ht, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h2c]
    ring
  have hgeom : ‖Ring.inverse ((1 : 𝔸) - t)‖ ≤ (1 - ‖t‖)⁻¹ := by
    rw [NormedRing.inverse_one_sub t hlt]
    have h := tsum_geometric_le_of_norm_lt_one t hlt
    rw [norm_one] at h
    have hcast : ‖Units.val (Units.oneSub t hlt)⁻¹‖ = ‖∑' n : ℕ, t ^ n‖ := rfl
    rw [hcast]
    linarith
  have hstep : ‖shiftedSymbolInv c T‖ ≤ c⁻¹ * (1 - ‖t‖)⁻¹ := by
    rw [shiftedSymbolInv, ← ht, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hc]
    exact mul_le_mul_of_nonneg_left hgeom (by positivity)
  refine le_trans hstep (le_of_eq ?_)
  rw [hnt]
  have hden : (1 : ℝ) - ‖T‖ / (2 * c) = (c - ‖T‖ / 2) / c := by field_simp
  rw [hden]
  rw [inv_div]
  have hposd : (0:ℝ) < c - ‖T‖ / 2 := by linarith
  field_simp

end

end GaloisForLFunctions.HTGeometry
