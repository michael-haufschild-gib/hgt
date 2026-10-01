import GaloisForLFunctions.RHTower.MertensVonMangoldtEulerConstant
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Unconditional weighted energy of the dyadic Chebyshev discrepancy

The PNT error integral and the global Chebyshev bound imply square integrability
of `ψ(x)-2ψ(x/2)` with weight `x⁻³` on `(1,∞)`. A reciprocal Jacobian transports
this finite energy to `t dt` on `(0,1]`. The exact reciprocal integral identity
and its integrability equivalence include the endpoint audit.

This supplies the arithmetic source for weighted logarithmic Fermi approximation.
It does not supply the stronger weight `x⁻²` required by the canonical PM norm.
-/

open MeasureTheory Set Filter Topology
noncomputable section
namespace RHTower

theorem abs_chebyshevError_le_linear {x : ℝ} (hx : 0 ≤ x) :
    |chebyshevError x| ≤ (Real.log 4 + 5) * x := by
  have hψ := Chebyshev.psi_le_const_mul_self hx
  have hψ0 := Chebyshev.psi_nonneg x
  have hl : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
  unfold chebyshevError
  apply abs_le.mpr
  constructor <;> nlinarith

theorem integrableOn_chebyshevError_div_sq_half :
    IntegrableOn (fun x : ℝ => chebyshevError x / x ^ 2) (Ioi (1 / 2 : ℝ)) := by
  have hloc : IntegrableOn (fun x : ℝ => chebyshevError x / x ^ 2)
      (Ioc (1 / 2 : ℝ) 1) := by
    refine Measure.integrableOn_of_bounded (M := 4 * (Real.log 4 + 5))
      measure_Ioc_lt_top.ne
      (measurable_chebyshevError.div (measurable_id.pow_const 2)).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    rcases hx with ⟨hxlo, hxhi⟩
    rw [Real.norm_eq_abs, abs_div, abs_sq]
    apply (div_le_iff₀ (sq_pos_of_pos (by linarith : 0 < x))).mpr
    have he := abs_chebyshevError_le_linear (by linarith : 0 ≤ x)
    have hl : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
    have hx2 : (1 / 4 : ℝ) ≤ x ^ 2 := by nlinarith [sq_nonneg (x - 1 / 2)]
    nlinarith [mul_le_mul_of_nonneg_left hx2 (by positivity : 0 ≤ Real.log (4 : ℝ) + 5)]
  have hu := hloc.union integrableOn_chebyshevError_div_sq
  simpa only [Ioc_union_Ioi_eq_Ioi (by norm_num : (1 / 2 : ℝ) ≤ 1)] using hu

theorem integrableOn_sq_chebyshevError_div_cube_half :
    IntegrableOn (fun x : ℝ => chebyshevError x ^ 2 / x ^ 3) (Ioi (1 / 2 : ℝ)) := by
  have hi := integrableOn_chebyshevError_div_sq_half.norm.const_mul (Real.log 4 + 5)
  refine hi.mono'
    ((measurable_chebyshevError.pow_const 2).div
      (measurable_id.pow_const 3)).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : 0 < x := lt_trans (by norm_num) hx
  rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (sq_nonneg _),
    abs_of_pos (pow_pos hx0 3), Real.norm_eq_abs, abs_div,
    abs_sq]
  have he := mul_le_mul_of_nonneg_right (abs_chebyshevError_le_linear hx0.le)
    (abs_nonneg (chebyshevError x))
  rw [← sq, sq_abs] at he
  apply (div_le_iff₀ (pow_pos hx0 3)).mpr
  calc
    chebyshevError x ^ 2 ≤ (Real.log 4 + 5) * x * |chebyshevError x| := by simpa [sq_abs] using he
    _ = (Real.log 4 + 5) * (|chebyshevError x| / x ^ 2) * x ^ 3 := by field_simp

/-- The dyadic discrepancy cancels the linear term of the Chebyshev function. -/
def dyadicChebyshevError (x : ℝ) : ℝ := Chebyshev.psi x - 2 * Chebyshev.psi (x / 2)

theorem dyadicChebyshevError_eq (x : ℝ) :
    dyadicChebyshevError x = chebyshevError x - 2 * chebyshevError (x / 2) := by
  unfold dyadicChebyshevError chebyshevError
  ring

theorem measurable_dyadicChebyshevError : Measurable dyadicChebyshevError :=
  measurable_psi.sub (measurable_const.mul (measurable_psi.comp (measurable_id.div_const 2)))

theorem integrableOn_sq_dyadicChebyshevError_div_cube :
    IntegrableOn (fun x : ℝ => dyadicChebyshevError x ^ 2 / x ^ 3) (Ioi (1 : ℝ)) := by
  have he := integrableOn_sq_chebyshevError_div_cube_half
  have he1 := he.mono_set (Ioi_subset_Ioi (by norm_num : (1 / 2 : ℝ) ≤ 1))
  have he2 : IntegrableOn (fun x : ℝ => chebyshevError (x / 2) ^ 2 / x ^ 3) (Ioi 1) := by
    have hc := (integrableOn_Ioi_comp_mul_left_iff
      (fun x : ℝ => chebyshevError x ^ 2 / x ^ 3) 1 (by norm_num : (0 : ℝ) < 1 / 2)).mpr
      (by simpa using he)
    refine IntegrableOn.congr_fun (hc.const_mul (1 / 8 : ℝ)) (fun x _ => ?_) measurableSet_Ioi
    rw [show (1 / 2 : ℝ) * x = x / 2 by ring]
    ring
  refine ((he1.const_mul 2).add (he2.const_mul 8)).mono'
    ((measurable_dyadicChebyshevError.pow_const 2).div
      (measurable_id.pow_const 3)).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : 0 < x := lt_trans (by norm_num) hx
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) (by positivity)),
    dyadicChebyshevError_eq]
  have h : (chebyshevError x - 2 * chebyshevError (x / 2)) ^ 2 ≤
      2 * chebyshevError x ^ 2 + 8 * chebyshevError (x / 2) ^ 2 := by
    nlinarith [sq_nonneg (chebyshevError x + 2 * chebyshevError (x / 2))]
  calc
    _ ≤ (2 * chebyshevError x ^ 2 + 8 * chebyshevError (x / 2) ^ 2) / x ^ 3 :=
      div_le_div_of_nonneg_right h (by positivity)
    _ = _ := by dsimp; ring

theorem image_inv_Ioc_zero_one : (fun t : ℝ => t⁻¹) '' Ioc 0 1 = Ici 1 := by
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact (one_le_inv₀ ht.1).mpr ht.2
  · intro hx
    have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
    exact ⟨x⁻¹, ⟨inv_pos.mpr hx0, (inv_le_one₀ hx0).mpr hx⟩, inv_inv x⟩

theorem reciprocal_cube_jacobian (q : ℝ → ℝ) {t : ℝ} (ht : 0 < t) :
    |-(t ^ 2)⁻¹| • (q t⁻¹ ^ 2 / (t⁻¹) ^ 3) = t * q t⁻¹ ^ 2 := by
  simp only [smul_eq_mul, abs_neg, abs_inv, abs_sq]
  field_simp

theorem integrableOn_mul_sq_comp_inv_iff (q : ℝ → ℝ) :
    IntegrableOn (fun t : ℝ => t * q t⁻¹ ^ 2) (Ioc 0 1) ↔
      IntegrableOn (fun x : ℝ => q x ^ 2 / x ^ 3) (Ioi 1) := by
  have hi := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioc
    (fun x (hx : x ∈ Ioc (0 : ℝ) 1) => (hasDerivAt_inv hx.1.ne').hasDerivWithinAt)
    (inv_injective.injOn) (fun x : ℝ => q x ^ 2 / x ^ 3)
  rw [image_inv_Ioc_zero_one, integrableOn_Ici_iff_integrableOn_Ioi] at hi
  exact (integrableOn_congr_fun (fun t ht => (reciprocal_cube_jacobian q ht.1).symm)
    measurableSet_Ioc).trans hi.symm

theorem integral_mul_sq_comp_inv (q : ℝ → ℝ) :
    (∫ t in Ioc (0 : ℝ) 1, t * q t⁻¹ ^ 2) =
      ∫ x in Ioi (1 : ℝ), q x ^ 2 / x ^ 3 := by
  have hi := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioc
    (fun x (hx : x ∈ Ioc (0 : ℝ) 1) => (hasDerivAt_inv hx.1.ne').hasDerivWithinAt)
    (inv_injective.injOn) (fun x : ℝ => q x ^ 2 / x ^ 3)
  rw [image_inv_Ioc_zero_one, integral_Ici_eq_integral_Ioi] at hi
  rw [hi]
  exact setIntegral_congr_fun measurableSet_Ioc
    (fun t ht => (reciprocal_cube_jacobian q ht.1).symm)

theorem integrableOn_weighted_dyadicChebyshevError :
    IntegrableOn (fun t : ℝ => t *
      (2 * Chebyshev.psi (1 / (2 * t)) - Chebyshev.psi (1 / t)) ^ 2) (Ioc 0 1) := by
  have hi := (integrableOn_mul_sq_comp_inv_iff dyadicChebyshevError).mpr
    integrableOn_sq_dyadicChebyshevError_div_cube
  refine hi.congr_fun (fun t _ => ?_) measurableSet_Ioc
  dsimp [dyadicChebyshevError]
  rw [show t⁻¹ / 2 = 1 / (2 * t) by ring, ← one_div t]
  ring

end RHTower
