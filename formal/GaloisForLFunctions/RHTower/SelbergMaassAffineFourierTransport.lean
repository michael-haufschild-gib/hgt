import GaloisForLFunctions.RHTower.DeningerSuspensionTranslation
import GaloisForLFunctions.RHTower.SelbergMaassRationalCuspTransport

/-!
# Affine transport of cusp Fourier coefficients

The rational cusp factorization reduces a pullback at an integral cusp to an
upper-triangular real action.  Its analytic contribution is affine in the
horizontal coordinate.  This file proves the exact Fourier effect of that
affine map: dilation changes the period, and translation multiplies by one
explicit Fourier character.  Identifying the affine parameters of a concrete
upper-triangular `GL(2, ℝ)` action remains the separate matrix-coordinate step.
-/

namespace GaloisForLFunctions.RHTower

open MeasureTheory

noncomputable section

/-- Rescaling the horizontal coordinate transports a Fourier coefficient to the correspondingly
rescaled period, with no analytic remainder. -/
theorem deningerFourierCoeff_comp_mul {w a : ℝ} (hw : w ≠ 0) (ha : a ≠ 0)
    {F : ℝ → ℂ} (n : ℤ) :
    deningerFourierCoeff w (fun x => F (a * x)) n =
      deningerFourierCoeff (a * w) F n := by
  have hkernel (x : ℝ) : deningerFourierKernel w n x =
      deningerFourierKernel (a * w) n (a * x) := by
    rw [deningerFourierKernel, deningerFourierKernel]
    congr 1
    push_cast
    have haw : (a * w : ℂ) ≠ 0 := by
      exact mul_ne_zero (by exact_mod_cast ha) (by exact_mod_cast hw)
    field_simp
  unfold deningerFourierCoeff
  rw [intervalIntegral.integral_congr (fun x _ => by rw [hkernel])]
  rw [intervalIntegral.integral_comp_mul_left (a := (0 : ℝ)) (b := w)
    (fun u : ℝ => deningerFourierKernel (a * w) n u * F u) ha]
  simp only [mul_zero, Complex.real_smul]
  have haw : (a * w : ℂ) ≠ 0 := by
    exact mul_ne_zero (by exact_mod_cast ha) (by exact_mod_cast hw)
  have hca : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  have hcw : (w : ℂ) ≠ 0 := by exact_mod_cast hw
  push_cast
  field_simp

/-- An affine cusp-coordinate change transports a Fourier coefficient by period dilation and one
translation character. -/
theorem deningerFourierCoeff_comp_affine {w a b : ℝ} (hw : w ≠ 0) (ha : a ≠ 0)
    {F : ℝ → ℂ} (hper : Function.Periodic F (a * w)) (n : ℤ) :
    deningerFourierCoeff w (fun x => F (a * x + b)) n =
      deningerFourierKernel (a * w) n (-b) * deningerFourierCoeff (a * w) F n := by
  let G : ℝ → ℂ := fun u => F (u + b)
  have hG : (fun x => F (a * x + b)) = fun x => G (a * x) := by rfl
  rw [hG, deningerFourierCoeff_comp_mul hw ha]
  have htranslate := deningerFourierCoeff_translate (mul_ne_zero ha hw) hper (-b) n
  simpa only [G, sub_neg_eq_add] using htranslate

end

end GaloisForLFunctions.RHTower
