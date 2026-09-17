import GaloisForLFunctions.RHTower.DeningerSuspensionTranslation
import GaloisForLFunctions.RHTower.SelbergMaassFourierModes
import GaloisForLFunctions.RHTower.SelbergMaassRationalCuspTransport

/-!
# Affine transport of cusp Fourier coefficients

The rational cusp factorization reduces a pullback at an integral cusp to an
upper-triangular real action. Its analytic contribution is affine in the
horizontal coordinate. This file identifies those coordinates and proves the
exact Fourier effect: dilation changes period, while translation contributes
one explicit Fourier character.
-/

namespace GaloisForLFunctions.RHTower

open MeasureTheory
open _root_.RHTower
open Complex UpperHalfPlane SelbergMaassMean Matrix SpecialLinearGroup GeneralLinearGroup
open scoped MatrixGroups

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
    have hca : (a : ℂ) ≠ 0 := by exact_mod_cast ha
    have hcw : (w : ℂ) ≠ 0 := by exact_mod_cast hw
    field_simp [hca, hcw, haw]
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
  field_simp [hca, hcw, haw]

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

/-- Horizontal scale of an upper-triangular real Möbius transformation. -/
def upperTriangularScale (U : GL (Fin 2) ℝ) : ℝ := U 0 0 / U 1 1

/-- Horizontal translation of an upper-triangular real Möbius transformation. -/
def upperTriangularShift (U : GL (Fin 2) ℝ) : ℝ := U 0 1 / U 1 1

/-- A positive-determinant upper-triangular transformation has nonzero lower diagonal entry. -/
theorem upperTriangular_denom_ne_zero (U : GL (Fin 2) ℝ) (hU : U 1 0 = 0)
    (hdet : 0 < U.det.val) : U 1 1 ≠ 0 := by
  have hdet' : 0 < (U.val).det := by
    simpa only [Matrix.GeneralLinearGroup.val_det_apply] using hdet
  intro hzero
  rw [Matrix.det_fin_two, hU, hzero] at hdet'
  norm_num at hdet'

/-- The cusp scale of a positive upper-triangular Möbius transformation is positive. -/
theorem upperTriangular_scale_pos (U : GL (Fin 2) ℝ) (hU : U 1 0 = 0)
    (hdet : 0 < U.det.val) : 0 < upperTriangularScale U := by
  have hdet' : 0 < (U.val).det := by
    simpa only [Matrix.GeneralLinearGroup.val_det_apply] using hdet
  have hprod : 0 < U 0 0 * U 1 1 := by
    simpa only [Matrix.det_fin_two, hU, mul_zero, sub_zero] using hdet'
  exact div_pos_iff.mpr (mul_pos_iff.mp hprod)

/-- Positive upper-triangular `GL(2,ℝ)` actions are literal affine maps in the complex chart. -/
theorem upperTriangular_coe_smul (U : GL (Fin 2) ℝ) (hU : U 1 0 = 0)
    (hdet : 0 < U.det.val) (z : ℍ) :
    ((U • z : ℍ) : ℂ) =
      (((U 0 0 : ℝ) : ℂ) * (z : ℂ) + (U 0 1 : ℝ)) / (U 1 1 : ℝ) := by
  have hdet' : 0 < (U.val).det := by
    simpa only [Matrix.GeneralLinearGroup.val_det_apply] using hdet
  rw [UpperHalfPlane.coe_smul]
  simp [UpperHalfPlane.σ, hdet', UpperHalfPlane.num, UpperHalfPlane.denom, hU]

/-- On a horizontal cusp slice, a positive upper-triangular action has the scale and translation
used by `deningerFourierCoeff_comp_affine`. -/
theorem upperTriangular_smul_point (U : GL (Fin 2) ℝ) (hU : U 1 0 = 0)
    (hdet : 0 < U.det.val) (x y : ℝ) (hy : 0 < y) :
    ((U • UpperHalfPlane.ofComplex (point x y) : ℍ) : ℂ) =
      point (upperTriangularScale U * x + upperTriangularShift U)
        (upperTriangularScale U * y) := by
  rw [upperTriangular_coe_smul U hU hdet]
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos]
  · have hdenom := upperTriangular_denom_ne_zero U hU hdet
    apply Complex.ext <;> simp [point, upperTriangularScale, upperTriangularShift]
    all_goals field_simp [hdenom]
  · simp [point, hy]

/-- At every integral cusp, a positive rational correspondence factors into an integral scaling
and a positive upper-triangular real transformation. -/
theorem rationalGL_integral_cusp_factor (g : GL (Fin 2) ℚ)
    (hg : 0 < (g.map (algebraMap ℚ ℝ)).det.val) (B : SL2Z) :
    ∃ A : SL2Z, ∃ U : GL (Fin 2) ℝ,
      U 1 0 = 0 ∧ 0 < U.det.val ∧
        g.map (algebraMap ℚ ℝ) * mapGL ℝ B = mapGL ℝ A * U := by
  let gB : GL (Fin 2) ℚ := g * mapGL ℚ B
  obtain ⟨A, hA⟩ := rationalGL_exists_integral_upperTriangular gB
  let U : GL (Fin 2) ℝ := (mapGL ℝ A)⁻¹ * gB.map (algebraMap ℚ ℝ)
  have hUdet : U.det.val = (g.map (algebraMap ℚ ℝ)).det.val := by
    dsimp only [U, gB]
    simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
  refine ⟨A, U, ?_, ?_, ?_⟩
  · simpa only [U] using hA
  · rw [hUdet]
    exact hg
  · have hmul : gB.map (algebraMap ℚ ℝ) =
        g.map (algebraMap ℚ ℝ) * mapGL ℝ B := by
      rw [rationalGL_mul_integral_real]
    dsimp only [U]
    rw [← hmul]
    group

/-- A positive rational pullback, viewed from any integral cusp, is exactly an integral
translate after one affine change of the horizontal cusp coordinate. -/
theorem rationalGL_pullback_cusp_affine (g : GL (Fin 2) ℚ)
    (hg : 0 < (g.map (algebraMap ℚ ℝ)).det.val) (B : SL2Z) (F : ℍ → ℂ)
    (x y : ℝ) (hy : 0 < y) :
    ∃ A : SL2Z, ∃ U : GL (Fin 2) ℝ,
      U 1 0 = 0 ∧ 0 < U.det.val ∧
        F (g.map (algebraMap ℚ ℝ) •
          (mapGL ℝ B • UpperHalfPlane.ofComplex (point x y))) =
        F (mapGL ℝ A • UpperHalfPlane.ofComplex
          (point (upperTriangularScale U * x + upperTriangularShift U)
            (upperTriangularScale U * y))) := by
  obtain ⟨A, U, hU, hdet, hfactor⟩ := rationalGL_integral_cusp_factor g hg B
  refine ⟨A, U, hU, hdet, ?_⟩
  have hpoint : U • UpperHalfPlane.ofComplex (point x y) =
      UpperHalfPlane.ofComplex
        (point (upperTriangularScale U * x + upperTriangularShift U)
          (upperTriangularScale U * y)) := by
    apply UpperHalfPlane.ext
    rw [upperTriangular_smul_point U hU hdet x y hy]
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos]
    simp [point, upperTriangular_scale_pos U hU hdet, hy]
  calc
    F (g.map (algebraMap ℚ ℝ) •
        (mapGL ℝ B • UpperHalfPlane.ofComplex (point x y))) =
        F ((g.map (algebraMap ℚ ℝ) * mapGL ℝ B) •
          UpperHalfPlane.ofComplex (point x y)) := by
      rw [mul_smul]
    _ = F ((mapGL ℝ A * U) • UpperHalfPlane.ofComplex (point x y)) :=
      congrArg (fun M : GL (Fin 2) ℝ => F (M • UpperHalfPlane.ofComplex (point x y))) hfactor
    _ = F (mapGL ℝ A • (U • UpperHalfPlane.ofComplex (point x y))) := by
      rw [mul_smul]
    _ = F (mapGL ℝ A • UpperHalfPlane.ofComplex
        (point (upperTriangularScale U * x + upperTriangularShift U)
          (upperTriangularScale U * y))) := by rw [hpoint]

end

end GaloisForLFunctions.RHTower
