import GaloisForLFunctions.RHTower.EisensteinMaassSelbergRegion

/-!
# Normalization of the Narain Eisenstein overlap

The primitive-row series agrees with the original Poincaré series.
Its exact constant terms and exponentially decaying tail follow by
dividing the completed Eisenstein model by its leading coefficient.
-/

open Complex RHTower UpperHalfPlane ModularGroup EisensteinSeries
open RHTower.D4BMJointSource
open GaloisForLFunctions.HTGeometry
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

/-- The uncompleted Eisenstein series with leading constant term `y^s`. -/
def narainOverlapEisenstein (s : ℂ) (τ : UpperHalfPlane) : ℂ := (1 / 2 : ℂ) * rowSum s τ

/-- The primitive-row normalization agrees with the actual Poincaré series. -/
theorem narainOverlapEisenstein_eq_poincare {s : ℂ} (hs : 1 < s.re) (τ : UpperHalfPlane) :
    narainOverlapEisenstein s τ =
      d4BMRawEisensteinPoincareSeries ⟨τ.re, τ.im, τ.im_pos⟩ ⟨s, hs⟩ := by
  unfold narainOverlapEisenstein rowSum rowHeight d4BMRawEisensteinPoincareSeries
  rw [← primitiveRowEquiv.tsum_eq (fun v => ((gammaSetMatrix v • τ).im : ℂ) ^ s)]
  simp_rw [← poincareSeed_eq_row_height]

/-- The scattering coefficient in the uncompleted normalization. -/
def narainOverlapScattering (s : ℂ) : ℂ := msB (s - 1 / 2) / msA (s - 1 / 2)

theorem narainOverlapScattering_eq_completedLambda (s : ℂ) :
    narainOverlapScattering s = reflectedCompletedLambda (2 * s - 1) /
      reflectedCompletedLambda (2 * s) := by
  unfold narainOverlapScattering msB msA
  rw [show 2 * (s - 1 / 2) = 2 * s - 1 by ring,
    show 1 + (2 * s - 1) = 2 * s by ring]

/-- Dividing the completed line model gives the same actual primitive-row series. -/
theorem narainOverlapEisenstein_eq_line {s : ℂ} (hs : 1 < s.re) (τ : UpperHalfPlane) :
    narainOverlapEisenstein s τ = eisensteinLineModel (s - 1 / 2) τ / msA (s - 1 / 2) := by
  have hu : 1 / 2 < (s - 1 / 2).re := by simp; linarith only [hs]
  rw [eisensteinLineModel_eq_rowSum hu,
    show (1 / 2 : ℂ) + (s - 1 / 2) = s by ring]
  unfold narainOverlapEisenstein
  rw [mul_div_cancel_left₀ _ (msA_ne_zero_of_re hu)]

/-- The exact constant terms and Fourier tail of the normalized Eisenstein series. -/
theorem narainOverlapEisenstein_expansion {s : ℂ} (hs : 1 < s.re) (τ : UpperHalfPlane) :
    narainOverlapEisenstein s τ = (τ.im : ℂ) ^ s +
      narainOverlapScattering s * (τ.im : ℂ) ^ (1 - s) +
        d4BMCompletedEisensteinCuspTailPart .scalar (s - 1 / 2) τ.re τ.im / msA (s - 1 / 2) := by
  have hu : 1 / 2 < (s - 1 / 2).re := by simp; linarith only [hs]
  rw [narainOverlapEisenstein_eq_line hs]
  unfold eisensteinLineModel d4BMCompletedEisensteinCuspLeg
  rw [cuspConstantPart_eq_msAB,
    show (1 / 2 : ℂ) + (s - 1 / 2) = s by ring,
    show (1 / 2 : ℂ) - (s - 1 / 2) = 1 - s by ring]
  unfold narainOverlapScattering
  rw [add_div, add_div, mul_div_cancel_left₀ _ (msA_ne_zero_of_re hu), div_mul_eq_mul_div]
  ring

/-- Removing the leading constant term leaves a power term and an exponentially decaying tail. -/
theorem norm_narainOverlapEisenstein_sub_le {s : ℂ} (hs : 1 < s.re)
    {τ : UpperHalfPlane} (hτ : 1 / 2 ≤ τ.im) :
    ‖narainOverlapEisenstein s τ - (τ.im : ℂ) ^ s‖ ≤
      ‖narainOverlapScattering s‖ * τ.im ^ (1 - s.re) +
        (tailConst (s - 1 / 2) / ‖msA (s - 1 / 2)‖) * Real.exp (-(2 * Real.pi * τ.im)) := by
  rw [narainOverlapEisenstein_expansion hs]
  rw [show (τ.im : ℂ) ^ s + narainOverlapScattering s * (τ.im : ℂ) ^ (1 - s) +
      d4BMCompletedEisensteinCuspTailPart .scalar (s - 1 / 2) τ.re τ.im / msA (s - 1 / 2) -
      (τ.im : ℂ) ^ s =
      narainOverlapScattering s * (τ.im : ℂ) ^ (1 - s) +
        d4BMCompletedEisensteinCuspTailPart .scalar (s - 1 / 2) τ.re τ.im / msA (s - 1 / 2) by ring]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos τ.im_pos, norm_div]
  have hb := div_le_div_of_nonneg_right
    (norm_cuspTailPart_le_exp (s - 1 / 2) τ.re hτ) (norm_nonneg (msA (s - 1 / 2)))
  simpa only [Complex.sub_re, Complex.one_re, div_mul_eq_mul_div] using
    add_le_add (le_refl (‖narainOverlapScattering s‖ * τ.im ^ (1 - s.re))) hb

#print axioms narainOverlapEisenstein_eq_poincare
#print axioms norm_narainOverlapEisenstein_sub_le
end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
