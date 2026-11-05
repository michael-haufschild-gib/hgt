import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheWeilFormIsCompleteBeforeContact
import GaloisForLFunctions.RHTower.Suzuki.SuzukiTaCharacteristicEntire

/-!
# Entire Fourier coordinates of the pre-contact Weil spaces

The unshifted Weil Hilbert space embeds injectively into entire functions by the literal compact
Fourier transform. Every evaluation is a continuous linear functional and takes the value one on
an explicit smooth compact source. The auxiliary shifted space is used only for its already
identified Fourier integral; the norm remains the exact unshifted Weil form.
-/

open Complex MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.CanonicalSystemOfTheWindowTower.WeilHilbertBeforeContact

open _root_.RHTower ArithmeticContinuationAndCriticalEnergy

variable (a : PrecontactAperture)

/-- Literal Fourier evaluation, transported through the common physical source domain. -/
def eval (z : ℂ) : WeilHilbertBeforeContact a →L[ℂ] ℂ :=
  (suzukiTaSpectralMoment a.1 (star z)).comp
    ((suzukiTaFromFormCLM a.1).comp (toFormCLM a))

/-- The entire Fourier transform of a vector in the exact Weil Hilbert space. -/
def fourier (x : WeilHilbertBeforeContact a) (z : ℂ) : ℂ := eval a z x

theorem fourier_eq_physical (x : WeilHilbertBeforeContact a) (z : ℂ) :
    fourier a x z = suzukiTaPhysicalFourier a.1
      (suzukiTaFromFormCLM a.1 (toForm a x)) z :=
  suzukiTaSpectralMoment_star_eq_physicalFourier a.1 _ z

theorem differentiable_fourier (x : WeilHilbertBeforeContact a) :
    Differentiable ℂ (fourier a x) := by
  have heq : fourier a x = suzukiTaPhysicalFourier a.1
      (suzukiTaFromFormCLM a.1 (toForm a x)) := funext (fourier_eq_physical a x)
  rw [heq]
  exact differentiable_suzukiTaPhysicalFourier a.1 _

/-- The whole-line physical source is unchanged by the auxiliary coordinate transport. -/
theorem fourier_eq_whole (x : WeilHilbertBeforeContact a) (z : ℂ) :
    fourier a x z = suzukiCompactL2Fourier a.1.1
      (ccmArchimedeanFormToAperture a.1 (toForm a x) : SoninL2) z := by
  rw [fourier_eq_physical, suzukiTaPhysicalFourier]
  congr 1
  change ((suzukiApertureL2Equiv a.1)
      ((suzukiApertureL2Equiv a.1).symm
        (ccmArchimedeanFormToAperture a.1 (toForm a x))) : SoninL2) = _
  rw [LinearIsometryEquiv.apply_symm_apply]

/-- The literal aperture bounds the exponential type of every completed transform. -/
theorem fourier_exponentialType (x : WeilHilbertBeforeContact a) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ z : ℂ, ‖fourier a x z‖ ≤ C * Real.exp (a.1.1 * ‖z‖) := by
  simpa only [fourier_eq_whole] using suzukiCompactL2Fourier_exponentialType a.1.2.le
    (ccmArchimedeanFormToAperture a.1 (toForm a x) : SoninL2)

/-- Isometric aperture inclusions preserve the entire function itself. -/
theorem fourier_inclusion {a b : PrecontactAperture} (hab : a.1.1 ≤ b.1.1)
    (x : WeilHilbertBeforeContact a) (z : ℂ) :
    fourier b (inclusion hab x) z = fourier a x z := by
  rw [fourier_eq_whole, fourier_eq_whole, toForm_inclusion]
  have hphys := ccmArchimedeanFormToAperture_coe_eq_of_val_eq
    (apertureExt_val hab (toForm a x))
  have ha : suzukiCutoff a.1.1
      (ccmArchimedeanFormToAperture a.1 (toForm a x) : SoninL2) =
      (ccmArchimedeanFormToAperture a.1 (toForm a x) : SoninL2) :=
    indicatorCutoff_suzukiApertureHilbert a.1 _
  have hb : suzukiCutoff b.1.1
      (ccmArchimedeanFormToAperture b.1 (apertureExt hab (toForm a x)) : SoninL2) =
      (ccmArchimedeanFormToAperture b.1 (apertureExt hab (toForm a x)) : SoninL2) :=
    indicatorCutoff_suzukiApertureHilbert b.1 _
  unfold suzukiCompactL2Fourier
  change (∫ u : ℝ, (suzukiCutoff b.1.1
      (ccmArchimedeanFormToAperture b.1 (apertureExt hab (toForm a x)) : SoninL2)) u *
        Complex.exp (I * z * (u : ℂ))) =
    ∫ u : ℝ, (suzukiCutoff a.1.1
      (ccmArchimedeanFormToAperture a.1 (toForm a x) : SoninL2)) u *
        Complex.exp (I * z * (u : ℂ))
  rw [ha, hb, hphys]

/-- Native smooth compact functions embedded in the unshifted Weil space. -/
def smoothCore : SuzukiTaSmoothCore a.1 →ₗ[ℂ] WeilHilbertBeforeContact a :=
  (fromFormCLM a).toLinearMap.comp (suzukiTaSmoothCoreToForm a.1)

theorem toForm_smoothCore (u : SuzukiTaSmoothCore a.1) :
    toForm a (smoothCore a u) = suzukiTaSmoothCoreToForm a.1 u := rfl

theorem eval_smoothCore (z : ℂ) (u : SuzukiTaSmoothCore a.1) :
    eval a z (smoothCore a u) =
      suzukiTaSpectralMoment a.1 (star z) (suzukiTaSmoothCoreToHilbert a.1 u) := rfl

theorem eval_smoothCore_eq_integral (z : ℂ) (u : SuzukiTaSmoothCore a.1) :
    eval a z (smoothCore a u) =
      ∫ x : ℝ, Complex.exp (I * z * (x : ℂ)) * u x := by
  rw [eval_smoothCore, suzukiTaSpectralMoment_smoothCore_eq_integral, star_star]

/-- A compactly supported exponential tilt of a unit-integral bump normalizes evaluation. -/
def evaluationNormalizer (z : ℂ) : WeilHilbertBeforeContact a :=
  smoothCore a (suzukiTaSpectralMomentNormalizer a.1 (star z))

theorem eval_normalizer (z : ℂ) : eval a z (evaluationNormalizer a z) = 1 := by
  rw [evaluationNormalizer, eval_smoothCore]
  exact suzukiTaSpectralMoment_normalizer a.1 (star z)

theorem eval_surjective (z : ℂ) : Function.Surjective (eval a z) := by
  intro c
  refine ⟨c • evaluationNormalizer a z, ?_⟩
  rw [map_smul, eval_normalizer, smul_eq_mul, mul_one]

/-- Compact Fourier uniqueness makes the entire-function realization faithful. -/
theorem eq_zero_of_fourier_eq_zero (x : WeilHilbertBeforeContact a)
    (hx : ∀ z, fourier a x z = 0) : x = 0 := by
  let y := suzukiTaFromFormCLM a.1 (toForm a x)
  let g := suzukiApertureZeroExtendL2 (suzukiTaPhysicalEmbedding a.1 y)
  have hg : g = 0 :=
    eq_zero_of_supported_fourier_constant_on_xiZeros a.1.2.le
      (suzukiApertureZeroExtendL2_cutoff _) (fun z _ => by
        exact (fourier_eq_physical a x z).symm.trans (hx z))
  have hphys : suzukiTaPhysicalEmbedding a.1 y = 0 := by
    apply norm_eq_zero.mp
    rw [← norm_suzukiApertureZeroExtendL2]
    change ‖g‖ = 0
    rw [hg, norm_zero]
  have hy : y = 0 := by
    apply suzukiTaPhysicalEmbedding_injective a.1
    simpa only [map_zero] using hphys
  apply (toForm a).injective
  have h := congrArg (suzukiTaToFormCLM a.1) hy
  simpa only [y, suzukiTaToFormCLM_fromForm, map_zero] using h

theorem fourier_injective : Function.Injective (fourier a) := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply eq_zero_of_fourier_eq_zero a
  intro z
  change eval a z (x - y) = 0
  rw [map_sub]
  exact sub_eq_zero.mpr (congrFun hxy z)

#print axioms differentiable_fourier
#print axioms fourier_inclusion
#print axioms eval_surjective
#print axioms fourier_injective

end GaloisForLFunctions.CanonicalSystemOfTheWindowTower.WeilHilbertBeforeContact
