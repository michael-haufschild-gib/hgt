import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.SoftLogarithmicHalfLineCoercivity
import GaloisForLFunctions.HTGeometry.FourierTranslationModulation

/-!
# The literal soft logarithmic L² domain

Real half-line profiles have finite physical first moment and absolute
logarithmic Fourier moment. The domain permits nonintegrable profiles and
requires no exponential moment. Trial representatives retain their energy.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set
open _root_.RHTower
open scoped FourierTransform
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open HTGeometry CriticalArithmeticCorrelationTheory ArithmeticCastelnuovoSeveri

/-- The finite-energy real half-line domain in ordinary L². -/
structure ClosedSoftLogarithmicHalfLineDomain (v : SoninL2) : Prop where
  real : ∀ᵐ u, (v u).im = 0
  support : ∀ᵐ u, 0 ≤ u → v u = 0
  moment : Integrable (fun u : ℝ => |u| * ‖v u‖ ^ 2)
  logarithmic : Integrable (fun ξ : ℝ => |Real.log (|ξ|)| * ‖fourierUnitary v ξ‖ ^ 2)

/-- The logarithmic Fourier form with linear physical confinement. -/
def closedSoftLogarithmicHalfLineEnergy (v : SoninL2) : ℝ :=
  8 * (∫ u : ℝ, |u| * ‖v u‖ ^ 2) +
    ∫ ξ : ℝ, Real.log |ξ| * ‖fourierUnitary v ξ‖ ^ 2

/-- The unitary Fourier transform agrees almost everywhere with the ordinary trial transform. -/
theorem SoftLogarithmicHalfLineDomain.fourier_representative {F : ℝ → ℝ}
    (hF : SoftLogarithmicHalfLineDomain F) {v : SoninL2}
    (hv : (v : ℝ → ℂ) =ᵐ[volume] cx F) :
    (fourierUnitary v : ℝ → ℂ) =ᵐ[volume] 𝓕 (cx F) := by
  have hv1 : Integrable (v : ℝ → ℂ) := (hF.integrable.ofReal (𝕜 := ℂ)).congr hv.symm
  have he := coeFn_fourierTransform_eq_fourierIntegral v hv1
  change (fourierUnitary v : ℝ → ℂ) =ᵐ[volume] 𝓕 (v : ℝ → ℂ) at he
  exact he.trans (Eventually.of_forall fun ξ => Real.fourier_congr_ae hv ξ)

/-- Every exponential-domain trial has a representative in the finite-energy L² domain. -/
theorem SoftLogarithmicHalfLineDomain.toClosed {F : ℝ → ℝ}
    (hF : SoftLogarithmicHalfLineDomain F) {v : SoninL2}
    (hv : (v : ℝ → ℂ) =ᵐ[volume] cx F) : ClosedSoftLogarithmicHalfLineDomain v := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · filter_upwards [hv] with u hu
    rw [hu]
    exact Complex.ofReal_im (F u)
  · filter_upwards [hv] with u hu
    intro hpos
    rw [hu]
    change (F u : ℂ) = 0
    rw [hF.support u hpos, Complex.ofReal_zero]
  · apply hF.integrable_absMoment.congr
    filter_upwards [hv] with u hu
    exact congrArg (fun z : ℂ => |u| * ‖z‖ ^ 2) hu.symm
  · apply hF.logarithmic.congr
    filter_upwards [hF.fourier_representative hv] with ξ hξ
    exact congrArg (fun z : ℂ => |Real.log (|ξ|)| * ‖z‖ ^ 2) hξ.symm

/-- The literal L² form agrees with the trial energy. -/
theorem SoftLogarithmicHalfLineDomain.closedEnergy_eq {F : ℝ → ℝ}
    (hF : SoftLogarithmicHalfLineDomain F) {v : SoninL2}
    (hv : (v : ℝ → ℂ) =ᵐ[volume] cx F) :
    closedSoftLogarithmicHalfLineEnergy v = softLogarithmicHalfLineEnergy F := by
  have hm : (∫ u : ℝ, |u| * ‖v u‖ ^ 2) = criticalHalfLineFirstMoment F := by
    calc
      _ = ∫ u : ℝ, |u| * ‖cx F u‖ ^ 2 := by
        apply integral_congr_ae
        filter_upwards [hv] with u hu
        exact congrArg (fun z : ℂ => |u| * ‖z‖ ^ 2) hu
      _ = _ := hF.integral_absMoment
  have hl : (∫ ξ : ℝ, Real.log |ξ| * ‖fourierUnitary v ξ‖ ^ 2) =
      logarithmicFourierEnergy F := by
    apply integral_congr_ae
    filter_upwards [hF.fourier_representative hv] with ξ hξ
    exact congrArg (fun z : ℂ => Real.log |ξ| * ‖z‖ ^ 2) hξ
  rw [closedSoftLogarithmicHalfLineEnergy, softLogarithmicHalfLineEnergy, hm, hl]
  ring

theorem ClosedSoftLogarithmicHalfLineDomain.integrable_positiveLogarithm {v : SoninL2}
    (hv : ClosedSoftLogarithmicHalfLineDomain v) :
    Integrable (fun ξ : ℝ => max (Real.log |ξ|) 0 * ‖fourierUnitary v ξ‖ ^ 2) := by
  have hm : Measurable (fun ξ : ℝ => max (Real.log |ξ|) 0) := by fun_prop
  apply hv.logarithmic.mono'
    (hm.aestronglyMeasurable.mul ((Lp.aestronglyMeasurable (fourierUnitary v)).norm.pow 2))
  exact Eventually.of_forall fun ξ => by
    dsimp only [Pi.mul_apply, Pi.pow_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (le_max_right _ _) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_right
      (max_le (le_abs_self _) (abs_nonneg _)) (sq_nonneg _)

theorem ClosedSoftLogarithmicHalfLineDomain.integrable_negativeLogarithm {v : SoninL2}
    (hv : ClosedSoftLogarithmicHalfLineDomain v) :
    Integrable (fun ξ : ℝ => max (-Real.log |ξ|) 0 * ‖fourierUnitary v ξ‖ ^ 2) := by
  have hm : Measurable (fun ξ : ℝ => max (-Real.log |ξ|) 0) := by fun_prop
  apply hv.logarithmic.mono'
    (hm.aestronglyMeasurable.mul ((Lp.aestronglyMeasurable (fourierUnitary v)).norm.pow 2))
  exact Eventually.of_forall fun ξ => by
    dsimp only [Pi.mul_apply, Pi.pow_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (le_max_right _ _) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_right
      (max_le (neg_le_abs _) (abs_nonneg _)) (sq_nonneg _)

/-- The literal energy splits into its physical, positive Fourier, and negative Fourier parts. -/
theorem ClosedSoftLogarithmicHalfLineDomain.energy_eq_parts {v : SoninL2}
    (hv : ClosedSoftLogarithmicHalfLineDomain v) :
    closedSoftLogarithmicHalfLineEnergy v =
      8 * (∫ u : ℝ, |u| * ‖v u‖ ^ 2) +
      (∫ ξ : ℝ, max (Real.log |ξ|) 0 * ‖fourierUnitary v ξ‖ ^ 2) -
        ∫ ξ : ℝ, max (-Real.log |ξ|) 0 * ‖fourierUnitary v ξ‖ ^ 2 := by
  have he : (∫ ξ : ℝ, Real.log |ξ| * ‖fourierUnitary v ξ‖ ^ 2) =
      (∫ ξ : ℝ, max (Real.log |ξ|) 0 * ‖fourierUnitary v ξ‖ ^ 2) -
        ∫ ξ : ℝ, max (-Real.log |ξ|) 0 * ‖fourierUnitary v ξ‖ ^ 2 := by
    rw [← integral_sub hv.integrable_positiveLogarithm hv.integrable_negativeLogarithm]
    apply integral_congr_ae
    exact Eventually.of_forall fun ξ => by
      dsimp only
      by_cases hξ : 0 ≤ Real.log |ξ|
      · rw [max_eq_left hξ, max_eq_right (neg_nonpos.mpr hξ), zero_mul, sub_zero]
      · rw [max_eq_right (lt_of_not_ge hξ).le,
          max_eq_left (neg_nonneg.mpr (lt_of_not_ge hξ).le), zero_mul]
        ring
  rw [closedSoftLogarithmicHalfLineEnergy, he]
  ring

#print axioms SoftLogarithmicHalfLineDomain.toClosed
#print axioms SoftLogarithmicHalfLineDomain.closedEnergy_eq
#print axioms ClosedSoftLogarithmicHalfLineDomain.energy_eq_parts
end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
