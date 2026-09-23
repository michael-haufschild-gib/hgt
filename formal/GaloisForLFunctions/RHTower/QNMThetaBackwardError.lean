import GaloisForLFunctions.HilbertMetric.QNMBackwardError
import GaloisForLFunctions.RHTower.HedenmalmThetaExteriorPseudospectralSeparation

/-!
# QNMThetaBackwardError

The corpus exterior theta pseudomodes become exact eigenvectors of an
explicit rank-one perturbation of the adjoint theta operator. The correction
is exponentially small while the original spectrum keeps its inverse-quadratic
separation. This applies the optical QNM backward-error mechanism to the
existing continuous theta kernel, without any zero-location assumption.
-/

noncomputable section
open Complex Set
open GaloisForLFunctions.HilbertMetric
namespace RHTower.HedenmalmThetaSource
open MeasureTheory HedenmalmQuantile HedenmalmClosedWeightedDerivative
private abbrev ThetaH_hedenmalmThetaEsscherCyclicity_hedenmalmThetaExteriorPseudospectralSeparation := Lp ℂ 2 unitIntervalMeasure

def thetaExteriorQNMCorrection (tau : ℝ) : ThetaH_hedenmalmThetaEsscherCyclicity_hedenmalmThetaExteriorPseudospectralSeparation →L[ℂ] ThetaH_hedenmalmThetaEsscherCyclicity_hedenmalmThetaExteriorPseudospectralSeparation :=
  qnmBackwardCorrection thetaKernelOperator.adjoint 1
    (starRingEnd ℂ (-(thetaEsscherResolventParameter (3 / 4) tau)⁻¹))
    (thetaExteriorPseudomode (3 / 4) tau)

theorem thetaExteriorQNMCorrection_exact (tau : ℝ) :
    (thetaKernelOperator.adjoint + thetaExteriorQNMCorrection tau)
        (thetaExteriorPseudomode (3 / 4) tau) =
      starRingEnd ℂ (-(thetaEsscherResolventParameter (3 / 4) tau)⁻¹) •
        thetaExteriorPseudomode (3 / 4) tau := by
  simpa [thetaExteriorQNMCorrection] using
    qnmBackwardCorrection_exact thetaKernelOperator.adjoint 1
      (starRingEnd ℂ (-(thetaEsscherResolventParameter (3 / 4) tau)⁻¹))
      (thetaExteriorPseudomode (3 / 4) tau)

theorem thetaExteriorQNMCorrection_exponential_separation :
    ∃ C : ℝ, 0 < C ∧ ∀ tau : ℝ,
      ‖thetaExteriorQNMCorrection tau‖ ≤
        C * Real.exp (-(1 / 2) * |tau|) / ‖thetaEsscherResolventParameter (3 / 4) tau‖ ∧
      ∀ mu ∈ spectrum ℂ thetaKernelOperator,
        (1 / 4 : ℝ) /
          (‖thetaEsscherResolventParameter (3 / 4) tau‖ *
            (‖thetaEsscherResolventParameter (3 / 4) tau‖ + 1 / 4)) ≤
          ‖-(thetaEsscherResolventParameter (3 / 4) tau)⁻¹ - mu‖ := by
  have hpi : (1 / 2 : ℝ) < Real.pi / 4 := by nlinarith [Real.pi_gt_three]
  obtain ⟨C, hC, h⟩ := thetaExterior_pseudospectral_separation
    (h := (3 / 4 : ℝ)) (δ := (1 / 2 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) hpi
  refine ⟨C, hC, fun tau => ?_⟩
  obtain ⟨hn, hr, hs⟩ := h tau
  constructor
  · simpa [thetaExteriorQNMCorrection, norm_qnmBackwardCorrection, hn] using hr
  · norm_num at hs ⊢
    exact hs

end RHTower.HedenmalmThetaSource
