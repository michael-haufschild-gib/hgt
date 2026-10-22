import GaloisForLFunctions.HilbertMetric.PseudospectrumSimilarity
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaExteriorPseudospectralSeparation

/-!
# Exterior theta pseudomodes as genuine pseudospectral points

This module converts the existing normalized Hedenmalm theta pseudomodes into the open
norm-resolvent pseudospectrum of the original theta kernel operator.  The conversion combines
equation (6), the pseudomode characterization, with equation (7), adjoint pseudospectral
reflection, from Krejčiřík--Siegl--Tater--Viola, arXiv:1402.1082.

The concrete exterior ray `h = 3/4` and decay rate `δ = 1/2` discharge all assumptions.  Every
frequency supplies a pseudospectral point while the existing inverse-quadratic estimate separates
that point from the true spectrum.  Thus the theorem records genuine nonnormal spectral
instability, not merely a small residual for the adjoint.
-/

open Complex MeasureTheory Set
open GaloisForLFunctions.HilbertMetric

namespace RHTower.HedenmalmThetaSource

noncomputable section

/-- Strict tolerance used to convert the concrete theta residual bound into open membership. -/
def thetaExteriorConcretePseudospectralScale (C tau : ℝ) : PseudospectralScale :=
  ⟨2 * (|C| + 1) * Real.exp (-(1 / 2) * |tau|) /
      ‖thetaEsscherResolventParameter (3 / 4) tau‖, by
    have hz : thetaEsscherResolventParameter (3 / 4) tau ≠ 0 := by
      apply thetaEsscherResolventParameter_ne_zero
      norm_num
    have hnorm : 0 < ‖thetaEsscherResolventParameter (3 / 4) tau‖ :=
      norm_pos_iff.mpr hz
    positivity⟩

/-- Every point on the concrete reciprocal exterior ray lies in an exponentially thin
pseudospectrum while remaining explicitly separated from every true spectral point. -/
theorem thetaExterior_concrete_pseudospectral_separation :
    ∃ C : ℝ, 0 < C ∧ ∀ tau : ℝ,
      -(thetaEsscherResolventParameter (3 / 4) tau)⁻¹ ∈
          normResolventPseudospectrum ℂ
            (thetaExteriorConcretePseudospectralScale C tau)
            thetaKernelOperator ∧
      ∀ mu ∈ spectrum ℂ thetaKernelOperator,
        (1 / 4 : ℝ) /
            (‖thetaEsscherResolventParameter (3 / 4) tau‖ *
              (‖thetaEsscherResolventParameter (3 / 4) tau‖ + 1 / 4)) ≤
          ‖-(thetaEsscherResolventParameter (3 / 4) tau)⁻¹ - mu‖ := by
  have hpi : (1 / 2 : ℝ) < Real.pi / 4 := by
    nlinarith [Real.pi_gt_three]
  obtain ⟨C, hC, hmain⟩ := thetaExterior_pseudospectral_separation
    (h := (3 / 4 : ℝ)) (δ := (1 / 2 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) hpi
  refine ⟨C, hC, fun tau => ?_⟩
  obtain ⟨hnorm, hres, hsep⟩ := hmain tau
  let z := thetaEsscherResolventParameter (3 / 4) tau
  let ε := thetaExteriorConcretePseudospectralScale C tau
  have hz : z ≠ 0 := by
    apply thetaEsscherResolventParameter_ne_zero
    norm_num
  have hfactor : 0 < Real.exp (-(1 / 2) * |tau|) / ‖z‖ :=
    div_pos (Real.exp_pos _) (norm_pos_iff.mpr hz)
  have hCscale :
      C * (Real.exp (-(1 / 2) * |tau|) / ‖z‖) <
        2 * (|C| + 1) * (Real.exp (-(1 / 2) * |tau|) / ‖z‖) := by
    apply mul_lt_mul_of_pos_right _ hfactor
    nlinarith [le_abs_self C]
  have hstrict :
      ‖thetaKernelOperator.adjoint (thetaExteriorPseudomode (3 / 4) tau) -
          (starRingEnd ℂ) (-z⁻¹) • thetaExteriorPseudomode (3 / 4) tau‖ <
        (ε : ℝ) := by
    apply lt_of_le_of_lt hres
    simpa [z, ε, thetaExteriorConcretePseudospectralScale, div_eq_mul_inv,
      mul_assoc] using hCscale
  have hmemAdjoint :
      (starRingEnd ℂ) (-z⁻¹) ∈
        normResolventPseudospectrum ℂ ε thetaKernelOperator.adjoint :=
    mem_normResolventPseudospectrum_of_pseudomode ε
      thetaKernelOperator.adjoint ((starRingEnd ℂ) (-z⁻¹)) hnorm hstrict
  have hmemStar :
      star (-z⁻¹) ∈ normResolventPseudospectrum ℂ ε (star thetaKernelOperator) := by
    simpa only [ContinuousLinearMap.star_eq_adjoint, starRingEnd_apply] using hmemAdjoint
  constructor
  · change -z⁻¹ ∈ normResolventPseudospectrum ℂ ε thetaKernelOperator
    exact (star_mem_normResolventPseudospectrum_iff ε
      thetaKernelOperator (-z⁻¹)).mp hmemStar
  · norm_num [z, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4)] at hsep ⊢
    exact hsep

end

end RHTower.HedenmalmThetaSource
