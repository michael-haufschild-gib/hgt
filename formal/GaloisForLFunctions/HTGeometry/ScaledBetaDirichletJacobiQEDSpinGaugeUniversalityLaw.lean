import GaloisForLFunctions.HTGeometry.DimensionalQEDGammaGaugePartitionUniversalityLaw
import GaloisForLFunctions.HTGeometry.ScaledEulerBetaCrossDomainBoundary
import GaloisForLFunctions.HTGeometry.UnivMeroFieldInstances

/-!
# Scaled-beta/Dirichlet/Jacobi/QED spin-gauge universality

Binary Gauss multiplication and the unit Gamma shift put the constant-magnetic QED
spin-statistics ratio in the same nonzero differential-algebraic gauge class as the
unit-slope scaled Euler-beta carrier.  Existing cross-domain identifications then
place the symmetric Dirichlet normalizer and Jacobi/MANOVA-to-Gaussian quotient in
that class as well.
-/

open Filter Set Topology Function Complex
open scoped BigOperators Differential

namespace GaloisForLFunctions

open Bottcher Polynomial

noncomputable section

open scoped UnivMeroFieldInstances

/-- Explicit unit-shift times binary-Gauss gauge relating scaled beta to the QED spin ratio. -/
def scaledBetaQEDSpinGaugeMero : meroField Set.univ :=
  algebraMap (RatFunc ℂ) (meroField Set.univ) (gammaOrbitNatFactor 0 1) *
    gammaNatScaleGaussGaugeMero 2 0

theorem scaledBetaQEDSpinGaugeMero_ne_zero :
    scaledBetaQEDSpinGaugeMero ≠ 0 := by
  rw [scaledBetaQEDSpinGaugeMero]
  exact mul_ne_zero
    ((map_ne_zero_iff _
      (algebraMap (RatFunc ℂ) (meroField Set.univ)).injective).2
        (gammaOrbitNatFactor_ne_zero 0 1))
    (gammaNatScaleGaussGaugeMero_ne_zero (show 0 < 2 by norm_num) 0)

theorem differentialAlgebraicOver_scaledBetaQEDSpinGaugeMero :
    DifferentialAlgebraicOver (RatFunc ℂ) scaledBetaQEDSpinGaugeMero := by
  rw [scaledBetaQEDSpinGaugeMero]
  exact HTGeometry.differentialAlgebraicOver_mul
    (HTGeometry.differentialAlgebraicOver_algebraMap _)
    (differentialAlgebraicOver_gammaNatScaleGaussGaugeMero 2 0)

/-- The QED spin-statistics ratio is the explicit nonzero DA gauge times the unit-slope scaled
Euler-beta carrier. -/
theorem constantMagneticQEDSpinStatisticsRatioMero_eq_gauge_mul_scaledEulerBeta :
    constantMagneticQEDSpinStatisticsRatioMero =
      scaledBetaQEDSpinGaugeMero * scaledEulerBetaMero 1 1 := by
  have hgauss := gammaNatScaleMero_gauss
    (n := 2) (show 0 < 2 by norm_num) (0 : ℂ)
  change gammaNatScaleMero 2 0 =
      gammaNatScaleGaussGaugeMero 2 0 *
        gammaNatScaleGaussProductMero 2 0 at hgauss
  have hprod : gammaNatScaleGaussProductMero 2 0 =
      gammaShiftMero 0 * gammaShiftMero (1 / 2) := by
    norm_num [gammaNatScaleGaussProductMero, Finset.prod_range_succ]
  rw [hprod] at hgauss
  have hshift := gammaShiftMero_add_nat (0 : ℂ) 1
  norm_num at hshift
  have hmap :
      ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
          Set.univ_nonempty Set.infinite_univ (gammaOrbitNatFactor 0 1) =
        algebraMap (RatFunc ℂ) (meroField Set.univ)
          (gammaOrbitNatFactor 0 1) := rfl
  rw [hmap] at hshift
  rw [constantMagneticQEDSpinStatisticsRatioMero,
    constantMagneticSpinorQEDGammaCarrierMero,
    constantMagneticScalarQEDGammaCarrierMero,
    scaledBetaQEDSpinGaugeMero, scaledEulerBetaMero,
    gammaNatScaleMero_one, hshift, hgauss]
  field_simp [gammaShiftMero_ne_zero,
    gammaNatScaleGaussGaugeMero_ne_zero (show 0 < 2 by norm_num) 0,
    gammaOrbitNatFactor_ne_zero]

/-- **Scaled-beta/Dirichlet/Jacobi/QED spin-gauge law.** Four physical/statistical
representations occupy one nonzero hypertranscendental DA gauge class. -/
theorem scaledBetaDirichletJacobiQED_spinGaugeUniversality :
    constantMagneticQEDSpinStatisticsRatioMero =
        scaledBetaQEDSpinGaugeMero * scaledEulerBetaMero 1 1 ∧
      scaledEulerBetaMero 1 1 =
        (symmetricDirichletNormalizerMero 2)⁻¹ ∧
      jacobiMANOVAPartitionNormalizerMero 1 1 1 /
          gaussianBetaEnsemblePartitionNormalizerMero 1 =
        (symmetricDirichletNormalizerMero 2)⁻¹ ∧
      scaledBetaQEDSpinGaugeMero ≠ 0 ∧
      DifferentialAlgebraicOver (RatFunc ℂ) scaledBetaQEDSpinGaugeMero ∧
      HTGeometry.DifferentialAlgebraicGaugeEquivalent (F := RatFunc ℂ)
        constantMagneticQEDSpinStatisticsRatioMero (scaledEulerBetaMero 1 1) ∧
      HypertranscendentalOver (RatFunc ℂ)
        constantMagneticQEDSpinStatisticsRatioMero ∧
      HypertranscendentalOver (RatFunc ℂ) (scaledEulerBetaMero 1 1) := by
  refine ⟨constantMagneticQEDSpinStatisticsRatioMero_eq_gauge_mul_scaledEulerBeta,
    scaledEulerBetaMero_one_one_eq_inv_symmetricDirichlet,
    jacobiMANOVA_one_one_one_div_gaussian_eq_inv_symmetricDirichlet,
    scaledBetaQEDSpinGaugeMero_ne_zero,
    differentialAlgebraicOver_scaledBetaQEDSpinGaugeMero, ?_,
    hypertranscendentalOver_constantMagneticQEDSpinStatisticsRatioMero,
    hypertranscendentalOver_scaledEulerBetaMero (by norm_num) (by norm_num)⟩
  exact ⟨scaledBetaQEDSpinGaugeMero,
    scaledBetaQEDSpinGaugeMero_ne_zero,
    differentialAlgebraicOver_scaledBetaQEDSpinGaugeMero,
    constantMagneticQEDSpinStatisticsRatioMero_eq_gauge_mul_scaledEulerBeta⟩

end

end GaloisForLFunctions
