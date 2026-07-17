import GaloisForLFunctions.HTGeometry.JacobiMANOVANormalizerBoundary

/-!
# Scaled Euler beta cross-domain boundary

At unit slopes, the two-slope Euler beta carrier is exactly the reciprocal binary symmetric
Dirichlet normalizer:

`B(z,z) = Gamma(z)^2 / Gamma(2*z) = D_2(z)^(-1)`.

Together with the one-channel Jacobi/MANOVA identity, this is one meromorphic value shared by a
quantum-transport observation law, a Veneziano/open-string beta amplitude, and a binary
AI/genomic Dirichlet normalization.  Multiplying it by the two-eigenangle circular beta-ensemble
normalizer cancels every Gamma factor and leaves the already identified rational gauge.
-/

open Filter Set Topology Function Complex
open scoped BigOperators Differential

namespace GaloisForLFunctions

open Bottcher Polynomial

noncomputable section

local instance scaledEulerBetaCrossDomain :
    IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty

local instance scaledEulerBetaCrossDifferential :
    Differential (meroField Set.univ) :=
  meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty

local instance scaledEulerBetaCrossRatFuncAlgebra :
    Algebra (RatFunc ℂ) (meroField Set.univ) :=
  (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
    Set.univ_nonempty Set.infinite_univ).toAlgebra

local instance scaledEulerBetaCrossRatFuncDifferential :
    Differential (RatFunc ℂ) := ratFuncCoordinateDifferential

local instance scaledEulerBetaCrossDifferentialAlgebra :
    DifferentialAlgebra (RatFunc ℂ) (meroField Set.univ) :=
  { deriv_algebraMap := fun r => meroField_deriv_ratfuncToMero r }

local instance scaledEulerBetaCrossCharZero : CharZero (meroField Set.univ) :=
  charZero_of_injective_algebraMap
    (algebraMap (RatFunc ℂ) (meroField Set.univ)).injective

/-- **Scaled-beta/Dirichlet value relation.**  The unit-slope Euler beta amplitude is exactly the
reciprocal binary symmetric-Dirichlet normalizer. -/
theorem scaledEulerBetaMero_one_one_eq_inv_symmetricDirichlet :
    scaledEulerBetaMero 1 1 =
      (symmetricDirichletNormalizerMero 2)⁻¹ := by
  rw [scaledEulerBetaMero, symmetricDirichletNormalizerMero,
    gammaNatScaleMero_one]
  norm_num
  field_simp [gammaShiftMero_ne_zero 0,
    gammaNatScaleMero_ne_zero (show 0 < 2 by norm_num) 0]

/-- **Transport/AI-genomics value relation.**  The symmetric one-channel Jacobi/Gaussian
quotient is the reciprocal binary Dirichlet normalizer. -/
theorem jacobiMANOVA_one_one_one_div_gaussian_eq_inv_symmetricDirichlet :
    jacobiMANOVAPartitionNormalizerMero 1 1 1 /
        gaussianBetaEnsemblePartitionNormalizerMero 1 =
      (symmetricDirichletNormalizerMero 2)⁻¹ := by
  rw [jacobiMANOVAPartitionNormalizer_one_div_gaussian_eq_scaledEulerBeta,
    scaledEulerBetaMero_one_one_eq_inv_symmetricDirichlet]

private theorem symmetricDirichletNormalizerMero_two_ne_zero :
    symmetricDirichletNormalizerMero 2 ≠ 0 := by
  rw [symmetricDirichletNormalizerMero]
  exact div_ne_zero
    (gammaNatScaleMero_ne_zero (show 0 < 2 by norm_num) 0)
    (pow_ne_zero 2 (gammaShiftMero_ne_zero 0))

/-- **Circular/Jacobi/Dirichlet cancellation law.**  Multiplying the two-eigenangle circular
beta-ensemble normalizer by the unit-slope one-channel Jacobi/Gaussian quotient removes every
Gamma factor and leaves exactly the rational Dirichlet gauge. -/
theorem circularBeta_two_mul_jacobiMANOVA_one_one_one_div_gaussian_eq_gauge :
    circularBetaEnsemblePartitionNormalizerMero 2 *
        (jacobiMANOVAPartitionNormalizerMero 1 1 1 /
          gaussianBetaEnsemblePartitionNormalizerMero 1) =
      algebraMap (RatFunc ℂ) (meroField Set.univ)
        (circularBetaDirichletGaugeRat 2) := by
  rw [circularBetaEnsemblePartitionNormalizerMero_eq_dirichlet
      (K := 2) (by norm_num),
    jacobiMANOVA_one_one_one_div_gaussian_eq_inv_symmetricDirichlet,
    mul_assoc, mul_inv_cancel₀ symmetricDirichletNormalizerMero_two_ne_zero,
    mul_one]

/-- The three-domain quotient above is differentially algebraic despite each nontrivial Gamma
carrier being hypertranscendental. -/
theorem differentialAlgebraicOver_circularBeta_two_mul_jacobiMANOVA_div_gaussian :
    DifferentialAlgebraicOver (RatFunc ℂ)
      (circularBetaEnsemblePartitionNormalizerMero 2 *
        (jacobiMANOVAPartitionNormalizerMero 1 1 1 /
          gaussianBetaEnsemblePartitionNormalizerMero 1)) := by
  rw [circularBeta_two_mul_jacobiMANOVA_one_one_one_div_gaussian_eq_gauge]
  exact HTGeometry.differentialAlgebraicOver_algebraMap _

end

end GaloisForLFunctions
