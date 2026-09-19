import GaloisForLFunctions.RHTower.RiemannGaussian.Hybrid.EtaSignedHeatCertificate
import GaloisForLFunctions.RHTower.RiemannGaussian.Hybrid.EtaSpectralHeatArithmeticBridge

/-!
# Lamzouri multiplicity energy in signed-heat coordinates

The finite eta matrix underlying the multiplicity rank--trace method also
admits an exact continuous signed-heat representation.  These closed,
clipped-height statements expose both descriptions without a height premise.
-/

namespace RiemannGaussian

open Filter MeasureTheory Set
open scoped Topology

/-- The signature of the finite eta zero-window matrix is its normalized
signed-heat current integral. -/
theorem lamzouri_etaSignedHeat_signature
    {d : Type*} [Fintype d] [DecidableEq d]
    (cutoff : d → ℕ) (T : ℝ) :
    (1 / Real.sqrt Real.pi) *
          ∫ u : ℝ in Set.Ioi 0,
            u ^ (-(1 / 2 : ℝ)) *
              pairedEtaTopPrefixFiniteZeroWindowSignedSpectralHeatCurrent
                cutoff (le_max_right T 0) u =
      (HermitianRankTrace.posIndex
          (pairedEtaTopPrefixFiniteZeroWindowBlock_isHermitian
            cutoff (le_max_right T 0)) : ℝ) -
        (HermitianRankTrace.negIndex
          (pairedEtaTopPrefixFiniteZeroWindowBlock_isHermitian
            cutoff (le_max_right T 0)) : ℝ) := by
  exact pairedEtaTopPrefixFiniteZeroWindowSignature_eq_signedHeatIntegral
    cutoff (le_max_right T 0)

/-- Positive inertia, hence the finite rank cost in Lamzouri-style ledgers,
is reconstructed exactly from nullity and signed heat current. -/
theorem lamzouri_etaSignedHeat_posIndex
    {d : Type*} [Fintype d] [DecidableEq d]
    (cutoff : d → ℕ) (T : ℝ) :
    (HermitianRankTrace.posIndex
        (pairedEtaTopPrefixFiniteZeroWindowBlock_isHermitian
          cutoff (le_max_right T 0)) : ℝ) =
      (1 / 2 : ℝ) *
        ((Fintype.card (d × Fin 2) : ℝ) -
          (pairedEtaTopPrefixFiniteZeroWindowZeroIndex
            cutoff (le_max_right T 0) : ℝ) +
          (1 / Real.sqrt Real.pi) *
            ∫ u : ℝ in Set.Ioi 0,
              u ^ (-(1 / 2 : ℝ)) *
                pairedEtaTopPrefixFiniteZeroWindowSignedSpectralHeatCurrent
                  cutoff (le_max_right T 0) u) := by
  exact pairedEtaTopPrefixFiniteZeroWindowPosIndex_eq_signedHeat
    cutoff (le_max_right T 0)

/-- The continuous signed-heat certificate is bounded by the represented
critical-line and upper off-line zero counts. -/
theorem lamzouri_etaSignedHeat_le_critical_add_upper
    {d : Type*} [Fintype d] [DecidableEq d]
    (cutoff : d → ℕ) (T : ℝ) :
    (1 / 2 : ℝ) *
          ((Fintype.card (d × Fin 2) : ℝ) -
            (pairedEtaTopPrefixFiniteZeroWindowZeroIndex
              cutoff (le_max_right T 0) : ℝ) +
            (1 / Real.sqrt Real.pi) *
              ∫ u : ℝ in Set.Ioi 0,
                u ^ (-(1 / 2 : ℝ)) *
                  pairedEtaTopPrefixFiniteZeroWindowSignedSpectralHeatCurrent
                    cutoff (le_max_right T 0) u) ≤
      ((spectralCriticalZetaZeroWindow (max T 0)).card +
        (spectralUpperZetaZeroWindow (max T 0)).card : ℕ) := by
  exact
    pairedEtaTopPrefixFiniteZeroWindowSignedHeatCertificate_le_critical_add_upper
      cutoff (le_max_right T 0)

/-- Initial order-two eta heat moment equals diagonal arithmetic mass plus
signed off-diagonal arithmetic correlation. -/
theorem lamzouri_etaHeatMoment_two_zero_eq_arithmetic
    {d : Type*} [Fintype d] [DecidableEq d]
    (cutoff : d → ℕ) (T : ℝ) :
    pairedEtaTopPrefixFiniteZeroWindowSpectralHeatMomentTrace
        cutoff (le_max_right T 0) 2 0 =
      pairedEtaTopPrefixFiniteZeroWindowDiagonalWeightedArithmeticMass
          cutoff (max T 0) +
        pairedEtaTopPrefixFiniteZeroWindowOffDiagonalWeightedArithmeticMass
          cutoff (max T 0) := by
  exact pairedEtaTopPrefixFiniteZeroWindowSpectralHeatMomentTrace_two_zero_eq_arithmetic
    cutoff (le_max_right T 0)

/-- The heat trace derivative at zero is the negative of the exact finite
diagonal-plus-off-diagonal arithmetic correlation. -/
theorem lamzouri_etaHeatTrace_hasDerivAt_zero_arithmetic
    {d : Type*} [Fintype d] [DecidableEq d]
    (cutoff : d → ℕ) (T : ℝ) :
    HasDerivAt
      (pairedEtaTopPrefixFiniteZeroWindowSpectralHeatMomentTrace
        cutoff (le_max_right T 0) 0)
      (-(pairedEtaTopPrefixFiniteZeroWindowDiagonalWeightedArithmeticMass
            cutoff (max T 0) +
          pairedEtaTopPrefixFiniteZeroWindowOffDiagonalWeightedArithmeticMass
            cutoff (max T 0))) 0 := by
  exact
    hasDerivAt_pairedEtaTopPrefixFiniteZeroWindowSpectralHeatTrace_at_zero_arithmetic
      cutoff (le_max_right T 0)

end RiemannGaussian
