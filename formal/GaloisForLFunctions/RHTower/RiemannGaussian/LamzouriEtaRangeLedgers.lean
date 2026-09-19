import GaloisForLFunctions.RHTower.RiemannGaussian.EtaEnergyFiniteWindowPairCorrelationSplit
import GaloisForLFunctions.RHTower.RiemannGaussian.EtaEnergyFiniteWindowReflectionCorrelation

/-!
# Lamzouri range ledgers for finite eta windows

Closed finite-window specializations of the multiplicity rank--trace inequality
at the two integer tangent parameters used by Lamzouri's range splitting.
Replacing a height by `max T 0` removes a sign premise without changing the
finite-window mechanism.
-/

namespace RiemannGaussian

open scoped BigOperators

/-- The `c = 2` multiplicity ledger at an arbitrary input height, interpreted
through the nonnegative clipped window. -/
theorem lamzouri_etaRangeTwo_ledger
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ) :
    4 *
          (pairedEtaTopPrefixFiniteZeroWindowOnLineTraceMass cutoff (max T 0) +
            pairedEtaTopPrefixFiniteZeroWindowOffLineTraceMass cutoff (max T 0)) -
        pairedEtaTopPrefixFiniteZeroWindowCoherentFrobeniusMass cutoff (max T 0) ≤
      pairedEtaTopPrefixFiniteZeroWindowCriticalMultiplicityPenalty
          cutoff (max T 0) 2 +
        4 * (spectralUpperZetaZeroWindow (max T 0)).card := by
  exact pairedEtaTopPrefixFiniteZeroWindow_multiplicityRankTrace_two_ledger
    cutoff (le_max_right T 0)

/-- The `c = 3` multiplicity ledger at an arbitrary input height.  This is the
second affine-square regime needed when one range is not sharp enough. -/
theorem lamzouri_etaRangeThree_ledger
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ) :
    6 *
          (pairedEtaTopPrefixFiniteZeroWindowOnLineTraceMass cutoff (max T 0) +
            pairedEtaTopPrefixFiniteZeroWindowOffLineTraceMass cutoff (max T 0)) -
        pairedEtaTopPrefixFiniteZeroWindowCoherentFrobeniusMass cutoff (max T 0) ≤
      pairedEtaTopPrefixFiniteZeroWindowCriticalMultiplicityPenalty
          cutoff (max T 0) 3 +
        9 * (spectralUpperZetaZeroWindow (max T 0)).card := by
  have h := pairedEtaTopPrefixFiniteZeroWindow_multiplicityRankTrace_ledger
    cutoff (le_max_right T 0) (c := 3) (by norm_num)
  norm_num at h ⊢
  exact h

/-- The `c = 2` ledger with coherent energy split into diagonal and signed
off-diagonal zero-pair correlation. -/
theorem lamzouri_etaRangeTwo_pairCorrelation_ledger
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ) :
    4 *
          (pairedEtaTopPrefixFiniteZeroWindowOnLineTraceMass cutoff (max T 0) +
            pairedEtaTopPrefixFiniteZeroWindowOffLineTraceMass cutoff (max T 0)) -
        pairedEtaTopPrefixFiniteZeroWindowDiagonalPairCorrelationMass cutoff (max T 0) -
        pairedEtaTopPrefixFiniteZeroWindowOffDiagonalPairCorrelationMass cutoff (max T 0) ≤
      pairedEtaTopPrefixFiniteZeroWindowCriticalMultiplicityPenalty
          cutoff (max T 0) 2 +
        4 * (spectralUpperZetaZeroWindow (max T 0)).card := by
  exact pairedEtaTopPrefixFiniteZeroWindow_multiplicityRankTrace_two_pairCorrelation_ledger
    cutoff (le_max_right T 0)

/-- The `c = 3` ledger with coherent energy split into diagonal and signed
off-diagonal zero-pair correlation. -/
theorem lamzouri_etaRangeThree_pairCorrelation_ledger
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ) :
    6 *
          (pairedEtaTopPrefixFiniteZeroWindowOnLineTraceMass cutoff (max T 0) +
            pairedEtaTopPrefixFiniteZeroWindowOffLineTraceMass cutoff (max T 0)) -
        pairedEtaTopPrefixFiniteZeroWindowDiagonalPairCorrelationMass cutoff (max T 0) -
        pairedEtaTopPrefixFiniteZeroWindowOffDiagonalPairCorrelationMass cutoff (max T 0) ≤
      pairedEtaTopPrefixFiniteZeroWindowCriticalMultiplicityPenalty
          cutoff (max T 0) 3 +
        9 * (spectralUpperZetaZeroWindow (max T 0)).card := by
  have h := lamzouri_etaRangeThree_ledger cutoff T
  rw [
    pairedEtaTopPrefixFiniteZeroWindowCoherentFrobeniusMass_eq_diagonal_add_offDiagonal]
    at h
  linarith

/-- The `c = 2` ledger after compressing the eta pair energy to one original
channel and its critical-line reflection. -/
theorem lamzouri_etaRangeTwo_reflectionCorrelation_ledger
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ) :
    4 *
          (pairedEtaTopPrefixFiniteZeroWindowOnLineTraceMass cutoff (max T 0) +
            pairedEtaTopPrefixFiniteZeroWindowOffLineTraceMass cutoff (max T 0)) -
        pairedEtaTopPrefixFiniteZeroWindowDiagonalReflectedOriginalMass cutoff (max T 0) -
        pairedEtaTopPrefixFiniteZeroWindowOffDiagonalReflectionCorrelationMass
          cutoff (max T 0) ≤
      pairedEtaTopPrefixFiniteZeroWindowCriticalMultiplicityPenalty
          cutoff (max T 0) 2 +
        4 * (spectralUpperZetaZeroWindow (max T 0)).card := by
  exact
    pairedEtaTopPrefixFiniteZeroWindow_multiplicityRankTrace_two_reflectionCorrelation_ledger
      cutoff (le_max_right T 0)

/-- The `c = 3` ledger in the original/reflected channel coordinates. -/
theorem lamzouri_etaRangeThree_reflectionCorrelation_ledger
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ) :
    6 *
          (pairedEtaTopPrefixFiniteZeroWindowOnLineTraceMass cutoff (max T 0) +
            pairedEtaTopPrefixFiniteZeroWindowOffLineTraceMass cutoff (max T 0)) -
        pairedEtaTopPrefixFiniteZeroWindowDiagonalReflectedOriginalMass cutoff (max T 0) -
        pairedEtaTopPrefixFiniteZeroWindowOffDiagonalReflectionCorrelationMass
          cutoff (max T 0) ≤
      pairedEtaTopPrefixFiniteZeroWindowCriticalMultiplicityPenalty
          cutoff (max T 0) 3 +
        9 * (spectralUpperZetaZeroWindow (max T 0)).card := by
  have h := lamzouri_etaRangeThree_ledger cutoff T
  rw [
    pairedEtaTopPrefixFiniteZeroWindowCoherentFrobeniusMass_eq_reflectedOriginalDiagonal_add_offDiagonal]
    at h
  linarith

end RiemannGaussian
