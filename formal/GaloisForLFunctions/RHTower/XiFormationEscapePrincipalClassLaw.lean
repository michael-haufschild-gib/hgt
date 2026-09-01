import GaloisForLFunctions.RHTower.XiGammaSixFilteredBoundaryHarmonicResidue
import GaloisForLFunctions.RHTower.MobiusThetaAdaptiveGreenDoubleLogResidueWeld
import GaloisForLFunctions.RHTower.HedenmalmThetaKakutaniBalancedIndexNoGo

/-!
# Quantized modular-formation escape: four-organ reconstruction

This module identifies one reflection-even principal escape class across four
structurally different organs already present in the corpus:

* filtered Gamma-six boundary jets;
* Möbius prime-normal double-log energy;
* adaptive resolved Green codiagonals;
* reflected Kakutani/Hellinger polarization.

The class is the support of centered modular charge.  These theorems reconstruct
that class; they do not prove that it vanishes for every Xi-zero copy.
-/

open Complex Filter
open scoped BigOperators Topology

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry
open HedenmalmThetaSource
open DeningerMeyerGaussianGreen

/-- The theta boundary flux and centered modular rate have the same zero locus. -/
theorem thetaXiRankTwoBoundaryFlux_eq_zero_iff_centeredRate_eq_zero
    (q : XiZeroCopy) :
    thetaXiRankTwoBoundaryFlux q = 0 ↔
      primeDepthBVWoldXiCenteredRate q.1 = 0 := by
  rw [thetaXiRankTwoBoundaryFlux_eq_neg_massEnergy_mul_centeredRate]
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left
      (neg_ne_zero.mpr
        (mul_ne_zero thetaSource.mass_ne_zero
          (thetaXiRootEnergy_pos q).ne'))
  · intro h
    rw [h, mul_zero]

/-- The common escape index vanishes exactly at neutral modular rate. -/
theorem thetaKakutaniHarmonicEscapeIndex_eq_zero_iff_centeredRate_eq_zero
    (q : XiZeroCopy) :
    thetaKakutaniHarmonicEscapeIndex q = 0 ↔
      primeDepthBVWoldXiCenteredRate q.1 = 0 := by
  rw [← thetaXiRankTwoBoundaryFlux_eq_zero_iff_centeredRate_eq_zero]
  by_cases hflux : thetaXiRankTwoBoundaryFlux q = 0 <;>
    simp [thetaKakutaniHarmonicEscapeIndex, hflux]

/-- Gamma-six harmonic residue is the common escape index times its depth scale. -/
theorem gammaSixFilteredBoundaryAsymptoticResidue_eq_escapeIndex
    (m : ℕ) (q : XiZeroCopy) :
    gammaSixFilteredBoundaryAsymptoticResidue m
        (primeDepthBVWoldXiCenteredRate q.1) =
      (Real.log 2 / (m : ℝ) ^ 2) *
        thetaKakutaniHarmonicEscapeIndex q := by
  by_cases hrate : primeDepthBVWoldXiCenteredRate q.1 = 0
  · have hflux : thetaXiRankTwoBoundaryFlux q = 0 :=
      (thetaXiRankTwoBoundaryFlux_eq_zero_iff_centeredRate_eq_zero q).2 hrate
    simp [gammaSixFilteredBoundaryAsymptoticResidue, hrate,
      thetaKakutaniHarmonicEscapeIndex, hflux]
  · have hflux : thetaXiRankTwoBoundaryFlux q ≠ 0 := by
      intro hzero
      exact hrate
        ((thetaXiRankTwoBoundaryFlux_eq_zero_iff_centeredRate_eq_zero q).1 hzero)
    simp [gammaSixFilteredBoundaryAsymptoticResidue, hrate,
      thetaKakutaniHarmonicEscapeIndex, hflux]

/-- The literal Gamma-six boundary jet reconstructs the common escape index at prime infinity. -/
theorem tendsto_gammaSixFilteredBoundarySecondJet_harmonic_residue_escapeIndex
    {m : ℕ} (hm : 1 ≤ m) (q : XiZeroCopy) :
    Tendsto (fun n : ℕ =>
      ((gammaSixFilteredBoundaryNthPrime n).1 : ℝ) *
        gammaSixFilteredBoundarySecondJet m q
          (gammaSixFilteredBoundaryNthPrime n)) atTop
      (nhds ((Real.log 2 / (m : ℝ) ^ 2) *
        thetaKakutaniHarmonicEscapeIndex q)) := by
  simpa [gammaSixFilteredBoundaryAsymptoticResidue_eq_escapeIndex m q] using
    tendsto_gammaSixFilteredBoundarySecondJet_harmonic_residue hm q

/-- Möbius prime-normal double-log energy reconstructs the same escape index. -/
theorem tendsto_thetaMobiusPrimeNormalHalfDensityEnergyPrefix_div_logLog_escapeIndex
    (q : XiZeroCopy) :
    Tendsto (fun N : ℕ =>
      thetaMobiusPrimeNormalHalfDensityEnergyPrefix q N /
        Real.log (Real.log (N : ℝ))) atTop
      (nhds (thetaKakutaniHarmonicEscapeIndex q)) := by
  by_cases hflux : thetaXiRankTwoBoundaryFlux q = 0
  · simpa [thetaKakutaniHarmonicEscapeIndex, hflux] using
      tendsto_thetaMobiusPrimeNormalHalfDensityEnergyPrefix_div_logLog_zero_of_boundaryFlux_zero
        q hflux
  · simpa [thetaKakutaniHarmonicEscapeIndex, hflux] using
      tendsto_thetaMobiusPrimeNormalHalfDensityEnergyPrefix_div_logLog_one_of_boundaryFlux_ne_zero
        q hflux

/-- The resolved Green codiagonal vanishes exactly when the common escape class vanishes. -/
theorem adaptivePrimeNormalActualGreenCodiagonal_eq_zero_iff_escapeIndex_zero
    (p : Nat.Primes) (q : XiZeroCopy) :
    resolvedDefectCodiagonal (R := ℂ)
        (adaptivePrimeNormalActualGreenResolvedLineComparison p q) = 0 ↔
      thetaKakutaniHarmonicEscapeIndex q = 0 := by
  rw [adaptivePrimeNormalActualGreenResolvedLineComparison_codiagonal_eq_zero_iff,
    thetaKakutaniHarmonicEscapeIndex_eq_zero_iff_centeredRate_eq_zero,
    primeDepthBVWoldXiCenteredRate_eq_zero_iff]

/-- Reflection cancels oriented charge but doubles the common unsigned escape class. -/
theorem tendsto_reflectionPairKakutaniFluxPolarization_div_primeReciprocalMass_escapeIndex
    (q : XiZeroCopy) :
    Tendsto
      (fun s : Finset Nat.Primes =>
        (∑ p ∈ s,
          (thetaKakutaniFluxPositiveUnit p q * thetaXiRankTwoBoundaryFlux q ^ 2 +
            thetaKakutaniFluxPositiveUnit p (xiZeroCopyReflectEquiv q) *
              thetaXiRankTwoBoundaryFlux (xiZeroCopyReflectEquiv q) ^ 2)) /
            primeReciprocalMass s)
      atTop (nhds (2 * thetaKakutaniHarmonicEscapeIndex q)) := by
  by_cases hflux : thetaXiRankTwoBoundaryFlux q = 0
  · have hreflect :
        thetaXiRankTwoBoundaryFlux (xiZeroCopyReflectEquiv q) = 0 := by
      rw [thetaXiRankTwoBoundaryFlux_reflect, hflux, neg_zero]
    simp [hflux, hreflect, thetaKakutaniHarmonicEscapeIndex]
  · simpa [thetaKakutaniHarmonicEscapeIndex, hflux] using
      tendsto_reflectionPairKakutaniFluxPolarization_div_primeReciprocalMass q hflux

/-- Four-organ reconstruction of one singular modular formation class. -/
theorem xiFormationEscapePrincipalClass_fourOrganLaw
    {m : ℕ} (hm : 1 ≤ m) (p : Nat.Primes) (q : XiZeroCopy) :
    Tendsto (fun n : ℕ =>
        ((gammaSixFilteredBoundaryNthPrime n).1 : ℝ) *
          gammaSixFilteredBoundarySecondJet m q
            (gammaSixFilteredBoundaryNthPrime n)) atTop
        (nhds ((Real.log 2 / (m : ℝ) ^ 2) *
          thetaKakutaniHarmonicEscapeIndex q)) ∧
    Tendsto (fun N : ℕ =>
        thetaMobiusPrimeNormalHalfDensityEnergyPrefix q N /
          Real.log (Real.log (N : ℝ))) atTop
        (nhds (thetaKakutaniHarmonicEscapeIndex q)) ∧
    (resolvedDefectCodiagonal (R := ℂ)
          (adaptivePrimeNormalActualGreenResolvedLineComparison p q) = 0 ↔
        thetaKakutaniHarmonicEscapeIndex q = 0) ∧
    Tendsto
      (fun s : Finset Nat.Primes =>
        (∑ ell ∈ s,
          (thetaKakutaniFluxPositiveUnit ell q * thetaXiRankTwoBoundaryFlux q ^ 2 +
            thetaKakutaniFluxPositiveUnit ell (xiZeroCopyReflectEquiv q) *
              thetaXiRankTwoBoundaryFlux (xiZeroCopyReflectEquiv q) ^ 2)) /
            primeReciprocalMass s)
      atTop (nhds (2 * thetaKakutaniHarmonicEscapeIndex q)) := by
  exact ⟨tendsto_gammaSixFilteredBoundarySecondJet_harmonic_residue_escapeIndex hm q,
    tendsto_thetaMobiusPrimeNormalHalfDensityEnergyPrefix_div_logLog_escapeIndex q,
    adaptivePrimeNormalActualGreenCodiagonal_eq_zero_iff_escapeIndex_zero p q,
    tendsto_reflectionPairKakutaniFluxPolarization_div_primeReciprocalMass_escapeIndex q⟩

end

end RHTower
