import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaCompactFluxEnergy
import GaloisForLFunctions.RHTower.XiSourceBoundaryOrientationConservation

/-!
# Theta compact boundary flux as signed arithmetic source entropy

This module preserves the sign discarded by the previously squared RH energies.  On every
multiplicity-exact Xi divisor copy, the boundary quadratic form of the genuine eigenvector of the
fixed compact theta source inverse is exactly the reflected prime-two source entropy, multiplied
by the strictly positive theta mass and root energy.  Consequently, simultaneous boundary
neutrality of the actual compact eigenvectors is equivalent to RH.
-/

open Complex
open scoped BigOperators

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry
open HedenmalmThetaSource

/-- Reflected prime-source entropy is twice the transverse coordinate of the centered Xi
spectral point.  Unlike the energy identities, this retains orientation. -/
theorem riemannReflectedSourceEntropy_xiZeroCopy_eq_two_spectralIm
    (q : XiZeroCopy) :
    riemannReflectedSourceEntropy (q.1 : ℂ) =
      2 * (xiSpectralPoint q).im := by
  rw [riemannReflectedSourceEntropy_eq_neg_sourceCayleyRate,
    xiSpectralPoint_im_eq]
  simp only [sourceCayleyTransverseRate, sub_re, one_re]
  ring

/-- **Signed compact/source weld.**  The arithmetic source entropy is exactly the normalized
rank-two boundary flux of the genuine compact theta divisor eigenvector. -/
theorem thetaXiRankTwoBoundaryFlux_eq_sourceEntropy (q : XiZeroCopy) :
    thetaXiRankTwoBoundaryFlux q =
      thetaSource.mass * thetaXiRootEnergy q *
        riemannReflectedSourceEntropy (q.1 : ℂ) := by
  rw [thetaXiRankTwoBoundaryFlux_eq,
    riemannReflectedSourceEntropy_xiZeroCopy_eq_two_spectralIm]
  ring

/-- Strict positivity of the theta mass and root energy makes the signed weld faithful before
squaring. -/
theorem thetaXiRankTwoBoundaryFlux_eq_zero_iff_sourceEntropy_eq_zero
    (q : XiZeroCopy) :
    thetaXiRankTwoBoundaryFlux q = 0 ↔
      riemannReflectedSourceEntropy (q.1 : ℂ) = 0 := by
  rw [thetaXiRankTwoBoundaryFlux_eq_sourceEntropy]
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left
      (mul_ne_zero thetaSource.mass_ne_zero (thetaXiRootEnergy_pos q).ne')
  · intro h
    rw [h, mul_zero]

/-- The actual compact-eigenvector boundary flux vanishes precisely when its centered spectral
eigenvalue is real. -/
theorem thetaXiRankTwoBoundaryFlux_eq_zero_iff_spectralIm_eq_zero
    (q : XiZeroCopy) :
    thetaXiRankTwoBoundaryFlux q = 0 ↔
      (xiSpectralPoint q).im = 0 := by
  rw [thetaXiRankTwoBoundaryFlux_eq_zero_iff_sourceEntropy_eq_zero,
    riemannReflectedSourceEntropy_xiZeroCopy_eq_two_spectralIm]
  constructor
  · intro h
    linarith
  · intro h
    rw [h, mul_zero]

/-- The normalized square of the compact boundary flux is the established source-entropy
density, pointwise and with divisor multiplicity retained. -/
theorem thetaXiNormalizedRankTwoBoundaryFluxTerm_eq_sourceEntropyDensity
    (q : XiZeroCopy) :
    thetaXiNormalizedRankTwoBoundaryFluxTerm q =
      riemannReflectedSourceEntropy (q.1 : ℂ) ^ (2 : ℕ) *
          (q.1 : ℂ).im ^ (2 : ℕ) /
        (((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) +
          (q.1 : ℂ).im ^ (2 : ℕ)) ^ (4 : ℕ) := by
  rw [thetaXiNormalizedRankTwoBoundaryFluxTerm_eq,
    xiZeroCopyThermalOrientationTerm_eq_sourceEntropyDensity]

/-- Global normalized compact boundary energy equals global arithmetic source-entropy energy. -/
theorem thetaXiNormalizedRankTwoBoundaryFluxEnergy_eq_sourceEntropyOrientationEnergy :
    thetaXiNormalizedRankTwoBoundaryFluxEnergy =
      xiSourceEntropyOrientationEnergy := by
  calc
    thetaXiNormalizedRankTwoBoundaryFluxEnergy =
        xiThermalOrientationEnergy :=
      thetaXiNormalizedRankTwoBoundaryFluxEnergy_eq_thermalOrientationEnergy
    _ = xiSourceEntropyOrientationEnergy :=
      xiSourceEntropyOrientationEnergy_eq_thermalOrientationEnergy.symm

/-- **Unsquared compact-boundary RH criterion.**  RH is equivalent to simultaneous neutrality of
the rank-two boundary form on every genuine eigenvector of the fixed compact theta source inverse.
No abstract eigenvector premise and no loss of sign remain. -/
theorem all_thetaXiRankTwoBoundaryFlux_eq_zero_iff_riemannHypothesis :
    (∀ q : XiZeroCopy, thetaXiRankTwoBoundaryFlux q = 0) ↔
      RiemannHypothesis := by
  constructor
  · intro hflux
    apply riemannHypothesis_of_xiSpectralPoint_real
    intro q
    have him : (xiSpectralPoint q).im = 0 :=
      (thetaXiRankTwoBoundaryFlux_eq_zero_iff_spectralIm_eq_zero q).mp
        (hflux q)
    refine ⟨(xiSpectralPoint q).re, Complex.ext ?_ ?_⟩
    · simp
    · simpa using him
  · intro hRH q
    apply (thetaXiRankTwoBoundaryFlux_eq_zero_iff_spectralIm_eq_zero q).mpr
    obtain ⟨t, ht⟩ := xiSpectralPoint_real_of_rh hRH q
    rw [ht]
    simp

/-- The same Frankenstein weld at global energy level: zero compact boundary energy, zero source
entropy energy, and RH are one statement. -/
theorem thetaXiNormalizedRankTwoBoundaryFluxEnergy_eq_zero_iff_sourceEntropy_and_rh :
    thetaXiNormalizedRankTwoBoundaryFluxEnergy = 0 ↔
      xiSourceEntropyOrientationEnergy = 0 ∧ RiemannHypothesis := by
  rw [thetaXiNormalizedRankTwoBoundaryFluxEnergy_eq_sourceEntropyOrientationEnergy,
    xiSourceEntropyOrientationEnergy_eq_thermalOrientationEnergy,
    xiThermalOrientationEnergy_eq_zero_iff_rh]
  exact ⟨fun h => ⟨h, h⟩, fun h => h.1⟩

end

end RHTower
