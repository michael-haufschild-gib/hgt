import GaloisForLFunctions.RHTower.CCM.CCMFirstClockCayleySourcePhaseOrientation
import GaloisForLFunctions.RHTower.CCM.CCMFirstClockBoundedExteriorPolarizationNoGo

/-!
# Orientation--capacity dichotomy for the first-clock Julia--Gamma current

The normalized Cayley source chart gives the calibrated rank-two Julia--Gamma exterior current
a global nonnegative Hermitian orientation.  It is unit-valued, so the universal bounded-
polarization estimate applies to the same current.  On the macroscopic first-clock prime blocks,
the resulting positive energy still cannot dominate the certified squared bad mass.

Thus the obstruction is not sign or phase wrapping.  Every bounded phase chart has insufficient
capacity.  Any surviving Route-J transport must leave the bounded-polarization class.
-/

open Finset
open scoped BigOperators

noncomputable section
namespace RHTower

/-- Cayley-oriented depth-zero Euler exterior energy on the first-clock macroscopic prime block. -/
def ccmFirstClockEulerDepthZeroCayleyExteriorEnergy
    (m : ℕ) (τ : ℝ) : ℂ :=
  ccmFirstClockEulerDepthZeroBoundedExteriorEnergy m
    (sourceCayleyPhase τ ccmFirstClockEulerDepthZeroExteriorHeight)

/-- The block energy is literally the universal Cayley exterior Hermitian energy. -/
theorem ccmFirstClockEulerDepthZeroCayleyExteriorEnergy_eq_source
    (m : ℕ) (τ : ℝ) :
    ccmFirstClockEulerDepthZeroCayleyExteriorEnergy m τ =
      sourceCayleyExteriorHermitianEnergy
        (suzukiMangoldtFivePrimeBlock (m ^ (4 : ℕ)))
        ccmFirstClockEulerDepthZeroExteriorAmplitude
        ccmFirstClockEulerDepthZeroExteriorHeight τ := by
  rfl

/-- Its real part is the explicit Cayley positive-square energy. -/
theorem ccmFirstClockEulerDepthZeroCayleyExteriorEnergy_re_eq
    (m : ℕ) (τ : ℝ) :
    (ccmFirstClockEulerDepthZeroCayleyExteriorEnergy m τ).re =
      sourceCayleyExteriorScalarEnergy
        (suzukiMangoldtFivePrimeBlock (m ^ (4 : ℕ)))
        ccmFirstClockEulerDepthZeroExteriorAmplitude
        ccmFirstClockEulerDepthZeroExteriorHeight τ := by
  rw [ccmFirstClockEulerDepthZeroCayleyExteriorEnergy_eq_source]
  exact sourceCayleyExteriorHermitianEnergy_re_eq _ _ _ _

/-- The Cayley chart gives a global nonnegative orientation on every first-clock block. -/
theorem ccmFirstClockEulerDepthZeroCayleyExteriorEnergy_re_nonneg
    (m : ℕ) {τ : ℝ} (hτ : 0 ≤ τ) :
    0 ≤ (ccmFirstClockEulerDepthZeroCayleyExteriorEnergy m τ).re := by
  rw [ccmFirstClockEulerDepthZeroCayleyExteriorEnergy_re_eq]
  exact sourceCayleyExteriorScalarEnergy_nonneg _ _ _ τ
    (fun p _ => ccmFirstClockEulerDepthZeroExteriorAmplitude_nonneg p) hτ

/-- Despite its global positive orientation, the unit Cayley chart cannot dominate the certified
first-clock bad-mass square beyond the explicit symbolic threshold. -/
theorem not_ccmFirstClock_badMass_sq_le_CayleyExteriorEnergy_re
    {m : ℕ} (hmLarge : Real.exp 7201 < (m : ℝ)) (τ : ℝ) :
    ¬ (∑ p ∈ suzukiMangoldtFivePrimeBlock (m ^ (4 : ℕ)),
        ccmFirstClockReducedBadNatTerm
          (ccmFirstClockJuliaSixthPowerAperture m) p) ^ (2 : ℕ) ≤
      (ccmFirstClockEulerDepthZeroCayleyExteriorEnergy m τ).re := by
  exact
    not_ccmFirstClock_badMass_sq_le_EulerDepthZeroBoundedExteriorEnergy_re
      hmLarge
      (sourceCayleyPhase τ ccmFirstClockEulerDepthZeroExteriorHeight)
      (fun p _ => by
        rw [norm_sourceCayleyPhase])

/-- **Orientation--capacity dichotomy.** The canonical Cayley source chart fixes sign globally,
but every such bounded chart remains quantitatively incapable of the Route-J domination step. -/
theorem ccmFirstClock_CayleyOrientationCapacity_dichotomy
    {m : ℕ} (hmLarge : Real.exp 7201 < (m : ℝ))
    {τ : ℝ} (hτ : 0 ≤ τ) :
    0 ≤ (ccmFirstClockEulerDepthZeroCayleyExteriorEnergy m τ).re ∧
      ¬ (∑ p ∈ suzukiMangoldtFivePrimeBlock (m ^ (4 : ℕ)),
          ccmFirstClockReducedBadNatTerm
            (ccmFirstClockJuliaSixthPowerAperture m) p) ^ (2 : ℕ) ≤
        (ccmFirstClockEulerDepthZeroCayleyExteriorEnergy m τ).re :=
  ⟨ccmFirstClockEulerDepthZeroCayleyExteriorEnergy_re_nonneg m hτ,
    not_ccmFirstClock_badMass_sq_le_CayleyExteriorEnergy_re hmLarge τ⟩

end RHTower
