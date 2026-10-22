import GaloisForLFunctions.RHTower.CCM.CCMFirstClockBoundedExteriorPolarizationNoGo

/-!
# Minimum singularity of a first-clock exterior capacity

The bounded-polarization theorem says that unit-bounded exterior charts cannot dominate the
certified macroscopic bad mass.  This module quantifies the full obstruction.  If a polarization
is bounded by `B` on the first-clock prime block and its exterior energy does dominate the bad
mass, then `B²` must pay the logarithm of the physical block aperture.  Thus every successful
exterior transport has at least square-root-logarithmic multiplier blow-up.
-/

open Set Finset Filter Topology
open scoped BigOperators

noncomputable section
namespace RHTower

/-- Exterior energy with multiplier norm bounded by `B` has the same logarithmic ceiling as the
unit-bounded case, multiplied by `B²`. -/
theorem abs_re_ccmFirstClockEulerDepthZeroExteriorEnergy_le_of_norm_le
    {m : ℕ} (hm : 25 ≤ m) {B : ℝ} (hB : 0 ≤ B)
    (multiplier : ℕ → ℂ)
    (hmultiplier : ∀ p ∈ suzukiMangoldtFivePrimeBlock (m ^ (4 : ℕ)),
      ‖multiplier p‖ ≤ B) :
    |(ccmFirstClockEulerDepthZeroBoundedExteriorEnergy m multiplier).re| ≤
      B ^ (2 : ℕ) * ((25 / 2 : ℝ) * Real.log 4 ^ (2 : ℕ) *
        ((m ^ (4 : ℕ) : ℕ) : ℝ) / Real.log (2 * ((m ^ (4 : ℕ) : ℕ) : ℝ))) := by
  have hmOne : 1 ≤ m ^ (4 : ℕ) := one_le_pow₀ (by omega : 1 ≤ m)
  have hgeneric :=
    abs_re_boundedPolarizedExteriorHermitianEnergy_le
      (suzukiMangoldtFivePrimeBlock (m ^ (4 : ℕ)))
      ccmFirstClockEulerDepthZeroExteriorAmplitude
      ccmFirstClockEulerDepthZeroExteriorHeight multiplier B 1
      (fun p _ => ccmFirstClockEulerDepthZeroExteriorAmplitude_nonneg p)
      hB (by norm_num) hmultiplier
      (fun p hp q hq =>
        ccmFirstClockEulerDepthZeroExteriorHeight_diameter_le_one hm hp hq)
  have hsum :=
    sq_sum_ccmFirstClockEulerDepthZeroExteriorAmplitude_le hmOne
  calc
    |(ccmFirstClockEulerDepthZeroBoundedExteriorEnergy m multiplier).re|
        ≤ B ^ (2 : ℕ) * 1 *
          (∑ p ∈ suzukiMangoldtFivePrimeBlock (m ^ (4 : ℕ)),
            ccmFirstClockEulerDepthZeroExteriorAmplitude p) ^ (2 : ℕ) := hgeneric
    _ ≤ B ^ (2 : ℕ) * 1 * ((25 / 2 : ℝ) * Real.log 4 ^ (2 : ℕ) *
          ((m ^ (4 : ℕ) : ℕ) : ℝ) /
            Real.log (2 * ((m ^ (4 : ℕ) : ℕ) : ℝ))) := by
      exact mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = B ^ (2 : ℕ) * ((25 / 2 : ℝ) * Real.log 4 ^ (2 : ℕ) *
          ((m ^ (4 : ℕ) : ℕ) : ℝ) /
            Real.log (2 * ((m ^ (4 : ℕ) : ℕ) : ℝ))) := by ring

/-- **Exterior-capacity singularity law.**  Domination of the certified first-clock bad-mass
square forces the squared uniform multiplier bound to grow at least logarithmically in the
macroscopic block aperture. -/
theorem ccmFirstClock_exteriorCapacity_forces_log_multiplier_sq
    {m : ℕ} (hm : 25 ≤ m)
    (hmCheb : Real.exp 20 ≤ ((m ^ (4 : ℕ) : ℕ) : ℝ))
    {B : ℝ} (hB : 0 ≤ B) (multiplier : ℕ → ℂ)
    (hmultiplier : ∀ p ∈ suzukiMangoldtFivePrimeBlock (m ^ (4 : ℕ)),
      ‖multiplier p‖ ≤ B)
    (hdominates :
      (∑ p ∈ suzukiMangoldtFivePrimeBlock (m ^ (4 : ℕ)),
        ccmFirstClockReducedBadNatTerm
          (ccmFirstClockJuliaSixthPowerAperture m) p) ^ (2 : ℕ) ≤
        (ccmFirstClockEulerDepthZeroBoundedExteriorEnergy m multiplier).re) :
    Real.log (2 * ((m ^ (4 : ℕ) : ℕ) : ℝ)) ≤
      7200 * Real.log 4 ^ (2 : ℕ) * B ^ (2 : ℕ) := by
  have hmPos : 0 < m := by omega
  have hnPos : (0 : ℝ) < ((m ^ (4 : ℕ) : ℕ) : ℝ) := by positivity
  have hlogPos : 0 < Real.log (2 * ((m ^ (4 : ℕ) : ℕ) : ℝ)) := by
    exact Real.log_pos (by
      have hmOne : 1 ≤ m := by omega
      have hnOneNat : 1 ≤ m ^ (4 : ℕ) := one_le_pow₀ hmOne
      have hnOne : (1 : ℝ) ≤ ((m ^ (4 : ℕ) : ℕ) : ℝ) := by
        exact_mod_cast hnOneNat
      nlinarith)
  have hbadMass :=
    ccmFirstClockJuliaSixthPower_block_badMass_lower hm hmCheb
  have hbadNonneg :
      0 ≤ ∑ p ∈ suzukiMangoldtFivePrimeBlock (m ^ (4 : ℕ)),
        ccmFirstClockReducedBadNatTerm
          (ccmFirstClockJuliaSixthPowerAperture m) p := by
    apply Finset.sum_nonneg
    intro p hp
    have hpPrime := (mem_suzukiMangoldtFivePrimeBlock.mp hp).1
    rw [ccmFirstClockReducedBadNatTerm_of_prime _ hpPrime]
    exact (ccmFirstClockJuliaSixthPower_block_badTerm_pos hm hp).le
  have hbadSq :
      ((m ^ (4 : ℕ) : ℕ) : ℝ) / 576 ≤
        (∑ p ∈ suzukiMangoldtFivePrimeBlock (m ^ (4 : ℕ)),
          ccmFirstClockReducedBadNatTerm
            (ccmFirstClockJuliaSixthPowerAperture m) p) ^ (2 : ℕ) := by
    have hmassSq :=
      (sq_le_sq₀ (by positivity : 0 ≤ (m : ℝ) ^ (2 : ℕ) / 24) hbadNonneg).2 hbadMass
    push_cast at hmassSq ⊢
    nlinarith
  have henergy :=
    abs_re_ccmFirstClockEulerDepthZeroExteriorEnergy_le_of_norm_le
      hm hB multiplier hmultiplier
  have hchain :
      ((m ^ (4 : ℕ) : ℕ) : ℝ) / 576 ≤
        B ^ (2 : ℕ) * ((25 / 2 : ℝ) * Real.log 4 ^ (2 : ℕ) *
          ((m ^ (4 : ℕ) : ℕ) : ℝ) /
            Real.log (2 * ((m ^ (4 : ℕ) : ℕ) : ℝ))) :=
    hbadSq.trans (hdominates.trans ((le_abs_self _).trans henergy))
  have hchain' :
      ((m ^ (4 : ℕ) : ℕ) : ℝ) / 576 ≤
        (B ^ (2 : ℕ) * ((25 / 2 : ℝ) * Real.log 4 ^ (2 : ℕ)) *
          ((m ^ (4 : ℕ) : ℕ) : ℝ)) /
            Real.log (2 * ((m ^ (4 : ℕ) : ℕ) : ℝ)) := by
    calc
      ((m ^ (4 : ℕ) : ℕ) : ℝ) / 576 ≤
          B ^ (2 : ℕ) * ((25 / 2 : ℝ) * Real.log 4 ^ (2 : ℕ) *
            ((m ^ (4 : ℕ) : ℕ) : ℝ) /
              Real.log (2 * ((m ^ (4 : ℕ) : ℕ) : ℝ))) := hchain
      _ = (B ^ (2 : ℕ) * ((25 / 2 : ℝ) * Real.log 4 ^ (2 : ℕ)) *
            ((m ^ (4 : ℕ) : ℕ) : ℝ)) /
              Real.log (2 * ((m ^ (4 : ℕ) : ℕ) : ℝ)) := by ring
  have hcross := (le_div_iff₀ hlogPos).1 hchain'
  have hcancel :
      Real.log (2 * ((m ^ (4 : ℕ) : ℕ) : ℝ)) / 576 ≤
        B ^ (2 : ℕ) * ((25 / 2 : ℝ) * Real.log 4 ^ (2 : ℕ)) := by
    have hmul :
        ((m ^ (4 : ℕ) : ℕ) : ℝ) *
            (Real.log (2 * ((m ^ (4 : ℕ) : ℕ) : ℝ)) / 576) ≤
          ((m ^ (4 : ℕ) : ℕ) : ℝ) *
            (B ^ (2 : ℕ) * ((25 / 2 : ℝ) * Real.log 4 ^ (2 : ℕ))) := by
      calc
        ((m ^ (4 : ℕ) : ℕ) : ℝ) *
            (Real.log (2 * ((m ^ (4 : ℕ) : ℕ) : ℝ)) / 576) =
          ((m ^ (4 : ℕ) : ℕ) : ℝ) / 576 *
            Real.log (2 * ((m ^ (4 : ℕ) : ℕ) : ℝ)) := by ring
        _ ≤ B ^ (2 : ℕ) * ((25 / 2 : ℝ) * Real.log 4 ^ (2 : ℕ)) *
            ((m ^ (4 : ℕ) : ℕ) : ℝ) := hcross
        _ = ((m ^ (4 : ℕ) : ℕ) : ℝ) *
            (B ^ (2 : ℕ) * ((25 / 2 : ℝ) * Real.log 4 ^ (2 : ℕ))) := by ring
    exact le_of_mul_le_mul_left hmul hnPos
  nlinarith

end RHTower
