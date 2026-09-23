import GaloisForLFunctions.RHTower.CCMFirstClockJuliaPrincipalRelativeNoGo

/-!
# Quadratic divergence of the literal reduced bad first-clock residual

At source-faithful apertures `L_m = 6 log m`, every prime in the macroscopic block
`(2m^(4 : ℕ), 5m^(4 : ℕ)]` is an admitted one-mode outer prime in the negative first-clock sine chamber.
The existing Chebyshev block estimate gives this block total bad mass at least `m^(2 : ℕ) / 24`.

This module embeds that block into the literal reduced bad-tower residual and proves the residual
tends to positive infinity. Therefore an `O(1)` upper bound for bad-over-good excess cannot come
from boundedness of the bad channel: it must cancel a quadratically growing outer-prime block
against the archimedean and stable-tower channels. All statements are unconditional.
-/

open Set Finset Filter Topology
open scoped BigOperators

noncomputable section
namespace RHTower

/-- The literal reduced bad residual contains the full macroscopic one-mode outer-prime block. -/
theorem ccmFirstClockReducedBadTowerResidual_sixthPower_lower {m : ℕ}
    (hm : 25 ≤ m) (hmCheb : Real.exp 20 ≤ ((m ^ (4 : ℕ) : ℕ) : ℝ)) :
    (m : ℝ) ^ (2 : ℕ) / 24 ≤
      ccmFirstClockReducedBadTowerResidual
        (ccmFirstClockJuliaSixthPowerAperture m) := by
  have hm0 : 0 < m := by omega
  have hL : 0 < ccmFirstClockJuliaSixthPowerAperture m := by
    rw [ccmFirstClockJuliaSixthPowerAperture]
    exact mul_pos (by norm_num)
      (Real.log_pos (by exact_mod_cast (show 1 < m by omega)))
  have hsubset : suzukiMangoldtFivePrimeBlock (m ^ (4 : ℕ)) ⊆
      Nat.primesLE ⌊Real.exp (ccmFirstClockJuliaSixthPowerAperture m)⌋₊ := by
    intro p hp
    obtain ⟨hpPrime, _hpLower, hpUpper⟩ :=
      mem_suzukiMangoldtFivePrimeBlock.mp hp
    rw [ccmFirstClockJuliaSixthPower_cutoff hm0, Nat.mem_primesLE]
    constructor
    · calc
        p ≤ 5 * m ^ (4 : ℕ) := hpUpper
        _ ≤ m ^ (2 : ℕ) * m ^ (4 : ℕ) := Nat.mul_le_mul_right _ (by nlinarith)
        _ = m ^ (6 : ℕ) := by ring
    · exact hpPrime
  have hblockFull :
      (∑ p ∈ suzukiMangoldtFivePrimeBlock (m ^ (4 : ℕ)),
          ccmFirstClockReducedBadNatTerm
            (ccmFirstClockJuliaSixthPowerAperture m) p) ≤
        ∑ p ∈ Nat.primesLE
            ⌊Real.exp (ccmFirstClockJuliaSixthPowerAperture m)⌋₊,
          ccmFirstClockReducedBadNatTerm
            (ccmFirstClockJuliaSixthPowerAperture m) p := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun p hpFull _hpBlock => by
        rw [ccmFirstClockReducedBadNatTerm_of_prime _
          (Nat.prime_of_mem_primesLE hpFull)]
        exact ccmFirstClockReducedBadPrimeTerm_nonneg hL _
          (Nat.le_of_mem_primesLE hpFull))
  refine (ccmFirstClockJuliaSixthPower_block_badMass_lower hm hmCheb).trans ?_
  calc
    (∑ p ∈ suzukiMangoldtFivePrimeBlock (m ^ (4 : ℕ)),
        ccmFirstClockReducedBadNatTerm
          (ccmFirstClockJuliaSixthPowerAperture m) p) ≤
      ∑ p ∈ Nat.primesLE
          ⌊Real.exp (ccmFirstClockJuliaSixthPowerAperture m)⌋₊,
        ccmFirstClockReducedBadNatTerm
          (ccmFirstClockJuliaSixthPowerAperture m) p := hblockFull
    _ = ccmFirstClockReducedBadTowerResidual
        (ccmFirstClockJuliaSixthPowerAperture m) := by
      rw [ccmFirstClockReducedBadTowerResidual]
      apply Finset.sum_congr rfl
      intro p hp
      rw [ccmFirstClockReducedBadNatTerm_of_prime _
        (Nat.prime_of_mem_primesLE hp)]
      rfl

/-- The literal reduced bad residual tends to positive infinity along sixth-power apertures. -/
theorem tendsto_ccmFirstClockReducedBadTowerResidual_sixthPower_atTop :
    Tendsto (fun m : ℕ =>
      ccmFirstClockReducedBadTowerResidual
        (ccmFirstClockJuliaSixthPowerAperture m)) atTop atTop := by
  have hgrow : Tendsto (fun m : ℕ => (m : ℝ) ^ (2 : ℕ) / 24) atTop atTop :=
    ((tendsto_pow_atTop (n := 2) (by norm_num)).comp
      tendsto_natCast_atTop_atTop).atTop_div_const (by norm_num)
  refine tendsto_atTop_mono' atTop ?_ hgrow
  have hExp : ∀ᶠ m : ℕ in atTop, Real.exp 20 ≤ (m : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop (Real.exp 20)
  filter_upwards [hExp, eventually_ge_atTop 25] with m hmExp hm25
  have hmPowNat : m ≤ m ^ (4 : ℕ) := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0 < m)
      (by omega : 1 ≤ 4)
  have hmPow : (m : ℝ) ≤ ((m ^ (4 : ℕ) : ℕ) : ℝ) := by exact_mod_cast hmPowNat
  exact ccmFirstClockReducedBadTowerResidual_sixthPower_lower hm25
    (hmExp.trans hmPow)

end RHTower
