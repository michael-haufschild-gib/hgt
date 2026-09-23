import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicWindowPartitionMassFilter
import GaloisForLFunctions.RHTower.Sieve.MenonFinalRangeWindowRough

/-!
# Menon's literal shell across the frequency partition, with no prime-gap hypothesis

The capstone of the corrected chain: the shell's frequency integral on `[-W,W]`, split at the
frequency partition, with the ladder split at the blocks' own harmonic masses on both halves, the
exceptional half received by measure-times-supremum with the moment budget, the rough half
discharged by the corpus's friable energy, and the sum taken only over blocks of positive mass so
that no block is required to contain a prime.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- **Menon's shell on a frequency window: the complete corrected estimate.** -/
theorem integral_Icc_normSq_menonFinalRangeShell_le_partition_mass_filter
    {x Q eta W : ℝ} {L : ℕ} (k : ℕ) (hk : 1 ≤ k)
    (hx : 1 ≤ ⌈x⌉₊) (hQ : 0 < Q) (heta : 0 ≤ eta) (hW : 1 ≤ W) (hWx : W ≤ x) (hL : 1 ≤ L)
    (hPrange : ∀ p ∈ menonFinalRangePrimes x,
      Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * (1 + eta) ^ L)
    (hleft : ∀ j ∈ Finset.range L,
      1 ≤ ⌈(⌈x⌉₊ : ℝ) / ((Q * (1 + eta) ^ j) * (1 + eta))⌉₊)
    (hright : ∀ j ∈ Finset.range L,
      1 ≤ ⌊(menonFinalRangeTopNat x : ℝ) / (Q * (1 + eta) ^ j)⌋₊)
    (htop : ∀ j ∈ Finset.range L, 1 ≤ ⌊Q * (1 + eta) ^ (j + 1)⌋₊)
    (V : ℕ → ℝ) (hV : ∀ j ∈ Finset.range L, 0 < V j)
    (V₀ : ℕ → ℝ) (hV₀ : ∀ j ∈ Finset.range L, 0 < V₀ j)
    (J : ℕ → ℕ)
    (hJ : ∀ j ∈ Finset.range L,
      harmonicPrimeMass (geomBlock (menonFinalRangePrimes x) Q (1 + eta) j)
        ≤ 2 ^ (J j) * V₀ j) :
    (∫ w in Set.Icc (-W) W,
      ‖logPoly harmonicMoebiusC (menonFinalRangeShell x) w‖ ^ (2 : ℕ))
      ≤ 2 * (harmonicPrimeMass (menonFinalRangePrimes x) *
              ∑ j ∈ menonHarmonicActiveBlocks (menonFinalRangePrimes x) Q eta L,
              min (menonHarmonicAllSmallBlockCost (menonFinalRangePrimes x) ⌈x⌉₊
                    (menonFinalRangeTopNat x) Q eta W (V j)
                    (menonHarmonicAllBlocksSmall (menonFinalRangePrimes x) Q eta L V W) j)
                (menonHarmonicSwappedBlockCost (menonFinalRangePrimes x) ⌈x⌉₊
                  (menonFinalRangeTopNat x) Q eta W
                  (menonHarmonicAllBlocksSmall (menonFinalRangePrimes x) Q eta L V W) j)
                / harmonicPrimeMass (geomBlock (menonFinalRangePrimes x) Q (1 + eta) j)
          + harmonicPrimeMass (menonFinalRangePrimes x) *
              ∑ j ∈ menonHarmonicActiveBlocks (menonFinalRangePrimes x) Q eta L,
              menonHarmonicLevelTrivialBlockCost (menonFinalRangePrimes x) ⌈x⌉₊
                  (menonFinalRangeTopNat x) Q eta W
                  (menonHarmonicSomeLargeMomentBudget k (menonFinalRangeTopNat x)
                    Q eta W L V) k j (J j) (V₀ j)
                / harmonicPrimeMass (geomBlock (menonFinalRangePrimes x) Q (1 + eta) j))
        + 2 * menonFinalRangeHarmonicRoughEnergy x := by
  classical
  have hP : menonFinalRangePrimes x ⊆ Finset.Icc 1 (menonFinalRangeTopNat x) := by
    intro p hp
    have hmem := mem_primesRange.1 hp
    exact Finset.mem_Icc.2 ⟨hmem.1.one_le, hmem.2.2⟩
  have hbil := integral_Icc_normSq_harmonicRamareBilinear_le_partition_mass_filter
    (P := menonFinalRangePrimes x) (A₀ := ⌈x⌉₊) (B₀ := menonFinalRangeTopNat x)
    (L := L) (N := menonFinalRangeTopNat x) (Q := Q) (eta := eta) (W := W)
    k hk hx hQ heta hW hL hP (fun p hp => menonFinalRangePrimes_prime x hp)
    hPrange hleft hright htop V hV V₀ hV₀ J hJ
  have hsplit := setIntegral_normSq_add_le
    (F := fun w => harmonicRamareBilinear (menonFinalRangePrimes x)
      (menonFinalRangeShell x) w)
    (G := fun w => logPoly harmonicMoebiusC (menonFinalRangeHarmonicRoughSet x) w)
    (E := Set.Icc (-W) W) (W := W)
    (continuous_harmonicRamareBilinear _ _)
    (continuous_logPoly _ _) measurableSet_Icc (le_refl _)
  have hsum : (∫ w in Set.Icc (-W) W,
      ‖logPoly harmonicMoebiusC (menonFinalRangeShell x) w‖ ^ (2 : ℕ))
      ≤ 2 * (∫ w in Set.Icc (-W) W,
          ‖harmonicRamareBilinear (menonFinalRangePrimes x)
            (menonFinalRangeShell x) w‖ ^ (2 : ℕ))
        + 2 * ∫ w in Set.Icc (-W) W,
            ‖logPoly harmonicMoebiusC (menonFinalRangeHarmonicRoughSet x) w‖ ^ (2 : ℕ) := by
    simpa only [logPoly_harmonicMoebius_eq_menonFinalRange_ramare_add_rough,
      menonFinalRangeHarmonicRoughSet] using hsplit
  have hrough := integral_Icc_normSq_menonFinalRangeHarmonicRough_le_energy
    (x := x) (W := W) (by linarith) hWx
  have h1 := mul_le_mul_of_nonneg_left hbil (show (0 : ℝ) ≤ 2 by norm_num)
  have h2 := mul_le_mul_of_nonneg_left hrough (show (0 : ℝ) ≤ 2 by norm_num)
  exact hsum.trans (add_le_add h1 h2)

end

end RHTower.Sieve
