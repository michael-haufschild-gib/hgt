import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicWindowPartitionMass

/-!
# Menon's literal shell across the frequency partition, with the mass split on both halves

The corpus's `integral_Icc_normSq_menonFinalRangeShell_le_explicitMoments` runs the same partition
with the block-count split and reciprocal Halasz--Montgomery on both halves.  This is the same
statement with the two corrections of this session: the split costs the total harmonic mass of the
designated prime range rather than the number of blocks, and the exceptional half uses the
measure-times-supremum receiver, whose every term is proportional to a measure.

The rough half is the corpus's friable energy, already `o((log x)^{-8})`.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- **Menon's shell across the frequency partition, mass split, rough half discharged.** -/
theorem integral_Icc_normSq_menonFinalRangeShell_le_partition_mass
    {x Q eta W : ℝ} {L : ℕ} (k : ℕ) (hk : 1 ≤ k)
    (hx : 1 ≤ ⌈x⌉₊) (hQ : 0 < Q) (heta : 0 ≤ eta) (hW : 1 ≤ W) (hWx : W ≤ x) (hL : 1 ≤ L)
    (hPrange : ∀ p ∈ menonFinalRangePrimes x,
      Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * (1 + eta) ^ L)
    (hmass : ∀ j ∈ Finset.range L,
      0 < harmonicPrimeMass (geomBlock (menonFinalRangePrimes x) Q (1 + eta) j))
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
      ≤ 2 * (harmonicPrimeMass (menonFinalRangePrimes x) * ∑ j ∈ Finset.range L,
              min (menonHarmonicAllSmallBlockCost (menonFinalRangePrimes x) ⌈x⌉₊
                    (menonFinalRangeTopNat x) Q eta W (V j)
                    (menonHarmonicAllBlocksSmall (menonFinalRangePrimes x) Q eta L V W) j)
                (menonHarmonicSwappedBlockCost (menonFinalRangePrimes x) ⌈x⌉₊
                  (menonFinalRangeTopNat x) Q eta W
                  (menonHarmonicAllBlocksSmall (menonFinalRangePrimes x) Q eta L V W) j)
                / harmonicPrimeMass (geomBlock (menonFinalRangePrimes x) Q (1 + eta) j)
          + harmonicPrimeMass (menonFinalRangePrimes x) * ∑ j ∈ Finset.range L,
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
  have hbil := integral_Icc_normSq_harmonicRamareBilinear_le_partition_mass
    (P := menonFinalRangePrimes x) (A₀ := ⌈x⌉₊) (B₀ := menonFinalRangeTopNat x)
    (L := L) (N := menonFinalRangeTopNat x) (Q := Q) (eta := eta) (W := W)
    k hk hx hQ heta hW hL hP (fun p hp => menonFinalRangePrimes_prime x hp)
    hPrange hmass hleft hright htop V hV V₀ hV₀ J hJ
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
