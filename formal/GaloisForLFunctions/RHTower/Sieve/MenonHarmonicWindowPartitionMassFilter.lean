import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicRamareLadderMassFilter
import GaloisForLFunctions.RHTower.Sieve.MenonFinalRangeWindowPartition

/-!
# The window estimate, with no block required to contain a prime

The same chain as `MenonHarmonicWindowPartitionMass` and `MenonFinalRangeWindowPartition`, but
summed over the ladder's blocks of positive harmonic mass.  Along Menon's schedule the blocks have
ratio `1 + (log x)^{-10}`, so requiring every one of them to contain a prime is a prime-gap
theorem; the filtered form needs nothing of the kind, because an empty block contributes nothing.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- The ladder's blocks of positive harmonic mass. -/
def menonHarmonicActiveBlocks (P : Finset ℕ) (Q eta : ℝ) (L : ℕ) : Finset ℕ :=
  (Finset.range L).filter (fun j => 0 < harmonicPrimeMass (geomBlock P Q (1 + eta) j))

theorem menonHarmonicActiveBlocks_subset (P : Finset ℕ) (Q eta : ℝ) (L : ℕ) :
    menonHarmonicActiveBlocks P Q eta L ⊆ Finset.range L :=
  Finset.filter_subset _ _

theorem harmonicPrimeMass_pos_of_mem_active {P : Finset ℕ} {Q eta : ℝ} {L j : ℕ}
    (hj : j ∈ menonHarmonicActiveBlocks P Q eta L) :
    0 < harmonicPrimeMass (geomBlock P Q (1 + eta) j) :=
  (Finset.mem_filter.1 hj).2

/-- **The hybrid ladder at the blocks' masses, with no prime-gap hypothesis.** -/
theorem setIntegral_normSq_harmonicRamareBilinear_le_min_mass_filter
    {P : Finset ℕ} {A₀ B₀ L : ℕ} {Q eta W : ℝ}
    (hA₀ : 1 ≤ A₀) (hQ : 0 < Q) (heta : 0 ≤ eta) (hW : 1 ≤ W) (hL : 1 ≤ L)
    (hPprime : ∀ p ∈ P, p.Prime)
    (hPrange : ∀ p ∈ P, Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * (1 + eta) ^ L)
    (V : ℕ → ℝ)
    (hleft : ∀ j ∈ Finset.range L,
      1 ≤ ⌈(A₀ : ℝ) / ((Q * (1 + eta) ^ j) * (1 + eta))⌉₊)
    (hright : ∀ j ∈ Finset.range L,
      1 ≤ ⌊(B₀ : ℝ) / (Q * (1 + eta) ^ j)⌋₊)
    (htop : ∀ j ∈ Finset.range L, 1 ≤ ⌊Q * (1 + eta) ^ (j + 1)⌋₊)
    {E : Set ℝ} (hEm : MeasurableSet E) (hEs : E ⊆ Set.Icc (-W) W)
    (hprime : ∀ j ∈ Finset.range L, ∀ w ∈ E,
      ‖harmonicPrimeBlockPoly (geomBlock P Q (1 + eta) j) w‖ ≤ V j) :
    (∫ w in E, ‖harmonicRamareBilinear P (Finset.Icc A₀ B₀) w‖ ^ 2)
      ≤ harmonicPrimeMass P * ∑ j ∈ menonHarmonicActiveBlocks P Q eta L,
          min (menonHarmonicAllSmallBlockCost P A₀ B₀ Q eta W (V j) E j)
            (menonHarmonicSwappedBlockCost P A₀ B₀ Q eta W E j)
          / harmonicPrimeMass (geomBlock P Q (1 + eta) j) := by
  classical
  have hr : 1 ≤ 1 + eta := by linarith
  have hsplit := setIntegral_normSq_harmonicRamareBilinear_le_blocks_mass_filter
    (P := P) (s := Finset.Icc A₀ B₀) (W := W) hEm hEs
    (Finset.range L) (geomBlock P Q (1 + eta))
    (geomBlock_pairwiseDisjoint P hQ hr L)
    (geomBlock_biUnion_eq P Q (1 + eta) hL hPrange)
    (fun j _ p hp => hPprime p (geomBlock_subset P Q (1 + eta) j hp))
  have hPmass : (0 : ℝ) ≤ harmonicPrimeMass P :=
    Finset.sum_nonneg fun p _ => by positivity
  refine hsplit.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j hj => ?_) hPmass)
  have hjr : j ∈ Finset.range L := menonHarmonicActiveBlocks_subset P Q eta L hj
  have hjm := harmonicPrimeMass_pos_of_mem_active hj
  refine div_le_div_of_nonneg_right ?_ hjm.le
  exact setIntegral_normSq_harmonicRamareBlock_geom_le_min
    hA₀ hQ heta hW j hPprime (hleft j hjr) (hright j hjr) (htop j hjr) hEm hEs
    (hprime j hjr)

/-- **The small-set ladder at the blocks' masses, with no prime-gap hypothesis.** -/
theorem setIntegral_normSq_harmonicRamareBilinear_le_levelTrivial_mass_filter
    {P : Finset ℕ} {A₀ B₀ L : ℕ} {Q eta W vol : ℝ} (k : ℕ) (hk : 1 ≤ k)
    (hA₀ : 1 ≤ A₀) (hQ : 0 < Q) (heta : 0 ≤ eta) (hW : 1 ≤ W) (hL : 1 ≤ L)
    (hPprime : ∀ p ∈ P, p.Prime)
    (hPrange : ∀ p ∈ P, Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * (1 + eta) ^ L)
    (hleft : ∀ j ∈ Finset.range L,
      1 ≤ ⌈(A₀ : ℝ) / ((Q * (1 + eta) ^ j) * (1 + eta))⌉₊)
    (V₀ : ℕ → ℝ) (hV₀ : ∀ j ∈ Finset.range L, 0 < V₀ j)
    (J : ℕ → ℕ)
    (hJ : ∀ j ∈ Finset.range L,
      harmonicPrimeMass (geomBlock P Q (1 + eta) j) ≤ 2 ^ (J j) * V₀ j)
    {E : Set ℝ} (hEm : MeasurableSet E) (hEs : E ⊆ Set.Icc (-W) W)
    (hbudget : volume.real E ≤ vol) :
    (∫ w in E, ‖harmonicRamareBilinear P (Finset.Icc A₀ B₀) w‖ ^ 2)
      ≤ harmonicPrimeMass P * ∑ j ∈ menonHarmonicActiveBlocks P Q eta L,
          menonHarmonicLevelTrivialBlockCost P A₀ B₀ Q eta W vol k j (J j) (V₀ j)
            / harmonicPrimeMass (geomBlock P Q (1 + eta) j) := by
  classical
  have hr : 1 ≤ 1 + eta := by linarith
  have hsplit := setIntegral_normSq_harmonicRamareBilinear_le_blocks_mass_filter
    (P := P) (s := Finset.Icc A₀ B₀) (W := W) hEm hEs
    (Finset.range L) (geomBlock P Q (1 + eta))
    (geomBlock_pairwiseDisjoint P hQ hr L)
    (geomBlock_biUnion_eq P Q (1 + eta) hL hPrange)
    (fun j _ p hp => hPprime p (geomBlock_subset P Q (1 + eta) j hp))
  have hPmass : (0 : ℝ) ≤ harmonicPrimeMass P :=
    Finset.sum_nonneg fun p _ => by positivity
  refine hsplit.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j hj => ?_) hPmass)
  have hjr : j ∈ Finset.range L := menonHarmonicActiveBlocks_subset P Q eta L hj
  have hjm := harmonicPrimeMass_pos_of_mem_active hj
  refine div_le_div_of_nonneg_right ?_ hjm.le
  refine le_trans (setIntegral_normSq_harmonicRamareBlock_geom_le_levelTrivial j k hk hA₀ hQ
    heta hW hPprime (hleft j hjr) hEm hEs (hV₀ j hjr) (hJ j hjr)) ?_
  exact menonHarmonicLevelTrivialBlockCost_mono P A₀ B₀ Q eta W k j (J j)
    (hV₀ j hjr).le hbudget

/-- **The complete window estimate across the frequency partition, with no prime-gap
hypothesis.** -/
theorem integral_Icc_normSq_harmonicRamareBilinear_le_partition_mass_filter
    {P : Finset ℕ} {A₀ B₀ L N : ℕ} {Q eta W : ℝ} (k : ℕ) (hk : 1 ≤ k)
    (hA₀ : 1 ≤ A₀) (hQ : 0 < Q) (heta : 0 ≤ eta) (hW : 1 ≤ W) (hL : 1 ≤ L)
    (hP : P ⊆ Finset.Icc 1 N)
    (hPprime : ∀ p ∈ P, p.Prime)
    (hPrange : ∀ p ∈ P, Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * (1 + eta) ^ L)
    (hleft : ∀ j ∈ Finset.range L,
      1 ≤ ⌈(A₀ : ℝ) / ((Q * (1 + eta) ^ j) * (1 + eta))⌉₊)
    (hright : ∀ j ∈ Finset.range L,
      1 ≤ ⌊(B₀ : ℝ) / (Q * (1 + eta) ^ j)⌋₊)
    (htop : ∀ j ∈ Finset.range L, 1 ≤ ⌊Q * (1 + eta) ^ (j + 1)⌋₊)
    (V : ℕ → ℝ) (hV : ∀ j ∈ Finset.range L, 0 < V j)
    (V₀ : ℕ → ℝ) (hV₀ : ∀ j ∈ Finset.range L, 0 < V₀ j)
    (J : ℕ → ℕ)
    (hJ : ∀ j ∈ Finset.range L,
      harmonicPrimeMass (geomBlock P Q (1 + eta) j) ≤ 2 ^ (J j) * V₀ j) :
    (∫ w in Set.Icc (-W) W, ‖harmonicRamareBilinear P (Finset.Icc A₀ B₀) w‖ ^ 2)
      ≤ harmonicPrimeMass P * ∑ j ∈ menonHarmonicActiveBlocks P Q eta L,
            min (menonHarmonicAllSmallBlockCost P A₀ B₀ Q eta W (V j)
                  (menonHarmonicAllBlocksSmall P Q eta L V W) j)
              (menonHarmonicSwappedBlockCost P A₀ B₀ Q eta W
                (menonHarmonicAllBlocksSmall P Q eta L V W) j)
              / harmonicPrimeMass (geomBlock P Q (1 + eta) j)
        + harmonicPrimeMass P * ∑ j ∈ menonHarmonicActiveBlocks P Q eta L,
            menonHarmonicLevelTrivialBlockCost P A₀ B₀ Q eta W
                (menonHarmonicSomeLargeMomentBudget k N Q eta W L V) k j (J j) (V₀ j)
              / harmonicPrimeMass (geomBlock P Q (1 + eta) j) := by
  classical
  have hcont : Continuous fun w : ℝ =>
      ‖harmonicRamareBilinear P (Finset.Icc A₀ B₀) w‖ ^ 2 :=
    ((continuous_harmonicRamareBilinear P (Finset.Icc A₀ B₀)).norm).pow 2
  have hpart := setIntegral_menonHarmonic_frequencyPartition P Q eta L V W
    (fun w => ‖harmonicRamareBilinear P (Finset.Icc A₀ B₀) w‖ ^ 2)
    hcont.integrableOn_Icc
  rw [hpart]
  refine add_le_add ?_ ?_
  · exact setIntegral_normSq_harmonicRamareBilinear_le_min_mass_filter hA₀ hQ heta hW hL
      hPprime hPrange V hleft hright htop
      (measurableSet_menonHarmonicAllBlocksSmall P Q eta L V W)
      (menonHarmonicAllBlocksSmall_subset P Q eta L V W)
      (fun j hj w hw => norm_harmonicPrimeBlockPoly_le_of_mem_allBlocksSmall hj hw)
  · refine setIntegral_normSq_harmonicRamareBilinear_le_levelTrivial_mass_filter
      (B₀ := B₀) k hk hA₀ hQ heta hW hL hPprime hPrange hleft V₀ hV₀ J hJ
      (measurableSet_menonHarmonicSomeBlockLarge P Q eta L V W)
      (fun _ hw => hw.1) ?_
    exact volume_menonHarmonicSomeBlockLarge_le_moments k N hk hP hPprime hQ heta
      (by linarith) V hV

end

end RHTower.Sieve
