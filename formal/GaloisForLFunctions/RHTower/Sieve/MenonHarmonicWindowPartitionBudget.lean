import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicWindowPartitionMassFilter

/-!
# The frequency partition with an arbitrary exceptional budget

`integral_Icc_normSq_harmonicRamareBilinear_le_partition_mass_filter` hard-wires the corpus's
moment budget for the some-large set.  Any measure bound will do, and the Heath--Brown/Case-II
route produces a different one (`Sieve/MenonHarmonicCaseIIWideMeasure`).  This file states the
partition estimate against an arbitrary budget, so whichever large-values input lands can be
substituted without touching the rest of the chain.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- **The frequency partition against any exceptional-measure budget.** -/
theorem integral_Icc_normSq_harmonicRamareBilinear_le_partition_budget
    {P : Finset ℕ} {A₀ B₀ L : ℕ} {Q eta W vol : ℝ} (k : ℕ) (hk : 1 ≤ k)
    (hA₀ : 1 ≤ A₀) (hQ : 0 < Q) (heta : 0 ≤ eta) (hW : 1 ≤ W) (hL : 1 ≤ L)
    (hPprime : ∀ p ∈ P, p.Prime)
    (hPrange : ∀ p ∈ P, Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * (1 + eta) ^ L)
    (hleft : ∀ j ∈ Finset.range L,
      1 ≤ ⌈(A₀ : ℝ) / ((Q * (1 + eta) ^ j) * (1 + eta))⌉₊)
    (hright : ∀ j ∈ Finset.range L,
      1 ≤ ⌊(B₀ : ℝ) / (Q * (1 + eta) ^ j)⌋₊)
    (htop : ∀ j ∈ Finset.range L, 1 ≤ ⌊Q * (1 + eta) ^ (j + 1)⌋₊)
    (V : ℕ → ℝ)
    (V₀ : ℕ → ℝ) (hV₀ : ∀ j ∈ Finset.range L, 0 < V₀ j)
    (J : ℕ → ℕ)
    (hJ : ∀ j ∈ Finset.range L,
      harmonicPrimeMass (geomBlock P Q (1 + eta) j) ≤ 2 ^ (J j) * V₀ j)
    (hbudget : volume.real (menonHarmonicSomeBlockLarge P Q eta L V W) ≤ vol) :
    (∫ w in Set.Icc (-W) W, ‖harmonicRamareBilinear P (Finset.Icc A₀ B₀) w‖ ^ (2 : ℕ))
      ≤ harmonicPrimeMass P * ∑ j ∈ menonHarmonicActiveBlocks P Q eta L,
            min (menonHarmonicAllSmallBlockCost P A₀ B₀ Q eta W (V j)
                  (menonHarmonicAllBlocksSmall P Q eta L V W) j)
              (menonHarmonicSwappedBlockCost P A₀ B₀ Q eta W
                (menonHarmonicAllBlocksSmall P Q eta L V W) j)
              / harmonicPrimeMass (geomBlock P Q (1 + eta) j)
        + harmonicPrimeMass P * ∑ j ∈ menonHarmonicActiveBlocks P Q eta L,
            menonHarmonicLevelTrivialBlockCost P A₀ B₀ Q eta W vol k j (J j) (V₀ j)
              / harmonicPrimeMass (geomBlock P Q (1 + eta) j) := by
  classical
  have hcont : Continuous fun w : ℝ =>
      ‖harmonicRamareBilinear P (Finset.Icc A₀ B₀) w‖ ^ (2 : ℕ) := by
    refine (Continuous.norm ?_).pow 2
    refine continuous_finsetSum _ fun p _ => ?_
    exact ((continuous_moebiusPhase p).div_const _).mul (continuous_logPoly _ _)
  have hpart := setIntegral_menonHarmonic_frequencyPartition P Q eta L V W
    (fun w => ‖harmonicRamareBilinear P (Finset.Icc A₀ B₀) w‖ ^ (2 : ℕ))
    hcont.integrableOn_Icc
  rw [hpart]
  refine add_le_add ?_ ?_
  · exact setIntegral_normSq_harmonicRamareBilinear_le_min_mass_filter hA₀ hQ heta hW hL
      hPprime hPrange V hleft hright htop
      (measurableSet_menonHarmonicAllBlocksSmall P Q eta L V W)
      (menonHarmonicAllBlocksSmall_subset P Q eta L V W)
      (fun j hj w hw => norm_harmonicPrimeBlockPoly_le_of_mem_allBlocksSmall hj hw)
  · exact setIntegral_normSq_harmonicRamareBilinear_le_levelTrivial_mass_filter
      (B₀ := B₀) k hk hA₀ hQ heta hW hL hPprime hPrange hleft V₀ hV₀ J hJ
      (measurableSet_menonHarmonicSomeBlockLarge P Q eta L V W)
      (fun _ hw => hw.1) hbudget

end

end RHTower.Sieve
