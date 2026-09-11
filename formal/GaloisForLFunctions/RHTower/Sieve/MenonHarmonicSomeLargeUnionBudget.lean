import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicWindowPartitionBudget

/-!
# From per-block large-value measures to a some-large budget

`Sieve/MenonHarmonicFrequencyPartition.volume_menonHarmonicSomeBlockLarge_le` is the union bound in
`ℝ≥0∞`.  The receivers of this session consume a **real** budget, and the large-values inputs
(`Sieve/MenonHarmonicCaseIIWideMeasure`, the moment method, Huxley) all produce per-block real
bounds.  This file is the glue: any family of per-block measure bounds gives a some-large budget,
and hence the complete partition estimate.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- **The union bound, in real measure.** -/
theorem volume_real_menonHarmonicSomeBlockLarge_le_sum
    (P : Finset ℕ) (Q eta : ℝ) (L : ℕ) (V : ℕ → ℝ) (W : ℝ) (M : ℕ → ℝ)
    (hM : ∀ j ∈ Finset.range L,
      volume.real (menonHarmonicBlockLarge P Q eta V W j) ≤ M j) :
    volume.real (menonHarmonicSomeBlockLarge P Q eta L V W)
      ≤ ∑ j ∈ Finset.range L, M j := by
  classical
  have hfinj : ∀ j ∈ Finset.range L,
      volume (menonHarmonicBlockLarge P Q eta V W j) ≠ ⊤ := by
    intro j _
    refine ne_top_of_le_ne_top ?_ (measure_mono (fun w hw => hw.1))
    simp [Real.volume_Icc]
  have hsumfin : (∑ j ∈ Finset.range L,
      volume (menonHarmonicBlockLarge P Q eta V W j)) ≠ ⊤ :=
    ENNReal.sum_ne_top.2 hfinj
  have hle := volume_menonHarmonicSomeBlockLarge_le P Q eta L V W
  have hmono := ENNReal.toReal_mono hsumfin hle
  rw [ENNReal.toReal_sum hfinj] at hmono
  refine hmono.trans ?_
  exact Finset.sum_le_sum hM

/-- **The complete partition estimate from per-block large-value measures.** -/
theorem integral_Icc_normSq_harmonicRamareBilinear_le_partition_blockMeasures
    {P : Finset ℕ} {A₀ B₀ L : ℕ} {Q eta W : ℝ} (k : ℕ) (hk : 1 ≤ k)
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
    (M : ℕ → ℝ)
    (hM : ∀ j ∈ Finset.range L,
      volume.real (menonHarmonicBlockLarge P Q eta V W j) ≤ M j) :
    (∫ w in Set.Icc (-W) W, ‖harmonicRamareBilinear P (Finset.Icc A₀ B₀) w‖ ^ 2)
      ≤ harmonicPrimeMass P * ∑ j ∈ menonHarmonicActiveBlocks P Q eta L,
            min (menonHarmonicAllSmallBlockCost P A₀ B₀ Q eta W (V j)
                  (menonHarmonicAllBlocksSmall P Q eta L V W) j)
              (menonHarmonicSwappedBlockCost P A₀ B₀ Q eta W
                (menonHarmonicAllBlocksSmall P Q eta L V W) j)
              / harmonicPrimeMass (geomBlock P Q (1 + eta) j)
        + harmonicPrimeMass P * ∑ j ∈ menonHarmonicActiveBlocks P Q eta L,
            menonHarmonicLevelTrivialBlockCost P A₀ B₀ Q eta W
                (∑ i ∈ Finset.range L, M i) k j (J j) (V₀ j)
              / harmonicPrimeMass (geomBlock P Q (1 + eta) j) :=
  integral_Icc_normSq_harmonicRamareBilinear_le_partition_budget k hk hA₀ hQ heta hW hL
    hPprime hPrange hleft hright htop V V₀ hV₀ J hJ
    (volume_real_menonHarmonicSomeBlockLarge_le_sum P Q eta L V W M hM)

end

end RHTower.Sieve
