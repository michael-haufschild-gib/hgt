import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicPrimePowerMeasure
import GaloisForLFunctions.RHTower.Sieve.Section4AllBlocksSmall

/-!
# Menon's harmonic all-small / some-large frequency partition

Menon's final harmonic Ramaré ladder is estimated differently where every harmonic prime block is
small and where at least one block is large.  This module defines those two literal measurable
sets in the Gallagher variable, proves the finite exceptional-block cover, and splits an arbitrary
integrable frequency mass exactly across them.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- Frequencies in `[-W,W]` where every harmonic prime block obeys its assigned threshold. -/
def menonHarmonicAllBlocksSmall
    (P : Finset ℕ) (Q eta : ℝ) (L : ℕ) (V : ℕ → ℝ) (W : ℝ) : Set ℝ :=
  Set.Icc (-W) W ∩ ⋂ j ∈ Finset.range L,
    {w : ℝ | ‖harmonicPrimeBlockPoly (geomBlock P Q (1 + eta) j) w‖ ≤ V j}

/-- Complementary frequencies where some harmonic prime block is large. -/
def menonHarmonicSomeBlockLarge
    (P : Finset ℕ) (Q eta : ℝ) (L : ℕ) (V : ℕ → ℝ) (W : ℝ) : Set ℝ :=
  Set.Icc (-W) W \ menonHarmonicAllBlocksSmall P Q eta L V W

/-- Large-value set for one literal harmonic prime block. -/
def menonHarmonicBlockLarge
    (P : Finset ℕ) (Q eta : ℝ) (V : ℕ → ℝ) (W : ℝ) (j : ℕ) : Set ℝ :=
  {w ∈ Set.Icc (-W) W |
    V j ≤ ‖harmonicPrimeBlockPoly (geomBlock P Q (1 + eta) j) w‖}

theorem measurableSet_menonHarmonicAllBlocksSmall
    (P : Finset ℕ) (Q eta : ℝ) (L : ℕ) (V : ℕ → ℝ) (W : ℝ) :
    MeasurableSet (menonHarmonicAllBlocksSmall P Q eta L V W) := by
  refine measurableSet_Icc.inter ?_
  refine MeasurableSet.biInter (Finset.range L).countable_toSet fun j _ => ?_
  exact measurableSet_le
    ((continuous_harmonicPrimeBlockPoly (geomBlock P Q (1 + eta) j)).norm).measurable
    measurable_const

theorem measurableSet_menonHarmonicSomeBlockLarge
    (P : Finset ℕ) (Q eta : ℝ) (L : ℕ) (V : ℕ → ℝ) (W : ℝ) :
    MeasurableSet (menonHarmonicSomeBlockLarge P Q eta L V W) := by
  exact measurableSet_Icc.diff
    (measurableSet_menonHarmonicAllBlocksSmall P Q eta L V W)

theorem measurableSet_menonHarmonicBlockLarge
    (P : Finset ℕ) (Q eta : ℝ) (V : ℕ → ℝ) (W : ℝ) (j : ℕ) :
    MeasurableSet (menonHarmonicBlockLarge P Q eta V W j) := by
  exact measurableSet_Icc.inter (measurableSet_le measurable_const
    ((continuous_harmonicPrimeBlockPoly (geomBlock P Q (1 + eta) j)).norm).measurable)

theorem menonHarmonicAllBlocksSmall_subset
    (P : Finset ℕ) (Q eta : ℝ) (L : ℕ) (V : ℕ → ℝ) (W : ℝ) :
    menonHarmonicAllBlocksSmall P Q eta L V W ⊆ Set.Icc (-W) W :=
  fun _ hw => hw.1

/-- Membership in the all-small set discharges one block's pointwise threshold. -/
theorem norm_harmonicPrimeBlockPoly_le_of_mem_allBlocksSmall
    {P : Finset ℕ} {Q eta : ℝ} {L : ℕ} {V : ℕ → ℝ} {W : ℝ}
    {j : ℕ} (hj : j ∈ Finset.range L) {w : ℝ}
    (hw : w ∈ menonHarmonicAllBlocksSmall P Q eta L V W) :
    ‖harmonicPrimeBlockPoly (geomBlock P Q (1 + eta) j) w‖ ≤ V j := by
  have h := hw.2
  rw [Set.mem_iInter₂] at h
  exact h j hj

/-- The some-large set is covered by the finite family of literal block-large sets. -/
theorem menonHarmonicSomeBlockLarge_subset_iUnion
    (P : Finset ℕ) (Q eta : ℝ) (L : ℕ) (V : ℕ → ℝ) (W : ℝ) :
    menonHarmonicSomeBlockLarge P Q eta L V W ⊆
      ⋃ j ∈ Finset.range L, menonHarmonicBlockLarge P Q eta V W j := by
  intro w hw
  have hwIcc : w ∈ Set.Icc (-W) W := hw.1
  have hnot : w ∉ menonHarmonicAllBlocksSmall P Q eta L V W := hw.2
  have hex : ∃ j ∈ Finset.range L,
      V j < ‖harmonicPrimeBlockPoly (geomBlock P Q (1 + eta) j) w‖ := by
    by_contra hcon
    refine hnot ⟨hwIcc, ?_⟩
    rw [Set.mem_iInter₂]
    intro j hj
    by_contra hjlarge
    exact hcon ⟨j, hj, lt_of_not_ge hjlarge⟩
  obtain ⟨j, hj, hjlarge⟩ := hex
  rw [Set.mem_iUnion₂]
  exact ⟨j, hj, ⟨hwIcc, hjlarge.le⟩⟩

/-- Union bound for the harmonic some-large set. -/
theorem volume_menonHarmonicSomeBlockLarge_le
    (P : Finset ℕ) (Q eta : ℝ) (L : ℕ) (V : ℕ → ℝ) (W : ℝ) :
    volume (menonHarmonicSomeBlockLarge P Q eta L V W) ≤
      ∑ j ∈ Finset.range L, volume (menonHarmonicBlockLarge P Q eta V W j) := by
  refine (measure_mono
    (menonHarmonicSomeBlockLarge_subset_iUnion P Q eta L V W)).trans ?_
  exact measure_biUnion_finset_le _ _

/-- The two pieces cover the frequency window exactly. -/
theorem menonHarmonic_frequencyWindow_eq_union
    (P : Finset ℕ) (Q eta : ℝ) (L : ℕ) (V : ℕ → ℝ) (W : ℝ) :
    menonHarmonicAllBlocksSmall P Q eta L V W ∪
        menonHarmonicSomeBlockLarge P Q eta L V W = Set.Icc (-W) W := by
  ext w
  constructor
  · intro hw
    rcases hw with hw | hw
    · exact menonHarmonicAllBlocksSmall_subset P Q eta L V W hw
    · exact hw.1
  · intro hw
    by_cases hsmall : w ∈ menonHarmonicAllBlocksSmall P Q eta L V W
    · exact Or.inl hsmall
    · exact Or.inr ⟨hw, hsmall⟩

theorem disjoint_menonHarmonic_frequencyPartition
    (P : Finset ℕ) (Q eta : ℝ) (L : ℕ) (V : ℕ → ℝ) (W : ℝ) :
    Disjoint (menonHarmonicAllBlocksSmall P Q eta L V W)
      (menonHarmonicSomeBlockLarge P Q eta L V W) := by
  rw [menonHarmonicSomeBlockLarge]
  exact Set.disjoint_sdiff_right

/-- Exact integral split across Menon's harmonic frequency partition. -/
theorem setIntegral_menonHarmonic_frequencyPartition
    (P : Finset ℕ) (Q eta : ℝ) (L : ℕ) (V : ℕ → ℝ) (W : ℝ)
    (f : ℝ → ℝ) (hf : IntegrableOn f (Set.Icc (-W) W)) :
    (∫ w in Set.Icc (-W) W, f w) =
      (∫ w in menonHarmonicAllBlocksSmall P Q eta L V W, f w) +
        ∫ w in menonHarmonicSomeBlockLarge P Q eta L V W, f w := by
  rw [← menonHarmonic_frequencyWindow_eq_union P Q eta L V W]
  exact setIntegral_union
    (disjoint_menonHarmonic_frequencyPartition P Q eta L V W)
    (measurableSet_menonHarmonicSomeBlockLarge P Q eta L V W)
    (hf.mono_set (menonHarmonicAllBlocksSmall_subset P Q eta L V W))
    (hf.mono_set (fun _ hw => hw.1))

end

end RHTower.Sieve
