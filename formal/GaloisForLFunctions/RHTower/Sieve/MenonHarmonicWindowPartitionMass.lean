import GaloisForLFunctions.RHTower.Sieve.MenonFinalRangeWindowRough

/-!
# Menon's frequency partition, under the mass split

The window is split into the all-small set, where every prime block obeys its threshold, and the
some-large set, whose measure the moment method controls.  On the first the pointwise (or swapped)
receiver applies; on the second the measure-times-supremum receiver applies, with the moment
budget substituted for the measure.  Both halves are split over the ladder at the blocks' own
harmonic masses, so neither pays the block count.

This is the same partition the corpus already used in
`Sieve/MenonHarmonicFrequencyMomentAssembly`, but with the mass split in place of the block-count
split and with the small-set receiver in place of reciprocal Halasz--Montgomery on the exceptional
half.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- The small-set block cost is monotone in the exposed measure. -/
theorem menonHarmonicLevelTrivialBlockCost_mono
    (P : Finset ℕ) (A₀ B₀ : ℕ) (Q eta W : ℝ) {u v : ℝ} (k j J : ℕ) {V₀ : ℝ}
    (_hV₀ : 0 ≤ V₀) (huv : u ≤ v) :
    menonHarmonicLevelTrivialBlockCost P A₀ B₀ Q eta W u k j J V₀
      ≤ menonHarmonicLevelTrivialBlockCost P A₀ B₀ Q eta W v k j J V₀ := by
  rw [menonHarmonicLevelTrivialBlockCost, menonHarmonicLevelTrivialBlockCost]
  have hm : (0 : ℝ) ≤ harmonicPrimeMass (harmonicGeomCofactorBlock A₀ B₀ Q eta j) ^ (2 : ℕ) := by
    positivity
  have hstep : u * harmonicPrimeMass (harmonicGeomCofactorBlock A₀ B₀ Q eta j) ^ (2 : ℕ)
      ≤ v * harmonicPrimeMass (harmonicGeomCofactorBlock A₀ B₀ Q eta j) ^ (2 : ℕ) :=
    mul_le_mul_of_nonneg_right huv hm
  have hV₀sq : (0 : ℝ) ≤ V₀ ^ (2 : ℕ) := by positivity
  nlinarith [hstep, hV₀sq]

/-- **The small-set ladder with the measure replaced by any budget.** -/
theorem setIntegral_normSq_harmonicRamareBilinear_le_levelTrivial_mass_budget
    {P : Finset ℕ} {A₀ B₀ L : ℕ} {Q eta W vol : ℝ} (k : ℕ) (hk : 1 ≤ k)
    (hA₀ : 1 ≤ A₀) (hQ : 0 < Q) (heta : 0 ≤ eta) (hW : 1 ≤ W) (hL : 1 ≤ L)
    (hPprime : ∀ p ∈ P, p.Prime)
    (hPrange : ∀ p ∈ P, Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * (1 + eta) ^ L)
    (hmass : ∀ j ∈ Finset.range L,
      0 < harmonicPrimeMass (geomBlock P Q (1 + eta) j))
    (hleft : ∀ j ∈ Finset.range L,
      1 ≤ ⌈(A₀ : ℝ) / ((Q * (1 + eta) ^ j) * (1 + eta))⌉₊)
    (V₀ : ℕ → ℝ) (hV₀ : ∀ j ∈ Finset.range L, 0 < V₀ j)
    (J : ℕ → ℕ)
    (hJ : ∀ j ∈ Finset.range L,
      harmonicPrimeMass (geomBlock P Q (1 + eta) j) ≤ 2 ^ (J j) * V₀ j)
    {E : Set ℝ} (hEm : MeasurableSet E) (hEs : E ⊆ Set.Icc (-W) W)
    (hbudget : volume.real E ≤ vol) :
    (∫ w in E, ‖harmonicRamareBilinear P (Finset.Icc A₀ B₀) w‖ ^ (2 : ℕ))
      ≤ harmonicPrimeMass P * ∑ j ∈ Finset.range L,
          menonHarmonicLevelTrivialBlockCost P A₀ B₀ Q eta W vol k j (J j) (V₀ j)
            / harmonicPrimeMass (geomBlock P Q (1 + eta) j) := by
  classical
  have hbase := setIntegral_normSq_harmonicRamareBilinear_le_levelTrivial_mass
    (B₀ := B₀) k hk hA₀ hQ heta hW hL hPprime hPrange hmass hleft V₀ hV₀ J hJ hEm hEs
  have hPmass : (0 : ℝ) ≤ harmonicPrimeMass P :=
    Finset.sum_nonneg fun p _ => by positivity
  refine hbase.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j hj => ?_) hPmass)
  refine div_le_div_of_nonneg_right ?_ (hmass j hj).le
  exact menonHarmonicLevelTrivialBlockCost_mono P A₀ B₀ Q eta W k j (J j)
    (hV₀ j hj).le hbudget

/-- **The complete window estimate across Menon's frequency partition, mass split on both
halves.** -/
theorem integral_Icc_normSq_harmonicRamareBilinear_le_partition_mass
    {P : Finset ℕ} {A₀ B₀ L N : ℕ} {Q eta W : ℝ} (k : ℕ) (hk : 1 ≤ k)
    (hA₀ : 1 ≤ A₀) (hQ : 0 < Q) (heta : 0 ≤ eta) (hW : 1 ≤ W) (hL : 1 ≤ L)
    (hP : P ⊆ Finset.Icc 1 N)
    (hPprime : ∀ p ∈ P, p.Prime)
    (hPrange : ∀ p ∈ P, Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * (1 + eta) ^ L)
    (hmass : ∀ j ∈ Finset.range L,
      0 < harmonicPrimeMass (geomBlock P Q (1 + eta) j))
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
    (∫ w in Set.Icc (-W) W, ‖harmonicRamareBilinear P (Finset.Icc A₀ B₀) w‖ ^ (2 : ℕ))
      ≤ harmonicPrimeMass P * ∑ j ∈ Finset.range L,
            min (menonHarmonicAllSmallBlockCost P A₀ B₀ Q eta W (V j)
                  (menonHarmonicAllBlocksSmall P Q eta L V W) j)
              (menonHarmonicSwappedBlockCost P A₀ B₀ Q eta W
                (menonHarmonicAllBlocksSmall P Q eta L V W) j)
              / harmonicPrimeMass (geomBlock P Q (1 + eta) j)
        + harmonicPrimeMass P * ∑ j ∈ Finset.range L,
            menonHarmonicLevelTrivialBlockCost P A₀ B₀ Q eta W
                (menonHarmonicSomeLargeMomentBudget k N Q eta W L V) k j (J j) (V₀ j)
              / harmonicPrimeMass (geomBlock P Q (1 + eta) j) := by
  classical
  have hcont : Continuous fun w : ℝ =>
      ‖harmonicRamareBilinear P (Finset.Icc A₀ B₀) w‖ ^ (2 : ℕ) :=
    ((continuous_harmonicRamareBilinear P (Finset.Icc A₀ B₀)).norm).pow 2
  have hpart := setIntegral_menonHarmonic_frequencyPartition P Q eta L V W
    (fun w => ‖harmonicRamareBilinear P (Finset.Icc A₀ B₀) w‖ ^ (2 : ℕ))
    hcont.integrableOn_Icc
  rw [hpart]
  refine add_le_add ?_ ?_
  · exact setIntegral_normSq_harmonicRamareBilinear_le_min_mass hA₀ hQ heta hW hL
      hPprime hPrange V hmass hleft hright htop
      (measurableSet_menonHarmonicAllBlocksSmall P Q eta L V W)
      (menonHarmonicAllBlocksSmall_subset P Q eta L V W)
      (fun j hj w hw => norm_harmonicPrimeBlockPoly_le_of_mem_allBlocksSmall hj hw)
  · refine setIntegral_normSq_harmonicRamareBilinear_le_levelTrivial_mass_budget
      k hk hA₀ hQ heta hW hL hPprime hPrange hmass hleft V₀ hV₀ J hJ
      (measurableSet_menonHarmonicSomeBlockLarge P Q eta L V W)
      (fun _ hw => hw.1) ?_
    exact volume_menonHarmonicSomeBlockLarge_le_moments k N hk hP hPprime hQ heta
      (by linarith) V hV

end

end RHTower.Sieve
