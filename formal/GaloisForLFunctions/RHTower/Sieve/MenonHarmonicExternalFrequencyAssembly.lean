import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicGlobalFrequencyAssembly

/-!
# Harmonic final-range assembly on an external frequency set

Menon's initial prime ranges leave an external set of frequencies for the final wide prime range.
This module keeps that set explicit.  Each final block is split at its own threshold, its small half
is paid by reciprocal Halasz--Montgomery, and only its strict large-value subset pays the Case-II
measure budget.  The global moving-support defect remains outside the ladder sum.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- Part of an external frequency set where one harmonic prime block is at most its threshold. -/
def menonHarmonicPrimeBlockSmallOn (E : Set ℝ) (B : Finset ℕ) (V : ℝ) : Set ℝ :=
  E ∩ {w : ℝ | ‖harmonicPrimeBlockPoly B w‖ ≤ V}

/-- Complementary strict large-value part of an external frequency set. -/
def menonHarmonicPrimeBlockLargeOn (E : Set ℝ) (B : Finset ℕ) (V : ℝ) : Set ℝ :=
  E \ menonHarmonicPrimeBlockSmallOn E B V

theorem measurableSet_menonHarmonicPrimeBlockSmallOn
    {E : Set ℝ} (hE : MeasurableSet E) (B : Finset ℕ) (V : ℝ) :
    MeasurableSet (menonHarmonicPrimeBlockSmallOn E B V) := by
  exact hE.inter (measurableSet_le
    ((continuous_harmonicPrimeBlockPoly B).norm).measurable measurable_const)

theorem measurableSet_menonHarmonicPrimeBlockLargeOn
    {E : Set ℝ} (hE : MeasurableSet E) (B : Finset ℕ) (V : ℝ) :
    MeasurableSet (menonHarmonicPrimeBlockLargeOn E B V) := by
  exact hE.diff (measurableSet_menonHarmonicPrimeBlockSmallOn hE B V)

theorem menonHarmonicPrimeBlockSmallOn_union_largeOn
    (E : Set ℝ) (B : Finset ℕ) (V : ℝ) :
    menonHarmonicPrimeBlockSmallOn E B V ∪
      menonHarmonicPrimeBlockLargeOn E B V = E := by
  ext w
  simp only [menonHarmonicPrimeBlockLargeOn, menonHarmonicPrimeBlockSmallOn,
    Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_sdiff]
  tauto

theorem disjoint_menonHarmonicPrimeBlockSmallOn_largeOn
    (E : Set ℝ) (B : Finset ℕ) (V : ℝ) :
    Disjoint (menonHarmonicPrimeBlockSmallOn E B V)
      (menonHarmonicPrimeBlockLargeOn E B V) := by
  rw [menonHarmonicPrimeBlockLargeOn]
  exact Set.disjoint_sdiff_right

theorem norm_harmonicPrimeBlockPoly_le_of_mem_smallOn
    {E : Set ℝ} {B : Finset ℕ} {V w : ℝ}
    (hw : w ∈ menonHarmonicPrimeBlockSmallOn E B V) :
    ‖harmonicPrimeBlockPoly B w‖ ≤ V := hw.2

theorem norm_harmonicPrimeBlockPoly_gt_of_mem_largeOn
    {E : Set ℝ} {B : Finset ℕ} {V w : ℝ}
    (hw : w ∈ menonHarmonicPrimeBlockLargeOn E B V) :
    V < ‖harmonicPrimeBlockPoly B w‖ := by
  by_contra h
  exact hw.2 ⟨hw.1, le_of_not_gt h⟩

theorem setIntegral_menonHarmonicPrimeBlock_thresholdPartition
    {E : Set ℝ} (hE : MeasurableSet E) (B : Finset ℕ) (V : ℝ)
    (f : ℝ → ℝ) (hf : IntegrableOn f E) :
    (∫ w in E, f w) =
      (∫ w in menonHarmonicPrimeBlockSmallOn E B V, f w) +
        ∫ w in menonHarmonicPrimeBlockLargeOn E B V, f w := by
  have h := setIntegral_union
    (disjoint_menonHarmonicPrimeBlockSmallOn_largeOn E B V)
    (measurableSet_menonHarmonicPrimeBlockLargeOn hE B V)
    (hf.mono_set fun _ hw => hw.1)
    (hf.mono_set fun _ hw => hw.1)
  rw [menonHarmonicPrimeBlockSmallOn_union_largeOn E B V] at h
  exact h

/-- One final harmonic block on an external frequency set, with its strict large-value measure
exposed as the only exceptional input. -/
theorem setIntegral_normSq_harmonicProduct_geom_le_threshold_largeMeasure
    {P : Finset ℕ} {A₀ B₀ : ℕ} {Q eta W V M : ℝ}
    (hW : 1 ≤ W) (j : ℕ)
    (hPprime : ∀ p ∈ P, p.Prime)
    (hleft : 1 ≤ ⌈(A₀ : ℝ) /
      ((Q * (1 + eta) ^ j) * (1 + eta))⌉₊)
    (hright : 1 ≤ ⌊(B₀ : ℝ) / (Q * (1 + eta) ^ j)⌋₊)
    {E : Set ℝ} (hEm : MeasurableSet E) (hEs : E ⊆ Set.Icc (-W) W)
    (hlargeVolume :
      volume.real (menonHarmonicPrimeBlockLargeOn E
        (geomBlock P Q (1 + eta) j) V) ≤ M) :
    (∫ w in E,
      ‖harmonicPrimeBlockPoly (geomBlock P Q (1 + eta) j) w *
        logPoly (harmonicRamareCofactorCoeff P)
          (geomCofactorBlockAt A₀ B₀ Q eta j) w‖ ^ 2) ≤
      menonHarmonicProductCostVolume P A₀ B₀ Q eta W V (volume.real E) j +
        menonHarmonicProductCostVolume P A₀ B₀ Q eta W
          (harmonicPrimeMass (geomBlock P Q (1 + eta) j)) M j := by
  let B : Finset ℕ := geomBlock P Q (1 + eta) j
  let Esmall : Set ℝ := menonHarmonicPrimeBlockSmallOn E B V
  let Elarge : Set ℝ := menonHarmonicPrimeBlockLargeOn E B V
  let f : ℝ → ℝ := fun w =>
    ‖harmonicPrimeBlockPoly B w *
      logPoly (harmonicRamareCofactorCoeff P)
        (geomCofactorBlockAt A₀ B₀ Q eta j) w‖ ^ 2
  have hcont : Continuous f :=
    (((continuous_harmonicPrimeBlockPoly B).mul (continuous_logPoly _ _)).norm).pow 2
  have hsmallm : MeasurableSet Esmall :=
    measurableSet_menonHarmonicPrimeBlockSmallOn hEm B V
  have hlargem : MeasurableSet Elarge :=
    measurableSet_menonHarmonicPrimeBlockLargeOn hEm B V
  have hsmalls : Esmall ⊆ Set.Icc (-W) W := fun _ hw => hEs hw.1
  have hlarges : Elarge ⊆ Set.Icc (-W) W := fun _ hw => hEs hw.1
  have hsmall := setIntegral_normSq_harmonicProduct_geom_le_HM
    (P := P) (A₀ := A₀) (B₀ := B₀) (Q := Q) (eta := eta) (W := W)
    (V := V) hW j hleft hright hsmallm hsmalls
      (fun w hw => norm_harmonicPrimeBlockPoly_le_of_mem_smallOn hw)
  have hBprime : ∀ p ∈ B, p.Prime := by
    intro p hp
    exact hPprime p (geomBlock_subset P Q (1 + eta) j hp)
  have hlarge := setIntegral_normSq_harmonicProduct_geom_le_HM
    (P := P) (A₀ := A₀) (B₀ := B₀) (Q := Q) (eta := eta) (W := W)
    (V := harmonicPrimeMass B) hW j hleft hright hlargem hlarges
      (fun w _ => norm_harmonicPrimeBlockPoly_le_mass hBprime w)
  have hEtop : volume E ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono hEs)
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have hsmallVolume : volume.real Esmall ≤ volume.real E :=
    measureReal_mono (fun _ hw => hw.1) hEtop
  have hsmall' := (menonHarmonicProductCostVolume_mono
    P A₀ B₀ Q eta W V j hW hsmallVolume).trans'
      (by simpa only [B, Esmall] using hsmall)
  have hlarge' := (menonHarmonicProductCostVolume_mono
    P A₀ B₀ Q eta W (harmonicPrimeMass B) j hW
      (by simpa only [B, Elarge] using hlargeVolume)).trans'
      (by simpa only [B, Elarge] using hlarge)
  have hsplit := setIntegral_menonHarmonicPrimeBlock_thresholdPartition
    hEm B V f (hcont.integrableOn_Icc.mono_set hEs)
  calc
    (∫ w in E,
      ‖harmonicPrimeBlockPoly (geomBlock P Q (1 + eta) j) w *
        logPoly (harmonicRamareCofactorCoeff P)
          (geomCofactorBlockAt A₀ B₀ Q eta j) w‖ ^ 2) =
        (∫ w in Esmall, f w) + ∫ w in Elarge, f w := by
          simpa only [B, Esmall, Elarge, f] using hsplit
    _ ≤ _ := add_le_add hsmall' hlarge'

/-- Complete final harmonic ladder on an external frequency set.  The support defect is paid once;
large-value measures remain block-local. -/
theorem setIntegral_normSq_harmonicRamareBilinear_le_external_thresholds
    {P : Finset ℕ} {A₀ B₀ L : ℕ} {Q eta W : ℝ}
    (hA : 0 < A₀) (hQ : 1 < Q) (heta : 0 ≤ eta) (hW : 1 ≤ W) (hL : 1 ≤ L)
    (hPprime : ∀ p ∈ P, p.Prime)
    (hPrange : ∀ p ∈ P, Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * (1 + eta) ^ L)
    (V M : ℕ → ℝ)
    (hleft : ∀ j ∈ Finset.range L,
      1 ≤ ⌈(A₀ : ℝ) / ((Q * (1 + eta) ^ j) * (1 + eta))⌉₊)
    (hright : ∀ j ∈ Finset.range L,
      1 ≤ ⌊(B₀ : ℝ) / (Q * (1 + eta) ^ j)⌋₊)
    {E : Set ℝ} (hEm : MeasurableSet E) (hEs : E ⊆ Set.Icc (-W) W)
    (hlargeVolume : ∀ j ∈ Finset.range L,
      volume.real (menonHarmonicPrimeBlockLargeOn E
        (geomBlock P Q (1 + eta) j) (V j)) ≤ M j) :
    (∫ w in E, ‖harmonicRamareBilinear P (Finset.Icc A₀ B₀) w‖ ^ 2) ≤
      2 * (L : ℝ) * ∑ j ∈ Finset.range L,
        (menonHarmonicProductCostVolume P A₀ B₀ Q eta W
            (V j) (volume.real E) j +
          menonHarmonicProductCostVolume P A₀ B₀ Q eta W
            (harmonicPrimeMass (geomBlock P Q (1 + eta) j)) (M j) j) +
        2 * menonHarmonicLadderErrorBudget A₀ B₀ Q eta W L := by
  have hbase := setIntegral_normSq_harmonicRamareBilinear_le_ladder_closed
    (P := P) (A₀ := A₀) (B₀ := B₀) (Q := Q) (eta := eta) (W := W) (L := L)
    hA hQ heta hW hL hPprime hPrange hEm hEs
  refine hbase.trans (add_le_add ?_ le_rfl)
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j hj => ?_)
    (mul_nonneg (by norm_num) (Nat.cast_nonneg L))
  exact setIntegral_normSq_harmonicProduct_geom_le_threshold_largeMeasure
    hW j hPprime (hleft j hj) (hright j hj) hEm hEs (hlargeVolume j hj)

end


end RHTower.Sieve
