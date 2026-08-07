import Mathlib.Probability.ConditionalProbability

/-!
# Conditioning moves a probability measure by exactly the complementary mass

Conditioning on an event `B` of probability `b` displaces a probability measure by exactly `1 - b` in
total variation.  The upper bound holds set by set and needs no decomposition theory: on the part of
a test set inside `B` the conditional measure is inflated by the factor `1/b`, which contributes at
most `b·(1-b)/b`, and on the part outside `B` it loses at most the complementary mass.  Testing `B`
itself attains the bound.

This is the exact amplification law behind normalized sieve restrictions: an unnormalized restriction
loses mass `a_P - a_Q` and telescopes, while the normalized conditional states stay a fixed distance
apart, so summability of the unnormalized defect says nothing about the normalized net.
-/

open MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Conditioning displaces a probability measure by at most the complementary
mass, uniformly over test sets.  The test set need not be measurable. -/
theorem abs_toReal_cond_sub_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    {B : Set Ω} (hB : MeasurableSet B) (hBpos : μ B ≠ 0) (A : Set Ω) :
    |((ProbabilityTheory.cond μ B) A).toReal - (μ A).toReal| ≤
      1 - (μ B).toReal := by
  have hBne : μ B ≠ ⊤ := measure_ne_top μ B
  have hb0 : 0 < (μ B).toReal := ENNReal.toReal_pos hBpos hBne
  have hb1 : (μ B).toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono (measure_ne_top μ univ) (measure_mono (subset_univ B))
  -- the three real quantities
  set b : ℝ := (μ B).toReal with hbdef
  set x : ℝ := (μ (B ∩ A)).toReal with hxdef
  set y : ℝ := (μ A).toReal with hydef
  have hxb : x ≤ b :=
    ENNReal.toReal_mono hBne (measure_mono inter_subset_left)
  have hxy : x ≤ y :=
    ENNReal.toReal_mono (measure_ne_top μ A) (measure_mono inter_subset_right)
  have hx0 : 0 ≤ x := ENNReal.toReal_nonneg
  have hcomplReal : b + (μ Bᶜ).toReal = 1 := by
    have hsum : μ B + μ Bᶜ = 1 := by
      rw [measure_add_measure_compl hB]
      exact measure_univ
    have h := congrArg ENNReal.toReal hsum
    rwa [ENNReal.toReal_add hBne (measure_ne_top μ Bᶜ), ENNReal.toReal_one] at h
  have hcompl : y - x ≤ 1 - b := by
    have hcover : A ⊆ (B ∩ A) ∪ Bᶜ := by
      intro ω hω
      by_cases hb : ω ∈ B
      · exact Or.inl ⟨hb, hω⟩
      · exact Or.inr hb
    have h1 : μ A ≤ μ (B ∩ A) + μ Bᶜ :=
      le_trans (measure_mono hcover) (measure_union_le _ _)
    have h2 := ENNReal.toReal_mono
      (ENNReal.add_ne_top.mpr ⟨measure_ne_top μ _, measure_ne_top μ _⟩) h1
    rw [ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _)] at h2
    linarith
  have hcond : ((ProbabilityTheory.cond μ B) A).toReal = x / b := by
    rw [ProbabilityTheory.cond_apply hB, ENNReal.toReal_mul,
      ENNReal.toReal_inv, hbdef, hxdef, div_eq_inv_mul]
  rw [hcond, abs_le]
  constructor
  · have hxle : x ≤ x / b := by
      rw [le_div_iff₀ hb0]
      nlinarith
    linarith
  · have hup : x / b - x = x * (1 - b) / b := by
      field_simp
    have : x / b - x ≤ 1 - b := by
      rw [hup, div_le_iff₀ hb0]
      nlinarith
    linarith

/-- Testing the conditioning event attains the bound. -/
theorem abs_toReal_cond_sub_self (μ : Measure Ω) [IsProbabilityMeasure μ]
    {B : Set Ω} (hBpos : μ B ≠ 0) :
    |((ProbabilityTheory.cond μ B) B).toReal - (μ B).toReal| =
      1 - (μ B).toReal := by
  have hBne : μ B ≠ ⊤ := measure_ne_top μ B
  have hb1 : (μ B).toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono (measure_ne_top μ univ) (measure_mono (subset_univ B))
  have hself : (ProbabilityTheory.cond μ B) B = 1 :=
    ProbabilityTheory.cond_apply_self hBpos hBne
  rw [hself, ENNReal.toReal_one, abs_of_nonneg (by linarith)]

/-! ## The amplification contrast on a nested pair -/

section Nested

variable (μ : Measure Ω) [IsProbabilityMeasure μ]
variable {B C : Set Ω}

omit [IsProbabilityMeasure μ] in
theorem cond_apply_of_subset (hB : MeasurableSet B) (hCB : C ⊆ B) :
    (ProbabilityTheory.cond μ B) C = (μ B)⁻¹ * μ C := by
  rw [ProbabilityTheory.cond_apply hB, inter_eq_right.mpr hCB]

omit [IsProbabilityMeasure μ] in
theorem toReal_cond_apply_of_subset (hB : MeasurableSet B) (hCB : C ⊆ B) :
    ((ProbabilityTheory.cond μ B) C).toReal = (μ C).toReal / (μ B).toReal := by
  rw [cond_apply_of_subset μ hB hCB, ENNReal.toReal_mul, ENNReal.toReal_inv,
    div_eq_inv_mul]

/-- **Normalized states stay a fixed distance apart.**  Conditioning further,
from `B` down to a nested `C`, displaces the state by exactly the complementary
*ratio* `1 - μ C / μ B`, not by the mass difference. -/
theorem abs_toReal_cond_sub_cond_le (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hCB : C ⊆ B) (hBpos : μ B ≠ 0) (hCpos : μ C ≠ 0) (A : Set Ω) :
    |((ProbabilityTheory.cond μ C) A).toReal -
        ((ProbabilityTheory.cond μ B) A).toReal| ≤
      1 - (μ C).toReal / (μ B).toReal := by
  have hBne : μ B ≠ ⊤ := measure_ne_top μ B
  haveI : IsProbabilityMeasure (ProbabilityTheory.cond μ B) :=
    ProbabilityTheory.cond_isProbabilityMeasure hBpos
  have hCcond : (ProbabilityTheory.cond μ B) C ≠ 0 := by
    rw [cond_apply_of_subset μ hB hCB]
    exact mul_ne_zero (ENNReal.inv_ne_zero.mpr hBne) hCpos
  have hchain : ProbabilityTheory.cond (ProbabilityTheory.cond μ B) C =
      ProbabilityTheory.cond μ C := by
    rw [ProbabilityTheory.cond_cond_eq_cond_inter hB hC,
      inter_eq_right.mpr hCB]
  have hmain :=
    abs_toReal_cond_sub_le (ProbabilityTheory.cond μ B) hC hCcond A
  rw [hchain, toReal_cond_apply_of_subset μ hB hCB] at hmain
  exact hmain

theorem abs_toReal_cond_sub_cond_self (hB : MeasurableSet B)
    (hC : MeasurableSet C) (hCB : C ⊆ B) (hBpos : μ B ≠ 0) (hCpos : μ C ≠ 0) :
    |((ProbabilityTheory.cond μ C) C).toReal -
        ((ProbabilityTheory.cond μ B) C).toReal| =
      1 - (μ C).toReal / (μ B).toReal := by
  have hBne : μ B ≠ ⊤ := measure_ne_top μ B
  haveI : IsProbabilityMeasure (ProbabilityTheory.cond μ B) :=
    ProbabilityTheory.cond_isProbabilityMeasure hBpos
  have hCcond : (ProbabilityTheory.cond μ B) C ≠ 0 := by
    rw [cond_apply_of_subset μ hB hCB]
    exact mul_ne_zero (ENNReal.inv_ne_zero.mpr hBne) hCpos
  have hchain : ProbabilityTheory.cond (ProbabilityTheory.cond μ B) C =
      ProbabilityTheory.cond μ C := by
    rw [ProbabilityTheory.cond_cond_eq_cond_inter hB hC,
      inter_eq_right.mpr hCB]
  have hmain :=
    abs_toReal_cond_sub_self (ProbabilityTheory.cond μ B) hCcond
  rw [hchain] at hmain
  rw [toReal_cond_apply_of_subset μ hB hCB] at hmain ⊢
  exact hmain

/-- **Unnormalized restrictions move only by the mass difference.**  This is the
quantity that telescopes along a decreasing family, in contrast with the ratio
above. -/
theorem toReal_restrict_sub_restrict_le (hB : MeasurableSet B)
    (hC : MeasurableSet C) (hCB : C ⊆ B) (A : Set Ω) :
    (μ.restrict B A).toReal - (μ.restrict C A).toReal ≤
      (μ B).toReal - (μ C).toReal := by
  have hBA : μ.restrict B A = μ (A ∩ B) := Measure.restrict_apply' hB
  have hCA : μ.restrict C A = μ (A ∩ C) := Measure.restrict_apply' hC
  have hsplit : μ (A ∩ B) ≤ μ (A ∩ C) + (μ B - μ C) := by
    have hcover : A ∩ B ⊆ (A ∩ C) ∪ (B \ C) := by
      intro ω hω
      by_cases hc : ω ∈ C
      · exact Or.inl ⟨hω.1, hc⟩
      · exact Or.inr ⟨hω.2, hc⟩
    refine le_trans (measure_mono hcover) (le_trans (measure_union_le _ _) ?_)
    rw [measure_sdiff hCB hC.nullMeasurableSet (measure_ne_top μ C)]
  have hCle : μ C ≤ μ B := measure_mono hCB
  have h := ENNReal.toReal_mono
    (by
      refine ENNReal.add_ne_top.mpr ⟨measure_ne_top μ _, ?_⟩
      exact ne_top_of_le_ne_top (measure_ne_top μ B) tsub_le_self) hsplit
  rw [ENNReal.toReal_add (measure_ne_top μ _)
      (ne_top_of_le_ne_top (measure_ne_top μ B) tsub_le_self),
    ENNReal.toReal_sub_of_le hCle (measure_ne_top μ B)] at h
  rw [hBA, hCA]
  linarith

omit [IsProbabilityMeasure μ] in
theorem toReal_restrict_sub_restrict_self (hB : MeasurableSet B)
    (hC : MeasurableSet C) (hCB : C ⊆ B) :
    (μ.restrict B B).toReal - (μ.restrict C B).toReal =
      (μ B).toReal - (μ C).toReal := by
  rw [Measure.restrict_apply' hB, Measure.restrict_apply' hC,
    inter_self, inter_eq_right.mpr hCB]

end Nested

end GaloisForLFunctions.HTGeometry
