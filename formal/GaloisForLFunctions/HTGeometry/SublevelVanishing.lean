/-
# Sublevel sets shrink to the zero set

If a measurable function has a null zero set, its sublevel sets `{|f| ≤ g}` have measure tending to
zero as `g ↓ 0`, because they decrease to the zero set and the measure is finite.  For a finite
family the same holds simultaneously, by a union bound over the family.

This is the mechanism behind a transversality tail: the discarded region of a stationary-phase
estimate is a sublevel set of the phase gradient, and it is small exactly because the critical set
is null.

Main results:
* `exists_small_sublevel` — one function.
* `exists_small_finite_sublevel` — a finite family, simultaneously.
* `exists_small_transversalityTail` — the two-parameter form: a discriminant sublevel set and a
  gradient sublevel set, chosen in that order.
-/
import GaloisForLFunctions.HTGeometry.GridUnionOnset

open MeasureTheory Filter Topology

namespace GaloisForLFunctions.HTGeometry

variable {X : Type*} [MeasurableSpace X]

/-- **Sublevel sets of a function with null zero set are eventually small.** -/
theorem exists_small_sublevel (μ : Measure X) [IsFiniteMeasure μ] {f : X → ℝ}
    (hf : Measurable f) (hnull : μ {x | f x = 0} = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℝ, 0 < g ∧ μ.real {x | |f x| ≤ g} < ε := by
  set S : ℕ → Set X := fun n => {x | |f x| ≤ 1 / ((n : ℝ) + 1)} with hS
  have hmeas : ∀ n, MeasurableSet (S n) := fun n => measurableSet_le hf.abs measurable_const
  have hanti : Antitone S := by
    intro a b hab x hx
    have hx' : |f x| ≤ 1 / ((b : ℝ) + 1) := hx
    show |f x| ≤ 1 / ((a : ℝ) + 1)
    refine le_trans hx' ?_
    have ha : (0 : ℝ) < (a : ℝ) + 1 := by positivity
    have hle : (a : ℝ) + 1 ≤ (b : ℝ) + 1 := by
      have : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
      linarith
    exact one_div_le_one_div_of_le ha hle
  have hinter : (⋂ n, S n) = {x | f x = 0} := by
    ext x
    constructor
    · intro hx
      have hall : ∀ n : ℕ, |f x| ≤ 1 / ((n : ℝ) + 1) := fun n => Set.mem_iInter.mp hx n
      have h0 : |f x| ≤ 0 :=
        ge_of_tendsto tendsto_one_div_add_atTop_nhds_zero_nat (Eventually.of_forall hall)
      exact abs_nonpos_iff.mp h0
    · intro hx
      refine Set.mem_iInter.mpr fun n => ?_
      have hxz : f x = 0 := hx
      show |f x| ≤ 1 / ((n : ℝ) + 1)
      rw [hxz, abs_zero]
      positivity
  have hlim : Tendsto (fun n => μ (S n)) atTop (nhds (μ (⋂ n, S n))) :=
    tendsto_measure_iInter_atTop (fun n => (hmeas n).nullMeasurableSet) hanti
      ⟨0, measure_ne_top μ _⟩
  rw [hinter, hnull] at hlim
  have hev : ∀ᶠ n in atTop, μ (S n) < ENNReal.ofReal ε :=
    hlim.eventually (gt_mem_nhds (by simpa using ENNReal.ofReal_pos.mpr hε))
  obtain ⟨n, hn⟩ := hev.exists
  refine ⟨1 / ((n : ℝ) + 1), by positivity, ?_⟩
  exact ENNReal.toReal_lt_of_lt_ofReal hn

/-- **A finite family, simultaneously.** -/
theorem exists_small_finite_sublevel (μ : Measure X) [IsFiniteMeasure μ] {K : Type*} [Fintype K]
    {h : K → X → ℝ} (hmeas : ∀ k, Measurable (h k)) (hnull : ∀ k, μ {x | h k x = 0} = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℝ, 0 < g ∧ μ.real {x | ∃ k, |h k x| ≤ g} < ε := by
  classical
  rcases isEmpty_or_nonempty K with hK | hK
  · refine ⟨1, one_pos, ?_⟩
    have hempty : {x : X | ∃ k : K, |h k x| ≤ 1} = ∅ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists]
      exact fun k => (IsEmpty.false k).elim
    rw [hempty]
    simpa using hε
  haveI : Nonempty K := hK
  have hcardpos : (0 : ℝ) < (Fintype.card K : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr hK
  have hcard : (Fintype.card K : ℝ) ≠ 0 := hcardpos.ne'
  have hpos : (0 : ℝ) < ε / (Fintype.card K : ℝ) := by positivity
  choose gk hgk hgkbound using fun k => exists_small_sublevel μ (hmeas k) (hnull k) hpos
  obtain ⟨k₀⟩ := hK
  refine ⟨Finset.univ.inf' ⟨k₀, Finset.mem_univ k₀⟩ gk, ?_, ?_⟩
  · exact (Finset.lt_inf'_iff _).mpr fun k _ => hgk k
  · have hsub : {x : X | ∃ k, |h k x| ≤ Finset.univ.inf' ⟨k₀, Finset.mem_univ k₀⟩ gk}
        ⊆ ⋃ k, {x : X | |h k x| ≤ gk k} := by
      rintro x ⟨k, hk⟩
      exact Set.mem_iUnion.mpr ⟨k, le_trans hk (Finset.inf'_le _ (Finset.mem_univ k))⟩
    calc μ.real {x : X | ∃ k, |h k x| ≤ Finset.univ.inf' ⟨k₀, Finset.mem_univ k₀⟩ gk}
        ≤ μ.real (⋃ k, {x : X | |h k x| ≤ gk k}) := measureReal_mono hsub
      _ ≤ ∑ k, μ.real {x : X | |h k x| ≤ gk k} := measureReal_iUnion_fintype_le _
      _ < ε := by
          calc ∑ k, μ.real {x : X | |h k x| ≤ gk k}
              < ∑ _k : K, ε / (Fintype.card K : ℝ) :=
                Finset.sum_lt_sum_of_nonempty ⟨k₀, Finset.mem_univ k₀⟩ fun k _ => hgkbound k
            _ = ε := by
                rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
                field_simp

/-- **The transversality tail vanishes.**  A discriminant with null zero set and a finite family of
gradient norms with null critical sets can be cut simultaneously: for every tolerance there are a
discriminant threshold and a gradient threshold whose two discarded regions together weigh less
than the tolerance. -/
theorem exists_small_transversalityTail (μ : Measure X) [IsFiniteMeasure μ]
    {D : X → ℝ} (hD : Measurable D) (hDnull : μ {x | D x = 0} = 0)
    {K : Type*} [Fintype K] {h : K → X → ℝ} (hmeas : ∀ k, Measurable (h k))
    (hnull : ∀ k, μ {x | h k x = 0} = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ ζ g : ℝ, 0 < ζ ∧ 0 < g ∧
      μ.real {x | |D x| ≤ ζ} + μ.real {x | ∃ k, |h k x| ≤ g} < ε := by
  obtain ⟨ζ, hζ, hζb⟩ := exists_small_sublevel μ hD hDnull (half_pos hε)
  obtain ⟨g, hg, hgb⟩ := exists_small_finite_sublevel μ hmeas hnull (half_pos hε)
  refine ⟨ζ, g, hζ, hg, ?_⟩
  linarith

end GaloisForLFunctions.HTGeometry
