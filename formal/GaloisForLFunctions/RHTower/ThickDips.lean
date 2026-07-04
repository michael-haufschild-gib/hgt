/-
Doc 72 §3 (the width-refined counting — the zero-floor dodge), machine-checked.

Wall 1 of doc 72: every on-line ζ-zero forces |ζ(½+it)| ≤ λ on an interval of
width ≈ 2λ/|ζ′(γ)| — a LINEAR-in-λ "floor" in the small-ball measure that
dominates the lognormal tail at the design threshold and would consume the
whole creation budget. The dodge is structural: sliver-zero dips are WIDE
(the dip lemma guarantees measure ≥ h inside a 2h-interval), floor dips are
THIN (≪ h), so counting against the h-locally-thick part of the sublevel set
excludes the floor at an O(1) cost:

* `thickPart` — the h-locally-thick part of a set: points whose 4h-window
  holds at least h of the set.
* `mem_thickPart_of_dip` — a dip interval lies inside the thick part.
* `thick_dips_count_le` — the counting bridge, upgraded: 3h-separated dip
  centers number at most volume(E ∩ thickPart E h)/h. NO measurability of E
  is needed (the proof runs through `volume.restrict` at an arbitrary set).
* `lintegral_window_mass` / `measurable_window_mass` — Fubini value and
  measurability of the window-mass function t ↦ volume(A ∩ [t±c]).
* `thickPart_union_measure_le` — the floor-exclusion Markov bound: if E ⊆
  A ∪ B with per-window B-mass ≤ h/2 (B = the thin floor), then
  volume(thickPart (A ∪ B) h) ≤ 8·volume A — the budget sees only the
  tail part A, at the cost of a factor 8.
-/
import Mathlib
import GaloisForLFunctions.RHTower.MollifiedDip

namespace RHTower

open MeasureTheory Set

/-- The `h`-locally-thick part of a set: points whose `4h`-window holds at
least `h` of the set's measure. Sliver-zero dips land here (dip lemma);
thin zero-floor dips do not. -/
def thickPart (E : Set ℝ) (h : ℝ) : Set ℝ :=
  {t | ENNReal.ofReal h ≤ volume (E ∩ Icc (t - 2 * h) (t + 2 * h))}

/-- A point of a dip interval is `h`-locally thick: its `4h`-window contains
the whole dip interval, hence at least `h` of `E`. -/
theorem mem_thickPart_of_dip {E : Set ℝ} {h γ t : ℝ}
    (hdip : ENNReal.ofReal h ≤ volume (E ∩ Icc (γ - h) (γ + h)))
    (htI : t ∈ Icc (γ - h) (γ + h)) : t ∈ thickPart E h := by
  refine le_trans hdip (measure_mono (inter_subset_inter_right E ?_))
  intro u hu
  exact ⟨by linarith [htI.2, hu.1], by linarith [htI.1, hu.2]⟩

/-- **The width-refined counting bridge (doc 72 §3).** `3h`-separated dip
centers, each contributing measure `≥ h` of `E` inside its `h`-interval,
number at most `volume (E ∩ thickPart E h) / h` — the sublevel measure
OUTSIDE the thick part (the thin zero-floor) never enters the count. No
measurability of `E` is required. -/
theorem thick_dips_count_le {E : Set ℝ} {h : ℝ} (hh : 0 < h) (S : Finset ℝ)
    (hsep : (↑S : Set ℝ).Pairwise fun x y => 3 * h ≤ |x - y|)
    (hdip : ∀ γ ∈ S, ENNReal.ofReal h ≤ volume (E ∩ Icc (γ - h) (γ + h))) :
    (S.card : ENNReal) * ENNReal.ofReal h ≤ volume (E ∩ thickPart E h) := by
  set X := E ∩ thickPart E h with hX
  have hdisj : (↑S : Set ℝ).PairwiseDisjoint
      (fun γ => Icc (γ - h) (γ + h)) := by
    intro x hx y hy hxy
    exact gapped_Icc_disjoint hh (hsep hx hy hxy)
  have key : ∀ γ ∈ S,
      ENNReal.ofReal h ≤ (volume.restrict X) (Icc (γ - h) (γ + h)) := by
    intro γ hγ
    rw [Measure.restrict_apply measurableSet_Icc]
    refine (hdip γ hγ).trans (measure_mono ?_)
    rintro t ⟨htE, htI⟩
    exact ⟨htI, htE, mem_thickPart_of_dip (hdip γ hγ) htI⟩
  calc (S.card : ENNReal) * ENNReal.ofReal h
      = ∑ _γ ∈ S, ENNReal.ofReal h := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ γ ∈ S, (volume.restrict X) (Icc (γ - h) (γ + h)) :=
        Finset.sum_le_sum key
    _ = (volume.restrict X) (⋃ γ ∈ S, Icc (γ - h) (γ + h)) :=
        (measure_biUnion_finset hdisj fun _ _ => measurableSet_Icc).symm
    _ ≤ (volume.restrict X) univ := measure_mono (subset_univ _)
    _ = volume X := Measure.restrict_apply_univ _

section WindowMass

/-- Pointwise identity: the product of the `A`-indicator at `u` and the
symmetric-window indicator equals the indicator of `A ∩ [t±c]` at `u`. -/
private theorem indicator_window_eq (A : Set ℝ) (c t u : ℝ) :
    (A.indicator (1 : ℝ → ENNReal) u) *
      ((Icc (u - c) (u + c)).indicator (1 : ℝ → ENNReal) t)
    = (A ∩ Icc (t - c) (t + c)).indicator 1 u := by
  have hwin : ((Icc (u - c) (u + c)).indicator (1 : ℝ → ENNReal) t)
      = ((Icc (t - c) (t + c)).indicator (1 : ℝ → ENNReal) u) := by
    simp only [Set.indicator_apply, mem_Icc, Pi.one_apply]
    by_cases hm : u - c ≤ t ∧ t ≤ u + c
    · rw [if_pos hm, if_pos ⟨by linarith [hm.2], by linarith [hm.1]⟩]
    · rw [if_neg hm, if_neg fun hc2 => hm ⟨by linarith [hc2.2], by linarith [hc2.1]⟩]
  rw [hwin, ← Set.inter_indicator_mul]
  simp only [Pi.one_apply, one_mul]
  rfl

/-- Window-mass as a `lintegral` of a product of indicators. -/
private theorem window_mass_eq_lintegral {A : Set ℝ} (hA : MeasurableSet A)
    (c t : ℝ) : volume (A ∩ Icc (t - c) (t + c))
      = ∫⁻ u, (A.indicator (1 : ℝ → ENNReal) u) *
          ((Icc (u - c) (u + c)).indicator (1 : ℝ → ENNReal) t) := by
  simp_rw [indicator_window_eq A c t]
  rw [lintegral_indicator (hA.inter measurableSet_Icc)]
  simp

/-- The window-mass function `t ↦ volume (A ∩ [t±c])` is measurable. -/
theorem measurable_window_mass {A : Set ℝ} (hA : MeasurableSet A) (c : ℝ) :
    Measurable fun t : ℝ => volume (A ∩ Icc (t - c) (t + c)) := by
  have hset : MeasurableSet {p : ℝ × ℝ | p.2 - c ≤ p.1 ∧ p.1 ≤ p.2 + c} :=
    ((measurableSet_le (measurable_snd.sub measurable_const) measurable_fst).inter
      (measurableSet_le measurable_fst (measurable_snd.add measurable_const)))
  have hf : Measurable fun p : ℝ × ℝ =>
      (A.indicator (1 : ℝ → ENNReal) p.2) *
      ({p : ℝ × ℝ | p.2 - c ≤ p.1 ∧ p.1 ≤ p.2 + c}.indicator 1 p) :=
    ((measurable_one.indicator hA).comp measurable_snd).mul
      (measurable_one.indicator hset)
  have key : ∀ t : ℝ, volume (A ∩ Icc (t - c) (t + c))
      = ∫⁻ u, (A.indicator (1 : ℝ → ENNReal) u) *
          ({p : ℝ × ℝ | p.2 - c ≤ p.1 ∧ p.1 ≤ p.2 + c}.indicator 1 (t, u)) := by
    intro t
    rw [window_mass_eq_lintegral hA c t]
    exact lintegral_congr fun u => rfl
  simp_rw [key]
  exact hf.lintegral_prod_right

/-- **Fubini value of the window mass:**
`∫⁻ t, volume (A ∩ [t±c]) dt = (2c)·volume A`. -/
theorem lintegral_window_mass {A : Set ℝ} (hA : MeasurableSet A) (c : ℝ) :
    ∫⁻ t : ℝ, volume (A ∩ Icc (t - c) (t + c))
      = ENNReal.ofReal (2 * c) * volume A := by
  simp_rw [fun t => window_mass_eq_lintegral hA c t]
  rw [lintegral_lintegral_swap]
  · have inner : ∀ u : ℝ,
        (∫⁻ t, (A.indicator (1 : ℝ → ENNReal) u) *
          ((Icc (u - c) (u + c)).indicator (1 : ℝ → ENNReal) t))
        = (A.indicator (1 : ℝ → ENNReal) u) * ENNReal.ofReal (2 * c) := by
      intro u
      rw [lintegral_const_mul' _ _ (by
        by_cases hu : u ∈ A <;> simp [hu])]
      congr 1
      rw [lintegral_indicator measurableSet_Icc]
      simp only [Pi.one_apply, MeasureTheory.setLIntegral_one]
      rw [Real.volume_Icc, show u + c - (u - c) = 2 * c by ring]
    simp_rw [inner]
    rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
    rw [lintegral_indicator hA]
    simp only [Pi.one_apply, MeasureTheory.setLIntegral_one]
    exact mul_comm _ _
  · apply Measurable.aemeasurable
    have hset : MeasurableSet {p : ℝ × ℝ | p.1 - c ≤ p.2 ∧ p.2 ≤ p.1 + c} :=
      ((measurableSet_le (measurable_fst.sub measurable_const) measurable_snd).inter
        (measurableSet_le measurable_snd (measurable_fst.add measurable_const)))
    show Measurable fun p : ℝ × ℝ => (A.indicator (1 : ℝ → ENNReal) p.2) *
        ((Icc (p.2 - c) (p.2 + c)).indicator (1 : ℝ → ENNReal) p.1)
    have heq : (fun p : ℝ × ℝ => (A.indicator (1 : ℝ → ENNReal) p.2) *
        ((Icc (p.2 - c) (p.2 + c)).indicator (1 : ℝ → ENNReal) p.1))
        = fun p : ℝ × ℝ => (A.indicator (1 : ℝ → ENNReal) p.2) *
        ({q : ℝ × ℝ | q.1 - c ≤ q.2 ∧ q.2 ≤ q.1 + c}.indicator 1 (p.2, p.1)) :=
      funext fun p => rfl
    rw [heq]
    exact ((measurable_one.indicator hA).comp measurable_snd).mul
      ((measurable_one.indicator hset).comp (measurable_snd.prodMk measurable_fst))

end WindowMass

/-- If the thin part `B` carries at most `h/2` mass in every `4h`-window,
then any `h`-thick point of `A ∪ B` is an `(h/2)`-thick point of `A`. -/
theorem thickPart_union_subset {A B : Set ℝ} {h : ℝ} (hh : 0 < h)
    (hB : ∀ t : ℝ, volume (B ∩ Icc (t - 2 * h) (t + 2 * h))
      ≤ ENNReal.ofReal (h / 2)) :
    thickPart (A ∪ B) h ⊆
      {t | ENNReal.ofReal (h / 2) ≤ volume (A ∩ Icc (t - 2 * h) (t + 2 * h))} := by
  intro t ht
  have hsplit : volume ((A ∪ B) ∩ Icc (t - 2 * h) (t + 2 * h))
      ≤ volume (A ∩ Icc (t - 2 * h) (t + 2 * h))
        + volume (B ∩ Icc (t - 2 * h) (t + 2 * h)) := by
    rw [union_inter_distrib_right]
    exact measure_union_le _ _
  have h1 : ENNReal.ofReal (h / 2) + ENNReal.ofReal (h / 2)
      ≤ volume (A ∩ Icc (t - 2 * h) (t + 2 * h)) + ENNReal.ofReal (h / 2) := by
    have hsum : ENNReal.ofReal (h / 2) + ENNReal.ofReal (h / 2)
        = ENNReal.ofReal h := by
      rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
      norm_num
    calc ENNReal.ofReal (h / 2) + ENNReal.ofReal (h / 2)
        = ENNReal.ofReal h := hsum
      _ ≤ volume ((A ∪ B) ∩ Icc (t - 2 * h) (t + 2 * h)) := ht
      _ ≤ _ := hsplit.trans (add_le_add le_rfl (hB t))
  exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).mp h1

/-- **The floor-exclusion bound (doc 72 §3).** If the sublevel set decomposes
as `A ∪ B` (tail ∪ thin floor) with per-`4h`-window floor mass `≤ h/2`, the
thick part is measured by the TAIL alone, at cost 8:
`volume (thickPart (A ∪ B) h) ≤ 8 · volume A`. -/
theorem thickPart_union_measure_le {A B : Set ℝ} (hA : MeasurableSet A)
    {h : ℝ} (hh : 0 < h)
    (hB : ∀ t : ℝ, volume (B ∩ Icc (t - 2 * h) (t + 2 * h))
      ≤ ENNReal.ofReal (h / 2)) :
    volume (thickPart (A ∪ B) h) ≤ 8 * volume A := by
  have hg := measurable_window_mass hA (2 * h)
  have step1 : volume (thickPart (A ∪ B) h)
      ≤ volume {t : ℝ | ENNReal.ofReal (h / 2)
          ≤ volume (A ∩ Icc (t - 2 * h) (t + 2 * h))} :=
    measure_mono (thickPart_union_subset hh hB)
  have step2 : volume {t : ℝ | ENNReal.ofReal (h / 2)
        ≤ volume (A ∩ Icc (t - 2 * h) (t + 2 * h))}
      ≤ (∫⁻ t, volume (A ∩ Icc (t - 2 * h) (t + 2 * h)))
          / ENNReal.ofReal (h / 2) :=
    meas_ge_le_lintegral_div hg.aemeasurable
      (by simp [ENNReal.ofReal_eq_zero]; linarith) ENNReal.ofReal_ne_top
  have hfub := lintegral_window_mass hA (2 * h)
  have step3 : (∫⁻ t, volume (A ∩ Icc (t - 2 * h) (t + 2 * h)))
      / ENNReal.ofReal (h / 2) = 8 * volume A := by
    rw [hfub, div_eq_mul_inv, mul_right_comm]
    congr 1
    rw [← div_eq_mul_inv, ← ENNReal.ofReal_div_of_pos (by linarith),
      show (2 * (2 * h)) / (h / 2) = 8 by
        have hne : h ≠ 0 := ne_of_gt hh
        field_simp
        ring]
    norm_num
  exact step1.trans (step2.trans step3.le)

end RHTower
