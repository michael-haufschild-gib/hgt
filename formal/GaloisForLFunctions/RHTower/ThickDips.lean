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

/-! Doc 74 §5 harvest: the parametric thickness constant (the crude `h/2`
split of `thickPart_union_measure_le` cost a factor 8; with the measured
thin-mass fraction β ≈ 0.006 per window, the sharp split costs 4/(1−β) ≈ 4)
and the elementary polynomial tail bound (the unconditional half of the
Christoffel–Markov mechanism of doc 73 §3). -/

namespace RHTower

open MeasureTheory Set

/-- Parametric split: if the thin part `B` carries at most `β·h` mass in
every `4h`-window, an `h`-thick point of `A ∪ B` is a `((1−β)h)`-thick
point of `A`. -/
theorem thickPart_union_subset' {A B : Set ℝ} {h β : ℝ} (hβh2 : 0 ≤ β * h)
    (hβh : 0 ≤ (1 - β) * h)
    (hB : ∀ t : ℝ, volume (B ∩ Icc (t - 2 * h) (t + 2 * h))
      ≤ ENNReal.ofReal (β * h)) :
    thickPart (A ∪ B) h ⊆
      {t | ENNReal.ofReal ((1 - β) * h)
        ≤ volume (A ∩ Icc (t - 2 * h) (t + 2 * h))} := by
  intro t ht
  have hsplit : volume ((A ∪ B) ∩ Icc (t - 2 * h) (t + 2 * h))
      ≤ volume (A ∩ Icc (t - 2 * h) (t + 2 * h))
        + volume (B ∩ Icc (t - 2 * h) (t + 2 * h)) := by
    rw [union_inter_distrib_right]
    exact measure_union_le _ _
  have hsum : ENNReal.ofReal ((1 - β) * h) + ENNReal.ofReal (β * h)
      = ENNReal.ofReal h := by
    rw [← ENNReal.ofReal_add hβh hβh2]
    congr 1
    ring
  have h1 : ENNReal.ofReal ((1 - β) * h) + ENNReal.ofReal (β * h)
      ≤ volume (A ∩ Icc (t - 2 * h) (t + 2 * h)) + ENNReal.ofReal (β * h) :=
    hsum.le.trans (ht.trans (hsplit.trans (add_le_add le_rfl (hB t))))
  exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).mp h1

/-- **The harvested floor-exclusion bound (doc 74 §5).** With per-window
thin mass `≤ β·h`, the thick part of `A ∪ B` is measured by the tail alone
at cost `4/(1−β)` — replacing the factor 8 of `thickPart_union_measure_le`
(which is the case `β = 1/2`). At the measured β ≈ 0.006 the cost is ≈ 4. -/
theorem thickPart_union_measure_le' {A B : Set ℝ} (hA : MeasurableSet A)
    {h β : ℝ} (hh : 0 < h) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hB : ∀ t : ℝ, volume (B ∩ Icc (t - 2 * h) (t + 2 * h))
      ≤ ENNReal.ofReal (β * h)) :
    volume (thickPart (A ∪ B) h) ≤ ENNReal.ofReal (4 / (1 - β)) * volume A := by
  have hbh : 0 < (1 - β) * h := by
    have : 0 < 1 - β := by linarith
    positivity
  have hg := measurable_window_mass hA (2 * h)
  have step1 : volume (thickPart (A ∪ B) h)
      ≤ volume {t : ℝ | ENNReal.ofReal ((1 - β) * h)
          ≤ volume (A ∩ Icc (t - 2 * h) (t + 2 * h))} :=
    measure_mono (thickPart_union_subset' (by positivity) hbh.le hB)
  have step2 : volume {t : ℝ | ENNReal.ofReal ((1 - β) * h)
        ≤ volume (A ∩ Icc (t - 2 * h) (t + 2 * h))}
      ≤ (∫⁻ t, volume (A ∩ Icc (t - 2 * h) (t + 2 * h)))
          / ENNReal.ofReal ((1 - β) * h) :=
    meas_ge_le_lintegral_div hg.aemeasurable
      (by simp [ENNReal.ofReal_eq_zero]; linarith) ENNReal.ofReal_ne_top
  have hfub := lintegral_window_mass hA (2 * h)
  have step3 : (∫⁻ t, volume (A ∩ Icc (t - 2 * h) (t + 2 * h)))
      / ENNReal.ofReal ((1 - β) * h)
      = ENNReal.ofReal (4 / (1 - β)) * volume A := by
    rw [hfub, div_eq_mul_inv, mul_right_comm]
    congr 1
    rw [← div_eq_mul_inv, ← ENNReal.ofReal_div_of_pos hbh,
      show (2 * (2 * h)) / ((1 - β) * h) = 4 / (1 - β) by
        have hne : h ≠ 0 := ne_of_gt hh
        have hbne : (1 : ℝ) - β ≠ 0 := by intro hz; rw [sub_eq_zero] at hz; linarith [hβ1, hz]
        field_simp
        ring]
  exact step1.trans (step2.trans step3.le)

/-- **The elementary tail bound behind Christoffel–Markov (doc 73 §3).**
For any function whose square is ≥ 1 on the tail ray, the tail measure is
bounded by the integral of the square — with `f = q.eval` for a certified
polynomial `q`, the right side is a finite quadratic form in the moment
ladder. The sharp Krein version (1/K_n) is the promotion target; this
unconditional half already certifies any table entry once `q² ≥ 1` on the
ray is checked. -/
theorem sq_tail_bound (μ : Measure ℝ) (f : ℝ → ℝ) (a : ℝ)
    (hf : ∀ x ≤ -a, 1 ≤ (f x) ^ 2) :
    μ {x | x ≤ -a} ≤ ∫⁻ x, ENNReal.ofReal ((f x) ^ 2) ∂μ := by
  have hS : MeasurableSet {x : ℝ | x ≤ -a} := measurableSet_Iic
  have h1 : μ {x | x ≤ -a}
      = ∫⁻ x, ({x : ℝ | x ≤ -a}).indicator 1 x ∂μ := by
    rw [lintegral_indicator hS]
    simp
  rw [h1]
  refine lintegral_mono fun x => ?_
  rw [Set.indicator_apply]
  split_ifs with hx
  · simpa using ENNReal.one_le_ofReal.mpr (hf x hx)
  · exact bot_le

/-- **The certified-tail consumable, fully proven.** Given the ray
condition `q² ≥ 1` on `(−∞, −a]` and a certified bound `M` on the
`q²`-moment of `μ` (in applications: the quadratic form of `q` against the
spacing-MV moment ladder of doc 73 §1), the tail measure is at most `M`.
Machine-checks any entry of the doc 73 §3 table once its polynomial and
moment bound are supplied. -/
theorem sq_tail_bound_of_moment (μ : Measure ℝ) (f : ℝ → ℝ) (a M : ℝ)
    (hf : ∀ x ≤ -a, 1 ≤ (f x) ^ 2)
    (hM : (∫⁻ x, ENNReal.ofReal ((f x) ^ 2) ∂μ) ≤ ENNReal.ofReal M) :
    μ {x | x ≤ -a} ≤ ENNReal.ofReal M :=
  (sq_tail_bound μ f a hf).trans hM

end RHTower

namespace RHTower

open MeasureTheory Set

/-- **Width-refined average-to-count endpoint.** Per-center average dips land in the
thick part of the sublevel set; if that sublevel set is contained in a tail part
`A` plus a thin floor `B`, the floor-exclusion estimate prices the count by the
tail kernel alone. -/
theorem thickSliverCount_le_of_average_floor_kernel
    {h B2 L2 β C r U : ℝ} (hh : 0 < h) (hpos : 0 < B2 + 2 * h * L2)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hCU : 0 ≤ C * r ^ 2 * U)
    {f : ℝ → ℝ} (hf : Continuous f) (hnn : ∀ t, 0 ≤ f t) (S : Finset ℝ)
    (hsep : (↑S : Set ℝ).Pairwise fun x y => 3 * h ≤ |x - y|)
    (havg : ∀ γ ∈ S,
      ∫ t in Icc (γ - h) (γ + h), f t ≤ 2 * h * B2 + 4 * h ^ 2 * L2)
    {A B : Set ℝ} (hA : MeasurableSet A)
    (hsub : {t | f t ≤ 2 * (B2 + 2 * h * L2)} ⊆ A ∪ B)
    (hB : ∀ t : ℝ, volume (B ∩ Icc (t - 2 * h) (t + 2 * h))
      ≤ ENNReal.ofReal (β * h))
    (hker : volume A ≤ ENNReal.ofReal (C * r ^ 2 * U)) :
    (S.card : ℝ) * h ≤ (4 / (1 - β)) * (C * r ^ 2 * U) := by
  let E : Set ℝ := {t | f t ≤ 2 * (B2 + 2 * h * L2)}
  have hcost_nonneg : 0 ≤ 4 / (1 - β) := by positivity
  have hdip : ∀ γ ∈ S, ENNReal.ofReal h ≤ volume (E ∩ Icc (γ - h) (γ + h)) := by
    intro γ hγ
    have hmeasure := dip_measure_lower hh hpos hf hnn (havg γ hγ)
    have hset : {t ∈ Icc (γ - h) (γ + h) | f t ≤ 2 * (B2 + 2 * h * L2)}
        = E ∩ Icc (γ - h) (γ + h) := by
      ext t
      constructor
      · intro ht
        exact ⟨ht.2, ht.1⟩
      · intro ht
        exact ⟨ht.2, ht.1⟩
    rwa [hset] at hmeasure
  have hcount := thick_dips_count_le (E := E) hh S hsep hdip
  have hmono_thick : E ∩ thickPart E h ⊆ (A ∪ B) ∩ thickPart (A ∪ B) h := by
    intro t ht
    refine ⟨hsub ht.1, ?_⟩
    dsimp [thickPart] at ht ⊢
    refine ht.2.trans (measure_mono ?_)
    intro u hu
    exact ⟨hsub hu.1, hu.2⟩
  have hcount_tail : (S.card : ENNReal) * ENNReal.ofReal h
      ≤ volume (thickPart (A ∪ B) h) := by
    exact hcount.trans ((measure_mono hmono_thick).trans (measure_mono inter_subset_right))
  have hfloor := thickPart_union_measure_le' hA hh hβ0 hβ1 hB
  have htail : (S.card : ENNReal) * ENNReal.ofReal h
      ≤ ENNReal.ofReal (4 / (1 - β)) * volume A := hcount_tail.trans hfloor
  have hbound : (S.card : ENNReal) * ENNReal.ofReal h
      ≤ ENNReal.ofReal (4 / (1 - β)) * ENNReal.ofReal (C * r ^ 2 * U) :=
    htail.trans (mul_le_mul_right hker _)
  have hleft : ENNReal.ofReal ((S.card : ℝ) * h)
      = (S.card : ENNReal) * ENNReal.ofReal h := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
  have hright : ENNReal.ofReal ((4 / (1 - β)) * (C * r ^ 2 * U))
      = ENNReal.ofReal (4 / (1 - β)) * ENNReal.ofReal (C * r ^ 2 * U) := by
    rw [ENNReal.ofReal_mul hcost_nonneg]
  have hofReal : ENNReal.ofReal ((S.card : ℝ) * h)
      ≤ ENNReal.ofReal ((4 / (1 - β)) * (C * r ^ 2 * U)) := by
    rw [hleft, hright]
    exact hbound
  have hreal := ENNReal.toReal_le_of_le_ofReal (mul_nonneg hcost_nonneg hCU) hofReal
  rwa [ENNReal.toReal_ofReal (by positivity)] at hreal

end RHTower
