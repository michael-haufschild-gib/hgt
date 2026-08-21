import GaloisForLFunctions.HTGeometry.CompletedTimeBohrMean

/-!
# Completed occupation forces same-draw hard gaps

A target with small completed one-sided occupation cannot be visited with bounded gaps when every
visit has a fixed positive temporal thickness inside a wider target.  The result is deterministic:
it applies to one fixed orbit and therefore converts a completed-time capture bound into
arbitrarily late continuous hard intervals for that same orbit.
-/

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Completed occupation-to-hard-gap law.**  If every hit of `narrow` supplies an interval of
length `delta` inside `wide`, and the completed one-sided occupation of `wide` is at most `b`, then
`narrow` has arbitrarily late gaps of length `W` whenever `b < delta / (W + delta)`. -/
theorem exists_late_interval_disjoint_of_limsup_windowProbability_le
    (narrow wide : Set ℝ) {delta W b : ℝ}
    (hdelta : 0 < delta) (hW : 0 ≤ W) (hb : 0 ≤ b)
    (hthick : ∀ t ∈ narrow, Ioc t (t + delta) ⊆ wide)
    (hlim : atTop.limsup (fun T => (windowProbabilityMeasure T : Measure ℝ) wide)
      ≤ ENNReal.ofReal b)
    (hpack : b < delta / (W + delta)) :
    ∀ A0 : ℝ, 0 ≤ A0 → ∃ u : ℝ, A0 ≤ u ∧ Icc u (u + W) ∩ narrow = ∅ := by
  intro A0 hA0
  let S : ℝ := W + delta
  have hS : 0 < S := by dsimp [S]; linarith
  let c : ℝ := (b + delta / S) / 2
  have hbc : b < c := by dsimp [c]; nlinarith
  have hcpack : c < delta / S := by dsimp [c]; nlinarith
  have hcpos : 0 < c := lt_of_le_of_lt hb hbc
  have hlimlt : atTop.limsup
      (fun T => (windowProbabilityMeasure T : Measure ℝ) wide) < ENNReal.ofReal c :=
    lt_of_le_of_lt hlim ((ENNReal.ofReal_lt_ofReal_iff hcpos).2 hbc)
  have hevent : ∀ᶠ T : ℝ in atTop,
      (windowProbabilityMeasure T : Measure ℝ) wide < ENNReal.ofReal c :=
    eventually_lt_of_limsup_lt hlimlt
  obtain ⟨T0, hT0⟩ := eventually_atTop.1 hevent
  by_contra hgap
  push Not at hgap
  have hhit : ∀ u : ℝ, A0 ≤ u → ∃ t : ℝ, t ∈ Icc u (u + W) ∧ t ∈ narrow := by
    intro u hu
    obtain ⟨t, ht⟩ := hgap u hu
    exact ⟨t, ht.1, ht.2⟩
  have hblock (k : ℕ) : A0 ≤ A0 + k * S := by
    have : (0 : ℝ) ≤ (k : ℝ) * S := mul_nonneg (Nat.cast_nonneg _) hS.le
    linarith
  let hit : ℕ → ℝ := fun k => Classical.choose (hhit (A0 + k * S) (hblock k))
  have hit_mem (k : ℕ) : hit k ∈ Icc (A0 + k * S) (A0 + k * S + W) :=
    (Classical.choose_spec (hhit (A0 + k * S) (hblock k))).1
  have hit_narrow (k : ℕ) : hit k ∈ narrow :=
    (Classical.choose_spec (hhit (A0 + k * S) (hblock k))).2
  have hcgap : 0 < delta - c * S := by
    have := (lt_div_iff₀ hS).mp hcpack
    linarith
  obtain ⟨N, hN⟩ := exists_nat_gt
    (max 1 (max ((T0 - A0) / S) ((c * A0) / (delta - c * S))))
  have hN1 : (1 : ℝ) < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hNpos : (0 : ℝ) < N := lt_trans (by norm_num) hN1
  have hNtimeDiv : (T0 - A0) / S < N :=
    lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hNratioDiv : (c * A0) / (delta - c * S) < N :=
    lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hNtime : T0 ≤ A0 + N * S := by
    have := (div_lt_iff₀ hS).mp hNtimeDiv
    linarith
  have hNratio : c * (A0 + N * S) < N * delta := by
    have := (div_lt_iff₀ hcgap).mp hNratioDiv
    nlinarith
  have hTNpos : 0 < A0 + N * S := by positivity
  have hlate := hT0 (A0 + N * S) hNtime
  let cells : Fin N → Set ℝ := fun k => Ioc (hit k) (hit k + delta)
  have hcells_disjoint : Pairwise (Function.onFun Disjoint cells) := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with hijlt | hjilt
    · apply Ioc_disjoint_Ioc_of_le
      have hi := (hit_mem i).2
      have hj := (hit_mem j).1
      have hsucc : ((i : ℕ) + 1 : ℝ) ≤ (j : ℕ) := by exact_mod_cast hijlt
      dsimp [S] at hi hj ⊢
      nlinarith
    · exact (Ioc_disjoint_Ioc_of_le (by
        have hj := (hit_mem j).2
        have hi := (hit_mem i).1
        have hsucc : ((j : ℕ) + 1 : ℝ) ≤ (i : ℕ) := by exact_mod_cast hjilt
        dsimp [S] at hj hi ⊢
        nlinarith)).symm
  have hcells_sub : (⋃ k : Fin N, cells k) ⊆ wide ∩ Ioc 0 (A0 + N * S) := by
    intro x hx
    obtain ⟨k, hxk⟩ := Set.mem_iUnion.mp hx
    have hkW := (hit_mem k).2
    have hk0 := (hit_mem k).1
    have hkN : ((k : ℕ) + 1 : ℝ) ≤ N := by exact_mod_cast k.isLt
    constructor
    · exact hthick (hit k) (hit_narrow k) hxk
    · constructor
      · exact lt_of_le_of_lt (le_trans (le_trans hA0 (hblock k)) hk0) hxk.1
      · have hnext : hit k + delta ≤ A0 + ((k : ℕ) + 1) * S := by
          dsimp [S] at hkW ⊢
          nlinarith
        have hmul : (((k : ℕ) : ℝ) + 1) * S ≤ (N : ℝ) * S :=
          mul_le_mul_of_nonneg_right hkN hS.le
        have hshift : A0 + (((k : ℕ) : ℝ) + 1) * S ≤ A0 + (N : ℝ) * S := by
          simpa [add_comm] using add_le_add_left hmul A0
        exact le_trans hxk.2 (le_trans hnext hshift)
  have hvolume_cells : volume (⋃ k : Fin N, cells k) = ENNReal.ofReal (N * delta) := by
    rw [measure_iUnion hcells_disjoint (fun _ => measurableSet_Ioc)]
    simp only [cells, Real.volume_Ioc, add_sub_cancel_left]
    rw [ENNReal.ofReal_mul hNpos.le, ENNReal.ofReal_natCast]
    simp
  have hvolume_lower : ENNReal.ofReal (N * delta) ≤
      volume (wide ∩ Ioc 0 (A0 + N * S)) := by
    rw [← hvolume_cells]
    exact measure_mono hcells_sub
  have hprob_lower : ENNReal.ofReal c <
      (windowProbabilityMeasure (A0 + N * S) : Measure ℝ) wide := by
    rw [windowProbabilityMeasure]
    change ENNReal.ofReal c <
      (((ENNReal.ofReal (windowLength (A0 + N * S)))⁻¹ •
        volume.restrict (Ioc 0 (windowLength (A0 + N * S)))) : Measure ℝ) wide
    rw [Measure.smul_apply, Measure.restrict_apply' measurableSet_Ioc, smul_eq_mul]
    rw [windowLength_eq hTNpos]
    have hratio : ENNReal.ofReal c <
        (ENNReal.ofReal (A0 + N * S))⁻¹ * ENNReal.ofReal (N * delta) := by
      have hratioReal : c < (N * delta) / (A0 + N * S) :=
        (lt_div_iff₀ hTNpos).2 hNratio
      have hratioENN := (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 hratioReal
      rw [ENNReal.ofReal_div_of_pos hTNpos] at hratioENN
      simpa [div_eq_mul_inv, mul_comm] using hratioENN
    exact lt_of_lt_of_le hratio (by gcongr)
  exact (not_lt_of_ge hprob_lower.le) hlate

/-- **Metric completed occupation-to-hard-gap law.**  A Lipschitz orbit with sparse wide-radius
target occupation has arbitrarily late continuous intervals avoiding the narrow-radius target. -/
theorem exists_late_interval_metric_hard_of_limsup_windowProbability_le
    {E : Type*} [PseudoMetricSpace E] (evolve : ℝ → E) (targets : Set E)
    {speed epsn epsw W b : ℝ} (hspeed0 : 0 < speed)
    (hspeed : ∀ t u, dist (evolve t) (evolve u) ≤ speed * |t - u|)
    (hgap : epsn < epsw) (hW : 0 ≤ W) (hb : 0 ≤ b)
    (hlim : atTop.limsup (fun T => (windowProbabilityMeasure T : Measure ℝ)
      {t | ∃ z ∈ targets, dist (evolve t) z ≤ epsw}) ≤ ENNReal.ofReal b)
    (hpack : b < ((epsw - epsn) / speed) / (W + (epsw - epsn) / speed)) :
    ∀ A0 : ℝ, 0 ≤ A0 → ∃ u : ℝ, A0 ≤ u ∧
      Icc u (u + W) ∩ {t | ∃ z ∈ targets, dist (evolve t) z ≤ epsn} = ∅ := by
  have hdelta : 0 < (epsw - epsn) / speed := div_pos (sub_pos.mpr hgap) hspeed0
  apply exists_late_interval_disjoint_of_limsup_windowProbability_le
    {t | ∃ z ∈ targets, dist (evolve t) z ≤ epsn}
    {t | ∃ z ∈ targets, dist (evolve t) z ≤ epsw}
    hdelta hW hb
  · rintro t ⟨z, hz, htz⟩ v hv
    refine ⟨z, hz, ?_⟩
    have hvt : |v - t| ≤ (epsw - epsn) / speed := by
      rw [abs_of_pos (sub_pos.mpr hv.1)]
      linarith [hv.2]
    calc
      dist (evolve v) z ≤ dist (evolve v) (evolve t) + dist (evolve t) z :=
        dist_triangle _ _ _
      _ ≤ speed * |v - t| + epsn := add_le_add (hspeed v t) htz
      _ ≤ speed * ((epsw - epsn) / speed) + epsn := by
        gcongr
      _ = epsw := by field_simp; ring
  · exact hlim
  · exact hpack

end

end GaloisForLFunctions.HTGeometry
