/-
Doc 31 S-mono to AMP-threshold bridge.

`SpurThreshold` consumes an explicit threshold split.  The S-mono arc naturally
produces a monotone sequence of real margin readings instead.  This module is
the reusable finite bridge: a nondecreasing or nonincreasing real sequence can
cross any threshold at most once, so the corrected copy/flip counting capstone
applies directly.
-/
import GaloisForLFunctions.RHTower.SpurThreshold

noncomputable section

namespace RHTower

/-- A nondecreasing real list crosses any threshold at most once. -/
theorem copyFlipTransitions_thresholdStates_pairwise_le_le_one {t : ℝ} :
    ∀ (xs : List ℝ), List.Pairwise (fun x y => x ≤ y) xs →
      copyFlipTransitions (thresholdStates t xs) ≤ 1 := by
  intro xs
  induction xs with
  | nil =>
      intro h
      simp [thresholdStates]
  | cons x xs ih =>
      intro h
      cases xs with
      | nil =>
          simp [thresholdStates]
      | cons y ys =>
          cases h with
          | cons hx_all htail =>
              by_cases hx : t < x
              · have hwhole : ∀ z ∈ x :: y :: ys, decide (t < z) = true := by
                  intro z hz
                  rcases List.mem_cons.mp hz with rfl | hz_tail
                  · exact decide_eq_true hx
                  · have hxz : x ≤ z := hx_all z hz_tail
                    exact decide_eq_true (lt_of_lt_of_le hx hxz)
                rw [thresholdStates_eq_replicate_of_forall_eq t (x :: y :: ys) true hwhole]
                simp
              · by_cases hy : t < y
                · cases htail with
                  | cons hy_all _ =>
                      have htail_true : ∀ z ∈ y :: ys, decide (t < z) = true := by
                        intro z hz
                        rcases List.mem_cons.mp hz with rfl | hz_tail
                        · exact decide_eq_true hy
                        · have hyz : y ≤ z := hy_all z hz_tail
                          exact decide_eq_true (lt_of_lt_of_le hy hyz)
                      have hrepTail :=
                        thresholdStates_eq_replicate_of_forall_eq t (y :: ys) true htail_true
                      have hxdec : decide (t < x) = false := decide_eq_false hx
                      rw [thresholdStates, List.map_cons, hxdec]
                      unfold thresholdStates at hrepTail
                      rw [hrepTail]
                      simpa using copyFlipTransitions_cons_replicate_not_le_one (y :: ys).length false
                · have hxdec : decide (t < x) = false := decide_eq_false hx
                  have hydec : decide (t < y) = false := decide_eq_false hy
                  rw [thresholdStates, List.map_cons, List.map_cons, hxdec, hydec,
                    copyFlipTransitions_cons_cons, if_pos rfl, zero_add]
                  simpa [thresholdStates, hydec] using ih htail

/-- A nonincreasing real list crosses any threshold at most once. -/
theorem copyFlipTransitions_thresholdStates_pairwise_ge_le_one {t : ℝ} :
    ∀ (xs : List ℝ), List.Pairwise (fun x y => y ≤ x) xs →
      copyFlipTransitions (thresholdStates t xs) ≤ 1 := by
  intro xs
  induction xs with
  | nil =>
      intro h
      simp [thresholdStates]
  | cons x xs ih =>
      intro h
      cases xs with
      | nil =>
          simp [thresholdStates]
      | cons y ys =>
          cases h with
          | cons hx_all htail =>
              by_cases hx : t < x
              · by_cases hy : t < y
                · have hxdec : decide (t < x) = true := decide_eq_true hx
                  have hydec : decide (t < y) = true := decide_eq_true hy
                  rw [thresholdStates, List.map_cons, List.map_cons, hxdec, hydec,
                    copyFlipTransitions_cons_cons, if_pos rfl, zero_add]
                  simpa [thresholdStates, hydec] using ih htail
                · cases htail with
                  | cons hy_all _ =>
                      have htail_false : ∀ z ∈ y :: ys, decide (t < z) = false := by
                        intro z hz
                        rcases List.mem_cons.mp hz with rfl | hz_tail
                        · exact decide_eq_false hy
                        · have hzy : z ≤ y := hy_all z hz_tail
                          have hnz : ¬ t < z := by
                            intro htz
                            exact hy (lt_of_lt_of_le htz hzy)
                          exact decide_eq_false hnz
                      have hrepTail :=
                        thresholdStates_eq_replicate_of_forall_eq t (y :: ys) false htail_false
                      have hxdec : decide (t < x) = true := decide_eq_true hx
                      rw [thresholdStates, List.map_cons, hxdec]
                      unfold thresholdStates at hrepTail
                      rw [hrepTail]
                      simpa using copyFlipTransitions_cons_replicate_not_le_one (y :: ys).length true
              · have hwhole : ∀ z ∈ x :: y :: ys, decide (t < z) = false := by
                  intro z hz
                  rcases List.mem_cons.mp hz with rfl | hz_tail
                  · exact decide_eq_false hx
                  · have hzx : z ≤ x := hx_all z hz_tail
                    have hnz : ¬ t < z := by
                      intro htz
                      exact hx (lt_of_lt_of_le htz hzx)
                    exact decide_eq_false hnz
                rw [thresholdStates_eq_replicate_of_forall_eq t (x :: y :: ys) false hwhole]
                simp

/-- Corrected counting after a nondecreasing threshold sequence. -/
theorem corrected_counting_exact_pair_of_thresholdStates_pairwise_le {Z : ℕ} {t : ℝ}
    {xs : List ℝ} (hmono : List.Pairwise (fun x y => x ≤ y) xs)
    (hvisible : 0 < Z) (heven : Even Z)
    (hbound : Z ≤ 2 + copyFlipTransitions (thresholdStates t xs)) :
    Z = 2 :=
  even_count_eq_two_of_visible_and_le_two hvisible heven
    (corrected_counting_bound_at_most_one_crossing hbound
      (copyFlipTransitions_thresholdStates_pairwise_le_le_one xs hmono) heven)

/-- Corrected counting after a nonincreasing threshold sequence. -/
theorem corrected_counting_exact_pair_of_thresholdStates_pairwise_ge {Z : ℕ} {t : ℝ}
    {xs : List ℝ} (hmono : List.Pairwise (fun x y => y ≤ x) xs)
    (hvisible : 0 < Z) (heven : Even Z)
    (hbound : Z ≤ 2 + copyFlipTransitions (thresholdStates t xs)) :
    Z = 2 :=
  even_count_eq_two_of_visible_and_le_two hvisible heven
    (corrected_counting_bound_at_most_one_crossing hbound
      (copyFlipTransitions_thresholdStates_pairwise_ge_le_one xs hmono) heven)

/-- AMP margin monotonicity, increasing orientation. -/
theorem copyFlipTransitions_ampMarginStates_pairwise_le_le_one {xs : List ℝ}
    (hmono : List.Pairwise (fun x y => x ≤ y) xs) :
    copyFlipTransitions (ampMarginStates xs) ≤ 1 := by
  unfold ampMarginStates
  exact copyFlipTransitions_thresholdStates_pairwise_le_le_one xs hmono

/-- AMP margin monotonicity, decreasing orientation. -/
theorem copyFlipTransitions_ampMarginStates_pairwise_ge_le_one {xs : List ℝ}
    (hmono : List.Pairwise (fun x y => y ≤ x) xs) :
    copyFlipTransitions (ampMarginStates xs) ≤ 1 := by
  unfold ampMarginStates
  exact copyFlipTransitions_thresholdStates_pairwise_ge_le_one xs hmono

/-- Corrected counting from nondecreasing AMP margin readings. -/
theorem corrected_counting_exact_pair_of_ampMargin_pairwise_le {Z : ℕ} {xs : List ℝ}
    (hmono : List.Pairwise (fun x y => x ≤ y) xs)
    (hvisible : 0 < Z) (heven : Even Z)
    (hbound : Z ≤ 2 + copyFlipTransitions (ampMarginStates xs)) :
    Z = 2 := by
  unfold ampMarginStates at hbound
  exact corrected_counting_exact_pair_of_thresholdStates_pairwise_le hmono hvisible heven hbound

/-- Corrected counting from nonincreasing AMP margin readings. -/
theorem corrected_counting_exact_pair_of_ampMargin_pairwise_ge {Z : ℕ} {xs : List ℝ}
    (hmono : List.Pairwise (fun x y => y ≤ x) xs)
    (hvisible : 0 < Z) (heven : Even Z)
    (hbound : Z ≤ 2 + copyFlipTransitions (ampMarginStates xs)) :
    Z = 2 := by
  unfold ampMarginStates at hbound
  exact corrected_counting_exact_pair_of_thresholdStates_pairwise_ge hmono hvisible heven hbound

end RHTower
