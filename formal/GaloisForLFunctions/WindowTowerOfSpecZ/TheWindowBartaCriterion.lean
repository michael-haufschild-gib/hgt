import GaloisForLFunctions.WindowTowerOfSpecZ.TheSecondStageIsAWeightedPath

/-!
# The Barta criterion of a window

An arithmetic window form `‖H‖² + Σ_n c_n ∫H(u)H(u + log n)` is controlled by any positive weight
that balances the folds. If `1 ≤ h ≤ C` is measurable and every point of the window satisfies

`Σ_{n∈s} a_n (G(u + log n) + G(u − log n)) ≤ h(u)`,  `G = h·1_{[−A,0]}`,

then `Σ_{n∈s} 2a_n|∫H(u)H(u + log n)| ≤ ‖H‖²` for every window test (`sum_two_mul_abs_autocorr_le`). This
is the ground-state (Barta, Allegretto–Piepenbrink) bound for the folds: the weight `h` plays the
Perron vector of the orbit graphs of the window, and a balanced weight certifies that the Hecke graph
of every configuration in the window has spectral radius `≤ 1` (`arith_form_nonneg_of_balanced`).
The second-stage path weight is one balanced weight (`path_balance`); the constant weight `h = 1`
recovers the pointwise canonical density.
-/

noncomputable section

namespace GaloisForLFunctions.WindowTowerOfSpecZ

open CohomologyOfWindowsOfSpecZ MeasureTheory Set

variable {A : ℝ} {H : ℝ → ℝ}

/-- **The Barta criterion of a window**: a balanced weight bounds every combination of folds. -/
theorem sum_two_mul_abs_autocorr_le (hH : IsWindowTest A H) {h : ℝ → ℝ} (hm : Measurable h)
    {C : ℝ} (h1 : ∀ u, 1 ≤ h u) (hC : ∀ u, h u ≤ C) (s : Finset ℕ) {a : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n)
    (hbal : ∀ u ∈ Icc (-A) 0, ∑ n ∈ s, a n * (windowGate A h (u + Real.log n) +
      windowGate A h (u - Real.log n)) ≤ h u) :
    ∑ n ∈ s, 2 * a n * |∫ u, H u * H (u + Real.log n)| ≤ ∫ u, H u ^ 2 := by
  have hpos : ∀ u, 0 < h u := fun u => lt_of_lt_of_le one_pos (h1 u)
  have iH : Integrable fun u => H u ^ 2 := _root_.RHTower.WeilMarkovPole.integrable_sq
    hH.continuous hH.hasCompactSupport
  have hGm : Measurable (windowGate A h) := hm.indicator measurableSet_Icc
  have hG0 : ∀ v, 0 ≤ windowGate A h v := fun v => indicator_nonneg (fun u _ => (hpos u).le) v
  have hGC : ∀ v, windowGate A h v ≤ C := fun v => by
    unfold windowGate
    by_cases hv : v ∈ Icc (-A) 0
    · rw [indicator_of_mem hv]; exact hC v
    · rw [indicator_of_notMem hv]; exact le_trans (by norm_num) ((h1 v).trans (hC v))
  -- integrability of the weighted squares
  have hint : ∀ n : ℕ, Integrable fun u =>
      (windowGate A h (u + Real.log n) + windowGate A h (u - Real.log n)) / h u * H u ^ 2 := fun n =>
    iH.bdd_mul (c := 2 * C)
      ((((hGm.comp (measurable_add_const _)).add (hGm.comp (measurable_sub_const _))).div
        hm).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun u => by
        show ‖(windowGate A h (u + Real.log n) + windowGate A h (u - Real.log n)) / h u‖ ≤ 2 * C
        rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (add_nonneg (hG0 _) (hG0 _)) (hpos u).le)]
        refine (div_le_self (add_nonneg (hG0 _) (hG0 _)) (h1 u)).trans ?_
        linarith [hGC (u + Real.log n), hGC (u - Real.log n)])
  -- each fold is bounded by its weighted squares
  have hfold : ∀ n ∈ s, 2 * a n * |∫ u, H u * H (u + Real.log n)| ≤
      a n * ∫ u, (windowGate A h (u + Real.log n) + windowGate A h (u - Real.log n)) / h u *
        H u ^ 2 := fun n _ => by
    have := two_abs_autocorr_le hH hm h1 hC (Real.log n)
    nlinarith [mul_le_mul_of_nonneg_left this (ha n)]
  refine (Finset.sum_le_sum hfold).trans ?_
  -- the balance pays the weighted squares pointwise
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum _ fun n _ => (hint n).const_mul (a n)]
  refine integral_mono (integrable_finsetSum _ fun n _ => (hint n).const_mul (a n)) iH fun u => ?_
  by_cases hu : u ∈ Icc (-A) 0
  · have hb := hbal u hu
    have hhu := hpos u
    have : ∑ n ∈ s, a n * ((windowGate A h (u + Real.log n) + windowGate A h (u - Real.log n)) /
        h u * H u ^ 2) = (∑ n ∈ s, a n * (windowGate A h (u + Real.log n) +
          windowGate A h (u - Real.log n))) / h u * H u ^ 2 := by
      rw [Finset.sum_div, Finset.sum_mul]
      exact Finset.sum_congr rfl fun n _ => by ring
    rw [this]
    calc _ ≤ h u / h u * H u ^ 2 :=
          mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hb hhu.le) (sq_nonneg _)
      _ = H u ^ 2 := by rw [div_self hhu.ne', one_mul]
  · rw [hH.vanish u hu]; simp

/-- **A balanced weight makes the arithmetic window form nonnegative**: under the balance condition,
`‖H‖² + Σ_{n∈s} 2a_n ∫H(u)H(u + log n) ≥ 0` for every window test and every choice of signs. -/
theorem arith_form_nonneg_of_balanced (hH : IsWindowTest A H) {h : ℝ → ℝ} (hm : Measurable h)
    {C : ℝ} (h1 : ∀ u, 1 ≤ h u) (hC : ∀ u, h u ≤ C) (s : Finset ℕ) {a : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n)
    (hbal : ∀ u ∈ Icc (-A) 0, ∑ n ∈ s, a n * (windowGate A h (u + Real.log n) +
      windowGate A h (u - Real.log n)) ≤ h u)
    (ε : ℕ → ℝ) (hε : ∀ n, |ε n| ≤ 1) :
    0 ≤ (∫ u, H u ^ 2) + ∑ n ∈ s, 2 * a n * ε n * ∫ u, H u * H (u + Real.log n) := by
  have key := sum_two_mul_abs_autocorr_le hH hm h1 hC s ha hbal
  have hterm : ∀ n ∈ s, -(2 * a n * |∫ u, H u * H (u + Real.log n)|) ≤
      2 * a n * ε n * ∫ u, H u * H (u + Real.log n) := fun n _ => by
    have h2 : 0 ≤ 2 * a n := by linarith [ha n]
    have habs : |ε n * ∫ u, H u * H (u + Real.log n)| ≤ |∫ u, H u * H (u + Real.log n)| := by
      rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) (hε n)
    have := neg_abs_le (ε n * ∫ u, H u * H (u + Real.log n))
    nlinarith [mul_le_mul_of_nonneg_left habs h2]
  have := Finset.sum_le_sum hterm
  rw [Finset.sum_neg_distrib] at this
  linarith

end GaloisForLFunctions.WindowTowerOfSpecZ
