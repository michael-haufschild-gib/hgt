import GaloisForLFunctions.RHTower.PaperCircleAdaptiveHistory
import GaloisForLFunctions.HTGeometry.PaperFourierLLogL.Paths.Wager

/-! # Evidence-paid maximal wagers on actual adaptive native histories

Project the source's certified play into its revealed-bit thread. Every predictable
linear wager then has an exponential maximal budget, including after conditioning
on the actual observation history. The evidence pays the entire conditioning cost;
the tail estimate holds simultaneously over every prefix of the chosen thread.
-/

open Filter
open scoped BigOperators NNReal Classical
open GaloisForLFunctions.HTGeometry.FourierLLogL
open GaloisForLFunctions.HTGeometry.FourierLLogL.Dyadic
open GaloisForLFunctions.HTGeometry.FourierLLogL.Dyadic.Procedure
open GaloisForLFunctions.HTGeometry.FourierLLogL.Dyadic.Procedure.Paths

namespace RHTower
noncomputable section
variable {ι : Type*} [Fintype ι] {E : Type*}

private lemma normalized_play {M j J : ℕ} {c : Scene M} {f : Grid M → ℝ}
    (play : Play j M c) (h : play.Follows J f) (hm : 0 < c.mass)
    (he : c.enter) (hr : ¬ c.retire j) : ∃ t : Play j M c.reset, t.Follows J f := by
  cases play with
  | rest c =>
    refine ⟨Play.rest _, ?_, h.2⟩
    exact ⟨h.1.within, h.1.depth_ok, h.1.capital, hm.le, h.1.positive, h.1.sub, h.1.cut⟩
  | ticket c t => exact ⟨t, h.2.2.2.2⟩
  | freeze c t => exact (hr h.2.2.1).elim
  | jump c left right => exact (h.2.1.2.2 he).elim
  | attempt c u left right => exact (h.2.1.2.2 he).elim

/-- Remove the initial normalization ticket before projecting revealed bits. -/
theorem paperCircleHistory_normalized_play_exists (a : ι → CCMCircleBoundedSymbol) (M k : ℕ)
    (s : List (ℝ≥0 × Grid M)) :
    ∀ᶠ j : ℕ in atTop, ∃ t : Play j M (paperCircleHistoryBegin a M k s).reset,
      t.Follows M (paperCircleHistoryLikelihood a M k s) := by
  filter_upwards [paperCircleHistory_play_exists a M k s,
    Thermal.hpoly (-Real.log (paperCircleHistoryEvidence a M k s)) 0] with j hj hheight
  simp only [pow_zero, mul_one] at hheight
  have hm := paperCircleHistoryBegin_mass_pos a M k s
  have hmass : Real.exp (-Compress.Params.height j) ≤ (paperCircleHistoryBegin a M k s).mass := by
    rw [paperCircleHistoryBegin_mass, ← Real.exp_log (paperCircleHistoryEvidence_pos a M k s)]
    exact Real.exp_le_exp.mpr (by linarith only [hheight])
  have hr : ¬ (paperCircleHistoryBegin a M k s).retire j := by
    rintro ⟨_, h | h⟩
    · change 1000 * Compress.Params.height j < 0 at h
      have hp := Thermal.d_pos j
      linarith only [h,hp]
    · exact (not_lt_of_ge hmass) h
  obtain ⟨play,hplay⟩ := hj
  apply normalized_play play hplay hm ?_ hr
  change 2 * 0 < (paperCircleHistoryBegin a M k s).mass
  simpa only [mul_zero] using hm

/-- Select the normalized actual play's revealed-bit thread, with an inert early-scale fallback. -/
def paperCircleHistoryThread (a : ι → CCMCircleBoundedSymbol) (M k : ℕ)
    (s : List (ℝ≥0 × Grid M)) (j : ℕ) : Thread M (paperCircleHistoryBegin a M k s).reset :=
  if h : ∃ play : Play j M (paperCircleHistoryBegin a M k s).reset,
      play.Follows M (paperCircleHistoryLikelihood a M k s) then
    Thread.project (Classical.choose h) else Thread.blank _

theorem paperCircleHistoryThread_following (a : ι → CCMCircleBoundedSymbol) (M k : ℕ)
    (s : List (ℝ≥0 × Grid M)) :
    ∀ᶠ j : ℕ in atTop, (paperCircleHistoryThread a M k s j).Following j M
      (paperCircleHistoryLikelihood a M k s) := by
  filter_upwards [paperCircleHistory_normalized_play_exists a M k s] with j hj
  unfold paperCircleHistoryThread
  rw [dif_pos hj]
  exact Thread.projected _ (Classical.choose_spec hj)

private lemma history_root_dice (M : ℕ) : Node.root.dice M = Law.uniform (Grid M) := by
  apply Law.ext
  intro x
  have hx : x ∈ Node.root.block M := (Node.mem_group _ _).mp (by
    rw [Node.group_top]
    exact Finset.mem_univ x)
  rw [Node.dice_apply (Node.root_ok M), if_pos hx, Node.len_top, inv_one, mul_one]
  exact (uniform_side x).symm

private lemma history_posterior_expectation (a : ι → CCMCircleBoundedSymbol) (M k : ℕ)
    (s : List (ℝ≥0 × Grid M)) (f : Grid M → ℝ) (hf : ∀ x, 0 ≤ f x) :
    (paperCircleHistoryPosterior a M k s).Ex f ≤
      (Law.uniform (Grid M)).Ex f / paperCircleHistoryEvidence a M k s := by
  rw [Law.Ex, Law.Ex, Finset.sum_div]
  apply Finset.sum_le_sum
  intro x _
  rw [paperCircleHistoryPosterior_apply, uniform_side]
  calc
    _ = (Period.side M * f x) * paperCircleHistoryLikelihood a M k s x /
        paperCircleHistoryEvidence a M k s := by ring
    _ ≤ _ := div_le_div_of_nonneg_right
      (mul_le_of_le_one_right (mul_nonneg (Period.side_pos M).le (hf x))
        (paperCircleHistoryLikelihood_le_one a M k s x))
      (paperCircleHistoryEvidence_pos a M k s).le

/-- A single eventual scale threshold works for every predictable stake rule and initial state. -/
theorem paperCircleHistoryThread_uniform_heat (a : ι → CCMCircleBoundedSymbol) (M k : ℕ)
    (s : List (ℝ≥0 × Grid M)) :
    ∀ᶠ j : ℕ in atTop, ∀ (A : Desk M E) (e : E),
      (Law.uniform (Grid M)).Ex
        (fun x => A.heatW e ((paperCircleHistoryThread a M k s j).stream x)) ≤ 2 := by
  filter_upwards [paperCircleHistoryThread_following a M k s] with j hj A e
  have h := A.heat_bound (paperCircleHistoryThread a M k s j) hj e
  change (Node.root.dice M).Ex _ ≤ 2 at h
  rw [history_root_dice] at h
  exact h

/-- The actual observation evidence pays the change from uniform inputs to the posterior. -/
theorem paperCircleHistoryThread_posterior_heat (a : ι → CCMCircleBoundedSymbol) (M k : ℕ)
    (s : List (ℝ≥0 × Grid M)) :
    ∀ᶠ j : ℕ in atTop, ∀ (A : Desk M E) (e : E),
      (paperCircleHistoryPosterior a M k s).Ex
        (fun x => A.heatW e ((paperCircleHistoryThread a M k s j).stream x)) ≤
          2 / paperCircleHistoryEvidence a M k s := by
  filter_upwards [paperCircleHistoryThread_uniform_heat (E := E) a M k s] with j hj A e
  exact (history_posterior_expectation a M k s _
    (fun x => zero_le_one.trans (A.heatW_one e _))).trans
      (div_le_div_of_nonneg_right (hj A e) (paperCircleHistoryEvidence_pos a M k s).le)

private lemma wager_exponential_tail {α : Type} [Fintype α] (P : Law α)
    (Y : α → ℝ) (C : ℝ) (hC : 0 < C)
    (h : P.Ex (fun x => Real.exp (Y x / 2)) ≤ C) (u : ℝ) :
    P.prob (fun x => 2 * Real.log C + u ≤ Y x) ≤ Real.exp (-u / 2) := by
  let v := 2 * Real.log C + u
  have ht := P.upperTail (fun x => v ≤ Y x) (fun x => Real.exp (Y x / 2))
    (fun x => (Real.exp_pos _).le) (Real.exp (v / 2))
    (fun x hx => Real.exp_le_exp.mpr (by linarith))
  have hid : Real.exp (v / 2) * Real.exp (-u / 2) = C := by
    rw [← Real.exp_add, show v / 2 + -u / 2 = Real.log C by dsimp [v]; ring,
      Real.exp_log hC]
  have hb := ht.trans h
  rw [← hid] at hb
  exact le_of_mul_le_mul_left hb (Real.exp_pos _)

/-- A posterior tail bound for the maximum score attained at any time along the thread. -/
theorem paperCircleHistoryThread_peak_tail (a : ι → CCMCircleBoundedSymbol) (M k : ℕ)
    (s : List (ℝ≥0 × Grid M)) :
    ∀ᶠ j : ℕ in atTop, ∀ (A : Desk M E) (e : E) (u : ℝ),
      (paperCircleHistoryPosterior a M k s).prob (fun x =>
        2 * Real.log (2 / paperCircleHistoryEvidence a M k s) + u ≤
          A.peak e 0 0 ((paperCircleHistoryThread a M k s j).stream x)) ≤ Real.exp (-u / 2) := by
  filter_upwards [paperCircleHistoryThread_posterior_heat (E := E) a M k s] with j hj A e u
  exact wager_exponential_tail _ _ _
    (div_pos (by norm_num) (paperCircleHistoryEvidence_pos a M k s)) (hj A e) u

private lemma wager_mean_peak {α : Type} [Fintype α] (P : Law α)
    (Y : α → ℝ) (C : ℝ) (hC : 0 < C)
    (h : P.Ex (fun x => Real.exp (Y x / 2)) ≤ C) : P.Ex Y ≤ 2 * Real.log C := by
  have hJ := (P.Ex_exp (fun x => Y x / 2)).trans h
  rw [← Real.exp_log hC] at hJ
  have hl := Real.exp_le_exp.mp hJ
  have he : P.Ex (fun x => Y x / 2) = P.Ex Y / 2 := by
    simp only [Law.Ex, mul_div_assoc, Finset.sum_div]
  rw [he] at hl
  linarith only [hl]

theorem paperCircleHistoryThread_mean_peak (a : ι → CCMCircleBoundedSymbol) (M k : ℕ)
    (s : List (ℝ≥0 × Grid M)) :
    ∀ᶠ j : ℕ in atTop, ∀ (A : Desk M E) (e : E),
      (paperCircleHistoryPosterior a M k s).Ex
        (fun x => A.peak e 0 0 ((paperCircleHistoryThread a M k s j).stream x)) ≤
          2 * Real.log (2 / paperCircleHistoryEvidence a M k s) := by
  filter_upwards [paperCircleHistoryThread_posterior_heat (E := E) a M k s] with j hj A e
  exact wager_mean_peak _ _ _
    (div_pos (by norm_num) (paperCircleHistoryEvidence_pos a M k s)) (hj A e)

theorem paperCircleHistoryThread_prefix_le_peak (a : ι → CCMCircleBoundedSymbol) (M k : ℕ)
    (s : List (ℝ≥0 × Grid M)) (j : ℕ) (A : Desk M E) (e : E) (x : Grid M) (n : ℕ) :
    A.tally e (((paperCircleHistoryThread a M k s j).stream x).take n) ≤
      A.peak e 0 0 ((paperCircleHistoryThread a M k s j).stream x) := by
  have h := A.peak_on e 0 0 le_rfl
    (((paperCircleHistoryThread a M k s j).stream x).take n)
    (((paperCircleHistoryThread a M k s j).stream x).drop n)
  simpa only [List.take_append_drop, zero_add] using h

/-- The same tail estimate controls existence of a successful prefix, without a union-bound cost. -/
theorem paperCircleHistoryThread_any_prefix_tail (a : ι → CCMCircleBoundedSymbol) (M k : ℕ)
    (s : List (ℝ≥0 × Grid M)) :
    ∀ᶠ j : ℕ in atTop, ∀ (A : Desk M E) (e : E) (u : ℝ),
      (paperCircleHistoryPosterior a M k s).prob (fun x => ∃ n : ℕ,
        2 * Real.log (2 / paperCircleHistoryEvidence a M k s) + u ≤
          A.tally e (((paperCircleHistoryThread a M k s j).stream x).take n)) ≤
            Real.exp (-u / 2) := by
  filter_upwards [paperCircleHistoryThread_peak_tail (E := E) a M k s] with j hj A e u
  apply le_trans (Law.prob_mono _ _ _ ?_) (hj A e u)
  rintro x ⟨n,hn⟩
  exact hn.trans (paperCircleHistoryThread_prefix_le_peak a M k s j A e x n)

end
end RHTower
