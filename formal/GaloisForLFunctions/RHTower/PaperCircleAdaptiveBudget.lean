import GaloisForLFunctions.RHTower.PaperCircleAdaptiveFluctuation
import GaloisForLFunctions.HTGeometry.PaperFourierLLogL.Paths.Upkeep

/-! # Paid loss and innovation budgets on actual adaptive histories

The native evidence controls posterior expectations. Normalization gives a unit
uniform budget for discarded mass and a finite total prediction-innovation budget.
Combining these with maximal wagers removes the random loss term from the
all-interval fluctuation threshold.
-/

open Filter
open scoped BigOperators NNReal Classical
open GaloisForLFunctions.HTGeometry.FourierLLogL
open GaloisForLFunctions.HTGeometry.FourierLLogL.Dyadic
open GaloisForLFunctions.HTGeometry.FourierLLogL.Dyadic.Procedure
open GaloisForLFunctions.HTGeometry.FourierLLogL.Dyadic.Procedure.Paths

namespace RHTower
noncomputable section
variable {ι : Type*} [Fintype ι]

/-- Actual evidence pays every absolute posterior expectation, without a sign premise. -/
theorem paperCircleHistoryPosterior_absolute_expectation (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (s : List (ℝ≥0 × Grid M)) (f : Grid M → ℝ) :
    paperCircleHistoryEvidence a M k s *
      (paperCircleHistoryPosterior a M k s).Ex (fun x => |f x|) ≤
        (Law.uniform (Grid M)).Ex (fun x => |f x|) := by
  rw [Law.Ex, Law.Ex, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  rw [paperCircleHistoryPosterior_apply, uniform_side]
  calc
    _ = (Period.side M * |f x|) * paperCircleHistoryLikelihood a M k s x := by
      field_simp [(paperCircleHistoryEvidence_pos a M k s).ne']
    _ ≤ _ := mul_le_of_le_one_right (mul_nonneg (Period.side_pos M).le (abs_nonneg _))
      (paperCircleHistoryLikelihood_le_one a M k s x)

private lemma posterior_transfer (a : ι → CCMCircleBoundedSymbol) (M k : ℕ)
    (s : List (ℝ≥0 × Grid M)) (f : Grid M → ℝ) (hf : ∀ x, 0 ≤ f x) :
    (paperCircleHistoryPosterior a M k s).Ex f ≤
      (Law.uniform (Grid M)).Ex f / paperCircleHistoryEvidence a M k s := by
  have h := paperCircleHistoryPosterior_absolute_expectation a M k s f
  simp_rw [abs_of_nonneg (hf _)] at h
  exact (le_div_iff₀ (paperCircleHistoryEvidence_pos a M k s)).mpr
    (by simpa only [mul_comm] using h)

private lemma native_stats (a : ι → CCMCircleBoundedSymbol) (M k : ℕ)
    (s : List (ℝ≥0 × Grid M)) (j : ℕ) (F : Path M → ℝ) :
    stats (paperCircleHistoryThread a M k s j) F =
      (Law.uniform (Grid M)).Ex (fun x => F ((paperCircleHistoryThread a M k s j).stream x)) := by
  change (Node.root.dice M).Ex _ = _
  rw [← Node.avg_ex (Node.root_ok M), top_avg, expU_ex]

theorem paperCircleHistoryThread_uniform_kills (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (s : List (ℝ≥0 × Grid M)) :
    ∀ᶠ j : ℕ in atTop, (Law.uniform (Grid M)).Ex (fun x =>
      fullKills ((paperCircleHistoryThread a M k s j).stream x)) ≤ 1 := by
  filter_upwards [paperCircleHistoryThread_following a M k s] with j hj
  have h := Thread.deaths (paperCircleHistoryThread a M k s j) hj
    (paperCircleHistoryNormalizedBegin_fit a M k s).pos
  change stats (paperCircleHistoryThread a M k s j) fullKills ≤
    (paperCircleHistoryBegin a M k s).mass / (paperCircleHistoryBegin a M k s).mass at h
  rw [div_self (paperCircleHistoryBegin_mass_pos a M k s).ne', native_stats] at h
  exact h

theorem paperCircleHistoryThread_posterior_kills (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (s : List (ℝ≥0 × Grid M)) :
    ∀ᶠ j : ℕ in atTop, (paperCircleHistoryPosterior a M k s).Ex (fun x =>
      fullKills ((paperCircleHistoryThread a M k s j).stream x)) ≤
        1 / paperCircleHistoryEvidence a M k s := by
  filter_upwards [paperCircleHistoryThread_uniform_kills a M k s,
    paperCircleHistoryThread_trip a M k s] with j hk ht
  exact (posterior_transfer a M k s _ (fun x => trip_K (ht x))).trans
    (div_le_div_of_nonneg_right hk (paperCircleHistoryEvidence_pos a M k s).le)

def paperCircleHistoryCumulativeInnovation (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (s : List (ℝ≥0 × Grid M)) (j : ℕ) (u x : Grid M) : ℝ :=
  subtotal (fun b => shower u b.post) ((paperCircleHistoryThread a M k s j).stream x)

private lemma innovation_mass_budget {M j J : ℕ} {s : Scene M} {f : Grid M → ℝ}
    (t : Thread M s) (h : t.Following j J f) (hs : Fit s) (u : Grid M) :
    stats t (Run.Streak.showers ⟨0,u⟩) ≤
      share s - Capture.energy s u + 7 * stats t fullKills := by
  induction t with
  | blank s =>
    rw [stats_nil, stats_nil]
    change 0 ≤ share s - Capture.energy s u + 7 * 0
    linarith only [(energy_small hs u).2]
  | ran s q k ih =>
    let U := Law.uniform Bool
    have hq := jump_ideal h hs.lift
    have hi := U.Ex_mono (fun b => ih b (h.2.2.2.2.2 b) (hq.climb.child b))
    rw [Law.Ex_add, Law.Ex_sub, Law.Ex_lmul] at hi
    have he : U.Ex (fun b => Capture.energy (q.smaller b) u) =
        Capture.energy q u + shower u q := by
      rw [fair_av]
      exact wet_average q hq.climb u
    have hm : U.Ex (fun b => share (q.smaller b)) = share q := by
      rw [fair_av]
      linarith only [share_split q]
    rw [hm,he] at hi
    have hd := energy_drain (b := Thread.Beat.mk s q false) hq u
    have hk : share s - share q = Thread.killed (Thread.Beat.mk s q false) := by
      unfold share Thread.killed
      rw [hq.lower.flat]
      ring
    change (Thread.ran s q k).fee (fun b => shower u b.post) ≤
      share s - Capture.energy s u + 7 * (Thread.ran s q k).fee Thread.killed
    rw [Thread.fee_ran _ h, Thread.fee_ran _ h]
    simp_rw [Law.Ex_add]
    rw [Law.Ex_const U (shower u q)]
    have hconst : U.Ex (fun b : Bool => Thread.killed ⟨s,q,b⟩) =
        Thread.killed (Thread.Beat.mk s q false) := Law.Ex_const U _
    rw [hconst]
    change shower u q + U.Ex (fun b => (k b).fee (fun d => shower u d.post)) ≤
      share s - Capture.energy s u +
        7 * (Thread.killed ⟨s,q,false⟩ + U.Ex (fun b => (k b).fee Thread.killed))
    change U.Ex (fun b => (k b).fee (fun d => shower u d.post)) ≤
      share q - (Capture.energy q u + shower u q) +
        7 * U.Ex (fun b => (k b).fee Thread.killed) at hi
    change |Capture.energy s u - Capture.energy q u| ≤ 8 * Thread.killed ⟨s,q,false⟩ at hd
    linarith only [hi,hk,(abs_le.mp hd).2]

/-- Refinement spends remaining mass and energy; discarded mass pays only seven extra units. -/
theorem paperCircleHistoryThread_innovation_mass_balance (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (s : List (ℝ≥0 × Grid M)) :
    ∀ᶠ j : ℕ in atTop, ∀ u : Grid M,
      (Law.uniform (Grid M)).Ex (paperCircleHistoryCumulativeInnovation a M k s j u) ≤
        1 - Capture.energy (paperCircleHistoryBegin a M k s).reset u +
          7 * (Law.uniform (Grid M)).Ex (fun x =>
            fullKills ((paperCircleHistoryThread a M k s j).stream x)) := by
  filter_upwards [paperCircleHistoryThread_following a M k s] with j hj u
  have h := innovation_mass_budget (paperCircleHistoryThread a M k s j) hj
    (paperCircleHistoryNormalizedBegin_fit a M k s) u
  have hm : share (paperCircleHistoryBegin a M k s).reset = 1 := by
    change (paperCircleHistoryBegin a M k s).mass / (paperCircleHistoryBegin a M k s).mass = 1
    exact div_self (paperCircleHistoryBegin_mass_pos a M k s).ne'
  rw [hm,native_stats,native_stats] at h
  exact h

theorem paperCircleHistoryThread_uniform_innovation (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (s : List (ℝ≥0 × Grid M)) :
    ∀ᶠ j : ℕ in atTop, ∀ u : Grid M,
      (Law.uniform (Grid M)).Ex (paperCircleHistoryCumulativeInnovation a M k s j u) ≤
        8 - Capture.energy (paperCircleHistoryBegin a M k s).reset u := by
  filter_upwards [paperCircleHistoryThread_innovation_mass_balance a M k s,
    paperCircleHistoryThread_uniform_kills a M k s] with j hj hk u
  linarith only [hj u,hk]

theorem paperCircleHistoryThread_posterior_innovation (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (s : List (ℝ≥0 × Grid M)) :
    ∀ᶠ j : ℕ in atTop, ∀ u : Grid M,
      (paperCircleHistoryPosterior a M k s).Ex (paperCircleHistoryCumulativeInnovation a M k s j u) ≤
        (8 - Capture.energy (paperCircleHistoryBegin a M k s).reset u) /
          paperCircleHistoryEvidence a M k s := by
  filter_upwards [paperCircleHistoryThread_uniform_innovation a M k s,
    paperCircleHistoryThread_trip a M k s] with j hi ht u
  have hn (x : Grid M) : 0 ≤ paperCircleHistoryCumulativeInnovation a M k s j u x :=
    Run.Streak.showers_pos (Run.Streak.mk 0 u) (ht x)
  exact (posterior_transfer a M k s _ hn).trans
    (div_le_div_of_nonneg_right (hi u) (paperCircleHistoryEvidence_pos a M k s).le)

theorem paperCircleHistoryThread_kills_tail (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (s : List (ℝ≥0 × Grid M)) :
    ∀ᶠ j : ℕ in atTop, ∀ v : ℝ,
      (paperCircleHistoryPosterior a M k s).prob (fun x =>
        Real.exp v / paperCircleHistoryEvidence a M k s ≤
          fullKills ((paperCircleHistoryThread a M k s j).stream x)) ≤ Real.exp (-v) := by
  filter_upwards [paperCircleHistoryThread_posterior_kills a M k s,
    paperCircleHistoryThread_trip a M k s] with j hk ht v
  let e := paperCircleHistoryEvidence a M k s
  have h := (paperCircleHistoryPosterior a M k s).upperTail _
    (fun x => fullKills ((paperCircleHistoryThread a M k s j).stream x))
    (fun x => trip_K (ht x)) (Real.exp v / e) (fun _ hx => hx)
  have he : Real.exp v / e * Real.exp (-v) = 1 / e := by
    calc
      _ = (Real.exp v * Real.exp (-v)) / e := by ring
      _ = _ := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hb := h.trans hk
  change _ ≤ 1 / e at hb
  rw [← he] at hb
  exact le_of_mul_le_mul_left hb
    (div_pos (Real.exp_pos _) (paperCircleHistoryEvidence_pos a M k s))

/-- Fully deterministic evidence-paid thresholds, with separate loss and wager parameters. -/
theorem paperCircleHistoryThread_paid_interval_tail (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (s : List (ℝ≥0 × Grid M)) :
    ∀ᶠ j : ℕ in atTop, ∀ (u : Grid M) (n : ℕ) (w v : ℝ),
      (paperCircleHistoryPosterior a M k s).prob (fun x =>
        let L := (paperCircleHistoryThread a M k s j).stream x
        ∃ start len : ℕ, 12000 * Real.sqrt (Period.side n) *
          (1 + Real.exp w / paperCircleHistoryEvidence a M k s +
            2 * Real.log (17 / paperCircleHistoryEvidence a M k s) + v) ≤
              ‖subtotal (frosty x u (Period.side n)) ((L.drop start).take len)‖) ≤
                Real.exp (-w) + Real.exp (-v / 2) := by
  filter_upwards [paperCircleHistoryThread_interval_fluctuation a M k s,
    paperCircleHistoryThread_cold_tail a M k s,
    paperCircleHistoryThread_kills_tail a M k s] with j hf hc hk u n w v
  let A := fun x => Real.exp w / paperCircleHistoryEvidence a M k s ≤
    fullKills ((paperCircleHistoryThread a M k s j).stream x)
  let B := fun x => 2 * Real.log (17 / paperCircleHistoryEvidence a M k s) + v ≤
    2 * Real.log (coldScore u (Period.side n) ((paperCircleHistoryThread a M k s j).stream x))
  apply le_trans (Law.prob_mono _ _ (fun x => A x ∨ B x) ?_)
    ((Law.prob_union _ A B).trans (add_le_add (hk w) (hc u (Period.side n) v)))
  rintro x ⟨start,len,h⟩
  by_cases ha : A x
  · exact Or.inl ha
  apply Or.inr
  have hcoef : 0 < 12000 * Real.sqrt (Period.side n) :=
    mul_pos (by norm_num) (Real.sqrt_pos.mpr (Period.side_pos n))
  have hb := le_of_mul_le_mul_left (h.trans (hf x u n start len)) hcoef
  dsimp [A] at ha
  dsimp [B]
  have hn := lt_of_not_ge ha
  linarith only [hb,hn]

/-- One tail parameter suffices to pay both exceptional events. -/
theorem paperCircleHistoryThread_balanced_interval_tail (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (s : List (ℝ≥0 × Grid M)) :
    ∀ᶠ j : ℕ in atTop, ∀ (u : Grid M) (n : ℕ) (v : ℝ),
      (paperCircleHistoryPosterior a M k s).prob (fun x =>
        let L := (paperCircleHistoryThread a M k s j).stream x
        ∃ start len : ℕ, 12000 * Real.sqrt (Period.side n) *
          (1 + Real.exp (v / 2) / paperCircleHistoryEvidence a M k s +
            2 * Real.log (17 / paperCircleHistoryEvidence a M k s) + v) ≤
              ‖subtotal (frosty x u (Period.side n)) ((L.drop start).take len)‖) ≤
                2 * Real.exp (-v / 2) := by
  filter_upwards [paperCircleHistoryThread_paid_interval_tail a M k s] with j hj u n v
  simpa only [neg_div, two_mul] using hj u n (v / 2) v

end
end RHTower
