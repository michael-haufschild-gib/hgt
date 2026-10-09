import GaloisForLFunctions.RHTower.PaperCircleAdaptiveBudget
import GaloisForLFunctions.HTGeometry.PaperFourierLLogL.Paths.Encore

/-! # Frequency selection paid by the actual adaptive history

Both scalar and vector selection run on the certified native thread. The selected
frequency set, its binary capacity, its score envelope and its logarithmic cost
have unconditional uniform and posterior budgets. The observation evidence pays
conditioning; the vector depth requirement holds eventually at every fixed level.
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

def paperCircleHistoryFrequencySet (a : ι → CCMCircleBoundedSymbol) (M k : ℕ)
    (s : List (ℝ≥0 × Grid M)) (j : ℕ) (main : Bool) (n : ℕ) (x : Grid M) : Finset (Grid M) :=
  (Capture.goal n main (Capture.Chart.classic M)
    ((paperCircleHistoryThread a M k s j).stream x)).items

def paperCircleHistorySelectionCapacity (a : ι → CCMCircleBoundedSymbol) (M k : ℕ)
    (s : List (ℝ≥0 × Grid M)) (j : ℕ) (main : Bool) (n : ℕ) (x : Grid M) : ℕ :=
  Nat.log 2 (paperCircleHistoryFrequencySet a M k s j main n x).card + 1

def paperCircleHistorySelectionScore (a : ι → CCMCircleBoundedSymbol) (M k : ℕ)
    (s : List (ℝ≥0 × Grid M)) (j : ℕ) (main : Bool) (n : ℕ) (x : Grid M) : ℝ :=
  Troupe.spillScore ⟨main,n⟩ j ((paperCircleHistoryThread a M k s j).stream x)

def paperCircleHistorySelectionCost (a : ι → CCMCircleBoundedSymbol) (M k : ℕ)
    (s : List (ℝ≥0 × Grid M)) (j : ℕ) (main : Bool) (n : ℕ) (x : Grid M) : ℝ :=
  Troupe.timex ⟨main,n⟩ j ((paperCircleHistoryThread a M k s j).stream x)

def paperCircleHistorySelectionHeight (a : ι → CCMCircleBoundedSymbol) (M k : ℕ)
    (s : List (ℝ≥0 × Grid M)) (j : ℕ) : ℝ :=
  Compress.Params.height j - Real.log (paperCircleHistoryEvidence a M k s) + 2

theorem paperCircleHistorySelectionHeight_source (a : ι → CCMCircleBoundedSymbol) (M k : ℕ)
    (s : List (ℝ≥0 × Grid M)) (j : ℕ) :
    Troupe.amount (paperCircleHistoryBegin a M k s).reset j =
      paperCircleHistorySelectionHeight a M k s j := by
  have hlog := Real.log_nonpos (paperCircleHistoryEvidence_pos a M k s).le
    (paperCircleHistoryEvidence_le_one a M k s)
  change Compress.Params.height j + max (-Real.log (paperCircleHistoryBegin a M k s).mass) 0 + 2 = _
  rw [paperCircleHistoryBegin_mass, max_eq_left (neg_nonneg.mpr hlog)]
  rfl

theorem paperCircleHistorySelectionHeight_ge_one (a : ι → CCMCircleBoundedSymbol) (M k : ℕ)
    (s : List (ℝ≥0 × Grid M)) (j : ℕ) : 1 ≤ paperCircleHistorySelectionHeight a M k s j := by
  rw [← paperCircleHistorySelectionHeight_source]
  exact (Troupe.amount_limits _ _).1

/-- The chosen binary capacity covers exactly the path's selected frequency set. -/
theorem paperCircleHistorySelectionCapacity_spec (a : ι → CCMCircleBoundedSymbol) (M k : ℕ)
    (s : List (ℝ≥0 × Grid M)) (j : ℕ) (main : Bool) (n : ℕ) (x : Grid M) :
    paperCircleHistorySelectionCapacity a M k s j main n x ≤ M + 2 ∧
      (paperCircleHistoryFrequencySet a M k s j main n x).card ≤
        2 ^ paperCircleHistorySelectionCapacity a M k s j main n x ∧
      (2 : ℝ) ^ paperCircleHistorySelectionCapacity a M k s j main n x ≤
        2 * ((paperCircleHistoryFrequencySet a M k s j main n x).card + 1) :=
  Troupe.choice_bounds ⟨main,n⟩ ((paperCircleHistoryThread a M k s j).stream x)

theorem paperCircleHistorySelectionScore_ge_one (a : ι → CCMCircleBoundedSymbol) (M k : ℕ)
    (s : List (ℝ≥0 × Grid M)) (j : ℕ) (main : Bool) (n : ℕ) (x : Grid M) :
    1 ≤ paperCircleHistorySelectionScore a M k s j main n x :=
  (Troupe.spill_share ⟨main,n⟩ j ((paperCircleHistoryThread a M k s j).stream x)).1

theorem paperCircleHistorySelectionCost_nonneg (a : ι → CCMCircleBoundedSymbol) (M k : ℕ)
    (s : List (ℝ≥0 × Grid M)) (j : ℕ) (main : Bool) (n : ℕ) (x : Grid M) :
    0 ≤ paperCircleHistorySelectionCost a M k s j main n x :=
  (Troupe.timex_scores ⟨main,n⟩ j ((paperCircleHistoryThread a M k s j).stream x)).1

/-- Both selection modes are entitled eventually at each fixed level. -/
theorem paperCircleHistorySelection_entitled (a : ι → CCMCircleBoundedSymbol) (M k : ℕ)
    (s : List (ℝ≥0 × Grid M)) (n : ℕ) :
    ∀ᶠ j : ℕ in atTop, ∀ main : Bool,
      Troupe.entitled ⟨main,n⟩ (paperCircleHistoryBegin a M k s).reset j := by
  filter_upwards [(tendsto_atTop.1 Compress.Params.ell_tendsto) n] with j hj main _
  refine ⟨?_,rfl⟩
  change n ≤ 16 * Compress.Params.ell j
  omega

private lemma native_selection_stats (a : ι → CCMCircleBoundedSymbol) (M k : ℕ)
    (s : List (ℝ≥0 × Grid M)) (j : ℕ) (F : Path M → ℝ) :
    stats (paperCircleHistoryThread a M k s j) F =
      (Law.uniform (Grid M)).Ex (fun x => F ((paperCircleHistoryThread a M k s j).stream x)) := by
  change (Node.root.dice M).Ex _ = _
  rw [← Node.avg_ex (Node.root_ok M), top_avg, expU_ex]

/-- Cardinality, binary capacity, score and logarithmic cost are paid together. -/
theorem paperCircleHistorySelection_uniform_bounds (a : ι → CCMCircleBoundedSymbol) (M k : ℕ)
    (s : List (ℝ≥0 × Grid M)) (n : ℕ) :
    ∀ᶠ j : ℕ in atTop, ∀ main : Bool,
      let c := (paperCircleHistoryBegin a M k s).reset
      let U := Law.uniform (Grid M)
      let H := paperCircleHistorySelectionHeight a M k s j
      U.Ex (fun x => ((paperCircleHistoryFrequencySet a M k s j main n x).card : ℝ)) ≤
          10^31 * ((2 : ℝ)^n)^6 * H ∧
        U.Ex (fun x => (paperCircleHistorySelectionCapacity a M k s j main n x : ℝ)) ≤
          10^6 * (1 + Real.log H + n) ∧
        U.Ex (paperCircleHistorySelectionScore a M k s j main n) ≤
          4 * Troupe.heartP c ⟨main,n⟩ j ∧
        U.Ex (paperCircleHistorySelectionCost a M k s j main n) ≤
          10^7 * (1 + Real.log H + n + Troupe.cutBook ⟨main,n⟩ c j) := by
  filter_upwards [Troupe.prelude, Troupe.spill_bound, Troupe.paid_levels,
    paperCircleHistoryThread_following a M k s,
    paperCircleHistorySelection_entitled a M k s n] with j hp hb hl hj he main
  have hf := paperCircleHistoryNormalizedBegin_fit a M k s
  have hentry : Troupe.entry (paperCircleHistoryBegin a M k s).reset := rfl
  have hupper (x : Grid M) : paperCircleHistoryLikelihood a M k s x ≤
      Real.exp (Compress.Params.height j) :=
    (paperCircleHistoryLikelihood_le_one a M k s x).trans
      (Real.one_le_exp (Thermal.d_pos j).le)
  have hcard := (hp M M _ _ _ hj hf hentry hupper (Troupe.stage ⟨main,n⟩ 0)).2
  have hscore := hb M M _ _ _ hj hf hentry hupper ⟨main,n⟩ (he main)
  obtain ⟨hcost,hcap⟩ := hl M M _ _ _ hj hf hentry hupper ⟨main,n⟩ (he main)
  rw [native_selection_stats] at hcard hscore hcost hcap
  simp only [Troupe.dBase, paperCircleHistorySelectionHeight_source] at hcost hcap
  change (Law.uniform (Grid M)).Ex (fun x =>
    ((paperCircleHistoryFrequencySet a M k s j main n x).card : ℝ)) ≤
      10^31 * ((2 : ℝ)^n)^6 * Troupe.amount (paperCircleHistoryBegin a M k s).reset j at hcard
  rw [paperCircleHistorySelectionHeight_source] at hcard
  exact ⟨hcard,hcap,hscore,hcost⟩

private lemma selection_posterior_bound (a : ι → CCMCircleBoundedSymbol) (M k : ℕ)
    (s : List (ℝ≥0 × Grid M)) (f : Grid M → ℝ) (hf : ∀ x, 0 ≤ f x)
    (B : ℝ) (hb : (Law.uniform (Grid M)).Ex f ≤ B) :
    (paperCircleHistoryPosterior a M k s).Ex f ≤ B / paperCircleHistoryEvidence a M k s := by
  have h := paperCircleHistoryPosterior_absolute_expectation a M k s f
  simp_rw [abs_of_nonneg (hf _)] at h
  exact (le_div_iff₀ (paperCircleHistoryEvidence_pos a M k s)).mpr
    (by simpa only [mul_comm] using h.trans hb)

/-- The actual observation evidence pays every adaptive selection budget. -/
theorem paperCircleHistorySelection_posterior_bounds (a : ι → CCMCircleBoundedSymbol) (M k : ℕ)
    (s : List (ℝ≥0 × Grid M)) (n : ℕ) :
    ∀ᶠ j : ℕ in atTop, ∀ main : Bool,
      let c := (paperCircleHistoryBegin a M k s).reset
      let P := paperCircleHistoryPosterior a M k s
      let E := paperCircleHistoryEvidence a M k s
      let H := paperCircleHistorySelectionHeight a M k s j
      P.Ex (fun x => ((paperCircleHistoryFrequencySet a M k s j main n x).card : ℝ)) ≤
          (10^31 * ((2 : ℝ)^n)^6 * H) / E ∧
        P.Ex (fun x => (paperCircleHistorySelectionCapacity a M k s j main n x : ℝ)) ≤
          (10^6 * (1 + Real.log H + n)) / E ∧
        P.Ex (paperCircleHistorySelectionScore a M k s j main n) ≤
          (4 * Troupe.heartP c ⟨main,n⟩ j) / E ∧
        P.Ex (paperCircleHistorySelectionCost a M k s j main n) ≤
          (10^7 * (1 + Real.log H + n + Troupe.cutBook ⟨main,n⟩ c j)) / E := by
  filter_upwards [paperCircleHistorySelection_uniform_bounds a M k s n] with j hj main
  obtain ⟨hcard,hcap,hscore,hcost⟩ := hj main
  exact ⟨selection_posterior_bound a M k s _ (fun _ => Nat.cast_nonneg _) _ hcard,
    selection_posterior_bound a M k s _ (fun _ => Nat.cast_nonneg _) _ hcap,
    selection_posterior_bound a M k s _ (fun x => zero_le_one.trans
      (paperCircleHistorySelectionScore_ge_one a M k s j main n x)) _ hscore,
    selection_posterior_bound a M k s _
      (paperCircleHistorySelectionCost_nonneg a M k s j main n) _ hcost⟩

private lemma positive_mean_log_tail {α : Type} [Fintype α] (P : Law α)
    (Y : α → ℝ) (hY : ∀ x, 0 < Y x) (C : ℝ) (hC : 0 < C)
    (h : P.Ex Y ≤ C) (v : ℝ) :
    P.prob (fun x => Real.log C + v ≤ Real.log (Y x)) ≤ Real.exp (-v) := by
  have ht := P.upperTail _ Y (fun x => (hY x).le) (Real.exp (Real.log C + v))
    (fun x hx => by rw [← Real.exp_log (hY x)]; exact Real.exp_le_exp.mpr hx)
  have he : Real.exp (Real.log C + v) * Real.exp (-v) = C := by
    rw [← Real.exp_add, show Real.log C + v + -v = Real.log C by ring, Real.exp_log hC]
  have hb := (ht.trans h).trans_eq he.symm
  exact le_of_mul_le_mul_left hb (Real.exp_pos _)

/-- A logarithmic tail for the score paying all adaptively selected frequency representatives. -/
theorem paperCircleHistorySelection_score_tail (a : ι → CCMCircleBoundedSymbol) (M k : ℕ)
    (s : List (ℝ≥0 × Grid M)) (n : ℕ) :
    ∀ᶠ j : ℕ in atTop, ∀ (main : Bool) (v : ℝ),
      (paperCircleHistoryPosterior a M k s).prob (fun x =>
        Real.log ((4 * Troupe.heartP (paperCircleHistoryBegin a M k s).reset ⟨main,n⟩ j) /
          paperCircleHistoryEvidence a M k s) + v ≤
            Real.log (paperCircleHistorySelectionScore a M k s j main n x)) ≤ Real.exp (-v) := by
  filter_upwards [paperCircleHistorySelection_posterior_bounds a M k s n] with j hj main v
  have hpos : 0 < Troupe.heartP (paperCircleHistoryBegin a M k s).reset ⟨main,n⟩ j := by
    have hs := Troupe.scale_pos n
    have hm := (Troupe.amount_limits (paperCircleHistoryBegin a M k s).reset j).1
    unfold Troupe.heartP
    positivity
  exact positive_mean_log_tail _ _ (fun x => lt_of_lt_of_le (by norm_num)
    (paperCircleHistorySelectionScore_ge_one a M k s j main n x)) _
    (div_pos (mul_pos (by norm_num) hpos) (paperCircleHistoryEvidence_pos a M k s))
    (hj main).2.2.1 v

end
end RHTower
