import GaloisForLFunctions.RHTower.PaperCircleAdaptiveWager
import GaloisForLFunctions.HTGeometry.PaperFourierLLogL.Paths.Frost

/-! # Evidence-paid fluctuations on every interval of an actual adaptive path

Normalization makes the selected native thread a genuine source trip. Eight
predictable wagers control its complex fluctuations. Conditioning costs only the
actual history evidence; selecting an interval carries no additional union cost.
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

theorem paperCircleHistoryNormalizedBegin_fit (a : ι → CCMCircleBoundedSymbol) (M k : ℕ)
    (s : List (ℝ≥0 × Grid M)) : Fit (paperCircleHistoryBegin a M k s).reset := by
  have hm := paperCircleHistoryBegin_mass_pos a M k s
  refine ⟨⟨Node.root_ok M, fun x => (paperCircleHistoryLikelihood_pos a M k s x).le⟩,
    hm, ?_⟩
  change (paperCircleHistoryBegin a M k s).mass /
    (paperCircleHistoryBegin a M k s).mass ≤ 4
  rw [div_self hm.ne']
  norm_num

theorem paperCircleHistoryThread_trip (a : ι → CCMCircleBoundedSymbol) (M k : ℕ)
    (s : List (ℝ≥0 × Grid M)) :
    ∀ᶠ j : ℕ in atTop, ∀ x : Grid M, Trip x (paperCircleHistoryBegin a M k s).reset
      ((paperCircleHistoryThread a M k s j).stream x) := by
  filter_upwards [paperCircleHistoryThread_following a M k s] with j hj x
  apply trip_stream _ hj (paperCircleHistoryNormalizedBegin_fit a M k s)
  exact (Node.mem_group _ _).mp (by
    change x ∈ Node.root.group M
    rw [Node.group_top]
    exact Finset.mem_univ x)

/-- The eight component wagers have total posterior budget at most 17/evidence. -/
theorem paperCircleHistoryThread_cold_budget (a : ι → CCMCircleBoundedSymbol) (M k : ℕ)
    (s : List (ℝ≥0 × Grid M)) :
    ∀ᶠ j : ℕ in atTop, ∀ (u : Grid M) (b : ℝ),
      (paperCircleHistoryPosterior a M k s).Ex (fun x =>
        coldScore u b ((paperCircleHistoryThread a M k s j).stream x)) ≤
          17 / paperCircleHistoryEvidence a M k s := by
  filter_upwards [paperCircleHistoryThread_posterior_heat (E := Unit) a M k s,
    paperCircleHistoryThread_posterior_heat (E := ℝ) a M k s] with j hq hs u b
  let P := paperCircleHistoryPosterior a M k s
  let L := fun x => (paperCircleHistoryThread a M k s j).stream x
  let e := paperCircleHistoryEvidence a M k s
  have he : 0 < e := paperCircleHistoryEvidence_pos a M k s
  have he1 : e ≤ 1 := paperCircleHistoryEvidence_le_one a M k s
  let F := fun d : Face => P.Ex (fun x =>
    (Lens.mk u b d).quest.heatW () (L x) + (Lens.mk u b d).shifted.heatW 0 (L x))
  have hd (d : Face) : F d ≤ 4 / e := by
    dsimp [F]
    rw [Law.Ex_add]
    have h1 := hq (Lens.mk u b d).quest ()
    have h2 := hs (Lens.mk u b d).shifted 0
    change _ ≤ 2 / e at h1 h2
    exact (add_le_add h1 h2).trans_eq (by ring)
  have hsum : (∑ d : Face, F d) ≤ ∑ _d : Face, (4 / e) :=
    Finset.sum_le_sum fun d _ => hd d
  norm_num [Face] at hsum
  have h1 : 1 ≤ 1 / e := (le_div_iff₀ he).mpr (by simpa using he1)
  change P.Ex (fun x => coldScore u b (L x)) ≤ 17 / e
  unfold coldScore
  rw [Law.Ex_add, Law.Ex_const, Law.Ex_finset_sum]
  change 1 + ∑ d : Face, F d ≤ 17 / e
  exact (add_le_add h1 hsum).trans_eq (by ring)

private lemma score_log_tail {α : Type} [Fintype α] (P : Law α) (Y : α → ℝ)
    (hY : ∀ x, 0 < Y x) (C : ℝ) (hC : 0 < C) (h : P.Ex Y ≤ C) (v : ℝ) :
    P.prob (fun x => 2 * Real.log C + v ≤ 2 * Real.log (Y x)) ≤ Real.exp (-v / 2) := by
  let t := 2 * Real.log C + v
  have ht := P.upperTail (fun x => t ≤ 2 * Real.log (Y x)) Y
    (fun x => (hY x).le) (Real.exp (t / 2)) (fun x hx => by
      rw [← Real.exp_log (hY x)]
      apply Real.exp_le_exp.mpr
      linarith only [hx])
  have hid : Real.exp (t / 2) * Real.exp (-v / 2) = C := by
    rw [← Real.exp_add, show t / 2 + -v / 2 = Real.log C by dsimp [t]; ring,
      Real.exp_log hC]
  have hb := ht.trans h
  rw [← hid] at hb
  exact le_of_mul_le_mul_left hb (Real.exp_pos _)

theorem paperCircleHistoryThread_cold_tail (a : ι → CCMCircleBoundedSymbol) (M k : ℕ)
    (s : List (ℝ≥0 × Grid M)) :
    ∀ᶠ j : ℕ in atTop, ∀ (u : Grid M) (b v : ℝ),
      (paperCircleHistoryPosterior a M k s).prob (fun x =>
        2 * Real.log (17 / paperCircleHistoryEvidence a M k s) + v ≤
          2 * Real.log (coldScore u b ((paperCircleHistoryThread a M k s j).stream x))) ≤
            Real.exp (-v / 2) := by
  filter_upwards [paperCircleHistoryThread_cold_budget a M k s] with j hj u b v
  exact score_log_tail _ _ (fun x => lt_of_lt_of_le (by norm_num) (cold_one u b _)) _
    (div_pos (by norm_num) (paperCircleHistoryEvidence_pos a M k s)) (hj u b) v

/-- Every contiguous interval shares one whole-path logarithmic fluctuation budget. -/
theorem paperCircleHistoryThread_interval_fluctuation (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (s : List (ℝ≥0 × Grid M)) :
    ∀ᶠ j : ℕ in atTop, ∀ (x u : Grid M) (n start len : ℕ),
      let L := (paperCircleHistoryThread a M k s j).stream x
      ‖subtotal (frosty x u (Period.side n)) ((L.drop start).take len)‖ ≤
        12000 * Real.sqrt (Period.side n) *
          (1 + fullKills L + 2 * Real.log (coldScore u (Period.side n) L)) := by
  filter_upwards [paperCircleHistoryThread_trip a M k s] with j hj x u n start len
  let L := (paperCircleHistoryThread a M k s j).stream x
  have hsplit : L.take start ++ (L.drop start).take len ++ (L.drop start).drop len = L := by
    rw [List.append_assoc, List.take_append_drop, List.take_append_drop]
  have htrip : Trip x (paperCircleHistoryBegin a M k s).reset
      (L.take start ++ (L.drop start).take len ++ (L.drop start).drop len) := by
    rw [hsplit]
    exact hj x
  have h := frosty_portion u (Period.side_pos n) (Period.side_le n)
    (L.take start) ((L.drop start).take len) ((L.drop start).drop len) htrip
    (2 * Real.log (coldScore u (Period.side n) L)) (by rw [hsplit])
  simpa only [hsplit] using h

/-- Choosing an interval after seeing the path incurs no extra cardinality factor. -/
theorem paperCircleHistoryThread_any_interval_tail (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (s : List (ℝ≥0 × Grid M)) :
    ∀ᶠ j : ℕ in atTop, ∀ (u : Grid M) (n : ℕ) (v : ℝ),
      (paperCircleHistoryPosterior a M k s).prob (fun x =>
        let L := (paperCircleHistoryThread a M k s j).stream x
        ∃ start len : ℕ, 12000 * Real.sqrt (Period.side n) *
          (1 + fullKills L + 2 * Real.log (17 / paperCircleHistoryEvidence a M k s) + v) ≤
            ‖subtotal (frosty x u (Period.side n)) ((L.drop start).take len)‖) ≤
              Real.exp (-v / 2) := by
  filter_upwards [paperCircleHistoryThread_interval_fluctuation a M k s,
    paperCircleHistoryThread_cold_tail a M k s] with j hf ht u n v
  apply le_trans (Law.prob_mono _ _ _ ?_) (ht u (Period.side n) v)
  rintro x ⟨start,len,h⟩
  have hb := h.trans (hf x u n start len)
  have hc : 0 < 12000 * Real.sqrt (Period.side n) :=
    mul_pos (by norm_num) (Real.sqrt_pos.mpr (Period.side_pos n))
  have hi := le_of_mul_le_mul_left hb hc
  linarith only [hi]

end
end RHTower
