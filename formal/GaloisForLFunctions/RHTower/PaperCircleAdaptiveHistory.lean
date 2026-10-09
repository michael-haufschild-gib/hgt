import GaloisForLFunctions.RHTower.PaperCircleObservationHistory
import GaloisForLFunctions.HTGeometry.PaperFourierLLogL.Procedure.Fisher

/-! # Certified adaptive histories for native circle observations

The actual history likelihood satisfies every input condition of the source's
terminating procedure. Its input actor is exactly the native posterior. For every
fixed history, sufficiently large procedure scales also pay all mass requirements,
giving unconditional existence of adaptive roads with explicit probability budgets.
-/

open Filter
open scoped BigOperators NNReal
open GaloisForLFunctions.HTGeometry.FourierLLogL
open GaloisForLFunctions.HTGeometry.FourierLLogL.Dyadic
open GaloisForLFunctions.HTGeometry.FourierLLogL.Dyadic.Procedure

namespace RHTower
noncomputable section
variable {ι : Type*} [Fintype ι]

def paperCircleHistoryBegin (a : ι → CCMCircleBoundedSymbol) (M k : ℕ)
    (s : List (ℝ≥0 × Grid M)) : Scene M :=
  Scene.beginPlay (paperCircleHistoryLikelihood a M k s) true

theorem paperCircleHistoryBegin_mass (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (s : List (ℝ≥0 × Grid M)) :
    (paperCircleHistoryBegin a M k s).mass = paperCircleHistoryEvidence a M k s :=
  top_avg _

theorem paperCircleHistoryBegin_mass_pos (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (s : List (ℝ≥0 × Grid M)) :
    0 < (paperCircleHistoryBegin a M k s).mass := by
  rw [paperCircleHistoryBegin_mass]
  exact paperCircleHistoryEvidence_pos a M k s

/-- The adaptive procedure samples the actual posterior, with all normalization obligations paid. -/
theorem paperCircleHistoryBegin_actor (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (s : List (ℝ≥0 × Grid M)) :
    (paperCircleHistoryBegin a M k s).actor = paperCircleHistoryPosterior a M k s := by
  apply Law.ext
  intro x
  have hx : x ∈ Node.root.block M := (Node.mem_group _ _).mp (by
    rw [Node.group_top]
    exact Finset.mem_univ x)
  rw [Scene.actor_def (Node.root_ok M)
    (fun x => (paperCircleHistoryLikelihood_pos a M k s x).le)
    (paperCircleHistoryBegin_mass_pos a M k s) x, Thermal.wt]
  change Node.root.dice M x * paperCircleHistoryLikelihood a M k s x /
    Node.root.avg (paperCircleHistoryLikelihood a M k s) = _
  rw [Node.dice_apply (Node.root_ok M), if_pos hx, Node.len_top, inv_one, mul_one,
    top_avg, paperCircleHistoryPosterior_apply]
  rfl

/-- Positive evidence eventually exceeds the procedure's decreasing mass threshold. -/
theorem paperCircleHistoryBegin_mass_ready (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (s : List (ℝ≥0 × Grid M)) :
    ∀ᶠ j : ℕ in atTop, 1 / Thermal.H j ≤ (paperCircleHistoryBegin a M k s).mass := by
  filter_upwards [Thermal.h_large (1 / paperCircleHistoryEvidence a M k s)] with j hj
  rw [paperCircleHistoryBegin_mass]
  apply (div_le_iff₀ (Thermal.H_pos j)).mpr
  have h := (div_le_iff₀ (paperCircleHistoryEvidence_pos a M k s)).mp hj
  nlinarith

/-- The source's existence theorem applies to every actual native observation history. -/
theorem paperCircleHistory_play_exists (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (s : List (ℝ≥0 × Grid M)) :
    ∀ᶠ j : ℕ in atTop, ∃ t : Play j M (paperCircleHistoryBegin a M k s),
      t.Follows M (paperCircleHistoryLikelihood a M k s) := by
  filter_upwards [plant] with j hj
  exact hj M M le_rfl (paperCircleHistoryLikelihood a M k s)
    (fun x => (paperCircleHistoryLikelihood_pos a M k s x).le)
    ((paperCircleHistoryEvidence_le_one a M k s).trans (by norm_num))
    (fun x => (paperCircleHistoryLikelihood_le_one a M k s x).trans
      (Real.one_le_exp (Thermal.d_pos j).le)) true

/-- All statements refer to the actual native posterior and the actual path taken by its input. -/
structure PaperCircleHistoryRoadCertificate (a : ι → CCMCircleBoundedSymbol) (M k : ℕ)
    (s : List (ℝ≥0 × Grid M)) (j : ℕ)
    (road : Road j M (paperCircleHistoryBegin a M k s)) : Prop where
  trusted : road.Trusted M (paperCircleHistoryLikelihood a M k s)
  terminal_mass : ∀ x : Grid M, 0 < (road.hike x).done.mass
  likelihood_identity : ∀ x : Grid M,
    (road.hike x).like = Real.log (road.hike x).done.mass -
      Real.log (paperCircleHistoryEvidence a M k s) + (road.hike x).membership
  inverse_likelihood : (paperCircleHistoryPosterior a M k s).Ex
    (fun x => Real.exp (-(road.hike x).like)) ≤ 1
  negative_likelihood : (paperCircleHistoryPosterior a M k s).Ex
    (fun x => (max (-(road.hike x).like) 0)^2) ≤ 4
  membership_mean : (paperCircleHistoryPosterior a M k s).Ex
    (fun x => (road.hike x).membership) ≤ Road.limitC * Thermal.H j
  membership_square : (paperCircleHistoryPosterior a M k s).Ex
    (fun x => (road.hike x).membership^2) ≤ (Road.limitC * Thermal.H j)^2
  terminal_log_mass : (paperCircleHistoryPosterior a M k s).Ex
    (fun x => (max (-Real.log (road.hike x).done.mass) 0)^2) ≤
      (10 * Road.limitC * Thermal.H j)^2
  successes : (paperCircleHistoryPosterior a M k s).Ex
    (fun x => (road.hike x).fee Event.count) ≤ capA * Thermal.H j
  starts : (paperCircleHistoryPosterior a M k s).Ex
    (fun x => (road.hike x).fee Road.beginFee) ≤ 100 * Road.limitC * Thermal.H j
  attempts : (paperCircleHistoryPosterior a M k s).Ex
    (fun x => (road.hike x).fee Event.tried) ≤ 12800 * capA * Thermal.H j^33
  information : (paperCircleHistoryPosterior a M k s).Ex
    (fun x => (road.hike x).fee Event.infoFee) ≤ Road.limitC * Compress.Params.height j

/-- Every fixed native history admits certified adaptive roads and all source budgets,
without assuming a trusted tree, positive mass threshold, or analytic estimate. -/
theorem paperCircleHistory_certified_road_exists (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (s : List (ℝ≥0 × Grid M)) (throughCold : Bool) :
    ∀ᶠ j : ℕ in atTop, ∃ road : Road j M (paperCircleHistoryBegin a M k s),
      PaperCircleHistoryRoadCertificate a M k s j road := by
  filter_upwards [paperCircleHistory_play_exists a M k s,
    paperCircleHistoryBegin_mass_ready a M k s, Road.mem_budget, Road.log_mass_budget,
    Road.final_coarse, Road.attempt_count, Road.fisher_bound]
      with j hp hm hmem hlog hcoarse hattempt hfisher
  obtain ⟨play, hplay⟩ := hp
  let road := Road.trace throughCold play
  have hr : road.Trusted M (paperCircleHistoryLikelihood a M k s) :=
    Road.traced play throughCold hplay
  have hpos := paperCircleHistoryBegin_mass_pos a M k s
  have hactor := paperCircleHistoryBegin_actor a M k s
  have Hmem := hmem M M _ _ road hr hpos
  have Hlog := hlog M M _ _ road hr hm
  have Hcoarse := hcoarse M M _ _ road hr hm
  have Hattempt := hattempt M M _ _ road hr hm
  have Hfisher := hfisher M M (paperCircleHistoryLikelihood a M k s)
    (fun x => (paperCircleHistoryLikelihood_le_one a M k s x).trans
      (Real.one_le_exp (Thermal.d_pos j).le)) road hr hm
  have Hpath (x : Grid M) := Road.final_sound hr hpos
    (show 0 < (paperCircleHistoryBegin a M k s).actor x by
      rw [hactor]
      exact paperCircleHistoryPosterior_pos a M k s x)
  refine ⟨road, {
    trusted := hr
    terminal_mass := fun x => (Hpath x).2.2.1
    likelihood_identity := ?_
    inverse_likelihood := ?_
    negative_likelihood := ?_
    membership_mean := ?_
    membership_square := ?_
    terminal_log_mass := ?_
    successes := ?_
    starts := ?_
    attempts := ?_
    information := ?_ }⟩
  · intro x
    simpa only [paperCircleHistoryBegin_mass] using (Hpath x).2.2.2.1
  · simpa only [Road.expHike, hactor] using Road.minus_like_cap road hr hpos
  · simpa only [Road.expHike, hactor] using Road.neg_like_budget road hr hpos
  · simpa only [Road.expHike, hactor] using Hmem.2
  · simpa only [Road.expHike, hactor] using Hmem.1
  · simpa only [Road.expHike, hactor] using Hlog
  · simpa only [Road.flatFee, Road.expHike, hactor] using Hcoarse.2.1
  · simpa only [Road.flatFee, Road.expHike, hactor] using Hcoarse.2.2 rfl
  · simpa only [Road.flatFee, Road.expHike, hactor] using Hattempt
  · change (paperCircleHistoryBegin a M k s).actor.Ex
      (fun x => (road.hike x).fee Event.infoFee) ≤ _ at Hfisher
    simpa only [hactor] using Hfisher

end
end RHTower
