import GaloisForLFunctions.RHTower.PaperCircleAdaptiveHistory
import GaloisForLFunctions.HTGeometry.PaperFourierLLogL.Edges.Global

/-! # Exact spatial information and adaptive boundary budgets

Completing every spatial bit turns the source's entropy inequality into an exact
identity. Applied to native observation histories, this identifies the full reveal
cost with the posterior's entropy deficit, and supplies uniform boundary budgets
for every state-dependent scale policy along a certified adaptive road.
-/

open Filter
open scoped BigOperators NNReal Classical
open GaloisForLFunctions.HTGeometry.FourierLLogL
open GaloisForLFunctions.HTGeometry.FourierLLogL.Dyadic
open GaloisForLFunctions.HTGeometry.FourierLLogL.Dyadic.Procedure
open Law Node Scene Fork Wire Pulse

namespace RHTower
noncomputable section
variable {ι : Type*} [Fintype ι]

private lemma split_entropy {M : ℕ} (v : Fork M) (ht : v.TrueLaw) :
    v.probs.Ex (fun b => (v.dst b).actor.entropy) =
      v.src.actor.entropy - v.probs.entropy := by
  let unit := fun _ : Grid M => uniform Unit
  have he := conditioned_balance unit v ht
  have hx : sideH v unit = v.probs.entropy := by
    let P := v.src.actor.tensorP (uniform Unit)
    let q := fun i : Grid M × Unit => v.bit i.1
    have HS : P.send q = v.probs := by
      have HH := P.send_send Prod.fst v.bit
      rw [send_fst_tensorP] at HH
      exact HH.symm
    change P.Hcond q Prod.snd = _
    rw [Hcond_right_partition (Z := fun _ => ()) _ _ (fun i j => by simp)]
    rw [Hcond_constant, Law.H, HS]
  simp only [unit, privateH_const] at he
  unfold unit at hx
  linarith

private lemma full_wire_balance {M : ℕ} {s : Scene M} (t : Wire M s)
    (a : Bool) (h : t.Valid a) (hm : 0 < s.mass) :
    t.expenditure (due 0) = levels s - s.actor.entropy + t.spotDebt := by
  induction t generalizing a with
  | term s =>
    have hl : levels s = 0 := by simp [levels, h.2]
    have he : s.actor.entropy = 0 := by
      apply le_antisymm
      · simpa only [hl] using cap_entropy s h.1.1 h.1.2 hm
      · exact entropy_nonneg _
    simp [expenditure, Wire.read, spotDebt, Ex_const, hl, he]
  | stay s v k ih =>
    rw [fee_stay]
    cases v <;> exact ih _ h.2 hm
  | spot s u k ih =>
    obtain ⟨hs, hS, hv, h⟩ := h
    let v := u.snip
    have hb := hv hm
    rw [fee_spot _ _ _ hb, spotDebt]
    have Hx (b : Bool) (hx : 0 < v.probs b) :=
      ih b _ (h _) ((true_mass hb).mp hx)
    have HH := v.probs.Ex_congr_mem Hx
    have hl (b) : levels (u.dst b) = levels s := by unfold levels; rw [hS]
    rw [Ex_add, Ex_sub] at HH
    simp_rw [hl, Ex_const] at HH
    have h1 := split_entropy v hb
    change v.probs.Ex (fun b => (u.dst b).actor.entropy) =
      s.actor.entropy - v.probs.entropy at h1
    unfold v at *
    linarith
  | link s v k ih =>
    obtain ⟨hs, hS, hv, h⟩ := h
    let U := step s
    have hb := step_true hs.1.1 hS hs.2 hm
    rw [fee_link v k _ hb, spotDebt]
    have Hx (b : Bool) (hx : 0 < U.probs b) :=
      ih b _ (h _) ((true_mass hb).mp hx)
    have Hh := U.probs.Ex_congr_mem Hx
    simp_rw [due, true_or, ite_true]
    rw [Ex_add]
    simp_rw [signal, Ex_const]
    rw [Ex_add, Ex_sub] at Hh
    simp_rw [levels_child _ hS, Ex_const] at Hh
    have hh := split_entropy U hb
    change U.probs.Ex (fun b => (s.smaller b).actor.entropy) =
      s.actor.entropy - U.probs.entropy at hh
    unfold pitch
    unfold U at *
    linarith

private lemma begin_levels (a : ι → CCMCircleBoundedSymbol) (M k : ℕ)
    (s : List (ℝ≥0 × Grid M)) :
    levels (paperCircleHistoryBegin a M k s) = M * Real.log 2 := by
  simp [levels, paperCircleHistoryBegin, beginPlay, Node.root]

/-- Reveal all grid bits while keeping the actual observation likelihood fixed. -/
def paperCircleHistoryFullReveal (a : ι → CCMCircleBoundedSymbol) (M k : ℕ)
    (s : List (ℝ≥0 × Grid M)) : Wire M (paperCircleHistoryBegin a M k s) :=
  Wire.extra (paperCircleHistoryBegin a M k s) M

theorem paperCircleHistoryFullReveal_valid (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (s : List (ℝ≥0 × Grid M)) :
    (paperCircleHistoryFullReveal a M k s).Valid true := by
  apply Wire.extra_ok
  · exact ⟨Node.root_ok M, fun x => (paperCircleHistoryLikelihood_pos a M k s x).le⟩
  · simp [paperCircleHistoryBegin, beginPlay, Node.root]

/-- Full spatial information is exactly the entropy deficit of the actual posterior. -/
theorem paperCircleHistoryFullReveal_entropy (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (s : List (ℝ≥0 × Grid M)) :
    (paperCircleHistoryPosterior a M k s).Ex
      (fun x => (((paperCircleHistoryFullReveal a M k s).read x).map (due 0)).sum) =
        M * Real.log 2 - (paperCircleHistoryPosterior a M k s).entropy := by
  have h := full_wire_balance (paperCircleHistoryFullReveal a M k s) true
    (paperCircleHistoryFullReveal_valid a M k s) (paperCircleHistoryBegin_mass_pos a M k s)
  simpa only [paperCircleHistoryFullReveal, Wire.extraDebt, add_zero, begin_levels,
    Wire.expenditure, paperCircleHistoryBegin_actor] using h

/-- One actual adaptive road with exact entropy accounting and both source edge budgets. -/
structure PaperCircleHistoryBoundaryCertificate (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (s : List (ℝ≥0 × Grid M)) (j : ℕ)
    (road : Road j M (paperCircleHistoryBegin a M k s)) : Prop where
  roadCertificate : PaperCircleHistoryRoadCertificate a M k s j road
  completed : (Wire.tape road).Valid true
  entropy_balance : (paperCircleHistoryPosterior a M k s).Ex
    (fun x => (((Wire.tape road).read x).map (due 0)).sum) =
      M * Real.log 2 - (paperCircleHistoryPosterior a M k s).entropy +
        (paperCircleHistoryPosterior a M k s).Ex (fun x => (road.hike x).membership)
  entropy_budget : (paperCircleHistoryPosterior a M k s).Ex
    (fun x => (((Wire.tape road).read x).map (due 0)).sum) ≤
      M * Real.log 2 - (paperCircleHistoryPosterior a M k s).entropy +
        Road.limitC * Thermal.H j
  adaptive_edges : ∀ p : Wire.Policy M,
    (paperCircleHistoryPosterior a M k s).Ex
      (fun x => (road.hike x).fee (Event.edgeFee p false)) ≤
        1000 * Compress.Params.height j
  indexed_edges : ∀ i : Fin (Thermal.testIx j + 1),
    (paperCircleHistoryPosterior a M k s).Ex
      (fun x => (road.hike x).fee (Event.edgeFee (fun _ => i.val) true)) ≤
        10000 * Road.limitC * Thermal.H j

/-- Every native history has a road satisfying every policy bound at once. -/
theorem paperCircleHistory_certified_boundary_exists (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (s : List (ℝ≥0 × Grid M)) (throughCold : Bool) :
    ∀ᶠ j : ℕ in atTop, ∃ road : Road j M (paperCircleHistoryBegin a M k s),
      PaperCircleHistoryBoundaryCertificate a M k s j road := by
  filter_upwards [paperCircleHistory_certified_road_exists a M k s throughCold,
    paperCircleHistoryBegin_mass_ready a M k s, global_edges] with j hc hm he
  obtain ⟨road, hc⟩ := hc
  have hp := paperCircleHistoryBegin_mass_pos a M k s
  have ht := Wire.tape_ok road hc.trusted
  have hactor := paperCircleHistoryBegin_actor a M k s
  have hb := full_wire_balance (Wire.tape road) true ht hp
  rw [Wire.debt_like road hc.trusted hp, begin_levels] at hb
  have hexact : (paperCircleHistoryPosterior a M k s).Ex
      (fun x => (((Wire.tape road).read x).map (due 0)).sum) =
      M * Real.log 2 - (paperCircleHistoryPosterior a M k s).entropy +
        (paperCircleHistoryPosterior a M k s).Ex (fun x => (road.hike x).membership) := by
    simpa only [Wire.expenditure, Road.flatFee, Road.expHike, hactor,
      Journal.membership] using hb
  have hedge := he M M (paperCircleHistoryLikelihood a M k s)
    (fun x => (paperCircleHistoryLikelihood_le_one a M k s x).trans
      (Real.one_le_exp (Thermal.d_pos j).le)) road hc.trusted hm
  refine ⟨road, {
    roadCertificate := hc
    completed := ht
    entropy_balance := hexact
    entropy_budget := ?_
    adaptive_edges := ?_
    indexed_edges := ?_ }⟩
  · rw [hexact]
    exact add_le_add le_rfl hc.membership_mean
  · intro p
    have h := hedge.1 p
    change (paperCircleHistoryBegin a M k s).actor.Ex
      (fun x => (road.hike x).fee (Event.edgeFee p false)) ≤ _ at h
    simpa only [hactor] using h
  · intro i
    have h := hedge.2 i.val (by omega)
    change (paperCircleHistoryBegin a M k s).actor.Ex
      (fun x => (road.hike x).fee (Event.edgeFee (fun _ => i.val) true)) ≤ _ at h
    simpa only [hactor] using h

end
end RHTower
