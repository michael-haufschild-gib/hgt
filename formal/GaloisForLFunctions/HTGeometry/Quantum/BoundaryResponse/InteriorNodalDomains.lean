import GaloisForLFunctions.HTGeometry.Quantum.BoundaryResponse.BoundaryNodalDomains
import Mathlib.Logic.Equiv.Sum

/-!
# Nodal domains of midpoint extensions

A positive-conductance midpoint of nonzero value has the sign of at least one of
its endpoints. Two same-sign boundary vertices connected by an effective
edge remain connected through their midpoint. Thus the effective network
controls the nodal components of the harmonic extension. Midpoints of
zero conductance contribute only isolated components.
-/

namespace GaloisForLFunctions.HTGeometry.BoundaryResponse

open WeightedGraph
open SimpleGraph

noncomputable section

variable {V : Type*}

/-- The nonzero vertices of a real graph function. -/
abbrev NodalSupport (x : V → ℝ) := {v : V // x v ≠ 0}

/-- The strong nodal graph keeps edges between nonzero vertices of the same sign. -/
def signedSupportGraph (B : SimpleGraph V) (x : V → ℝ) : SimpleGraph (NodalSupport x) where
  Adj u v := B.Adj u.1 v.1 ∧ 0 < x u.1 * x v.1
  symm := ⟨fun _ _ h => ⟨h.1.symm, by rw [mul_comm]; exact h.2⟩⟩
  loopless := ⟨fun _ h => h.1.ne rfl⟩

private theorem sameSign_trans {a b c : ℝ} (hab : 0 < a * b) (hbc : 0 < b * c) :
    0 < a * c := by
  rcases mul_pos_iff.mp hab with h | h
  · rcases mul_pos_iff.mp hbc with k | k
    · exact mul_pos h.1 k.2
    · exact (not_lt_of_gt h.2 k.1).elim
  · rcases mul_pos_iff.mp hbc with k | k
    · exact (not_lt_of_gt k.1 h.2).elim
    · exact mul_pos_of_neg_of_neg h.1 k.2

private theorem sameSign_with_midpoint {a b : ℝ} (h : 0 < a * b) :
    0 < a * ((a + b) / 2) ∧ 0 < ((a + b) / 2) * b := by
  rcases mul_pos_iff.mp h with h | h
  · have hm : 0 < (a + b) / 2 := div_pos (add_pos h.1 h.2) (by norm_num)
    exact ⟨mul_pos h.1 hm, mul_pos hm h.2⟩
  · have hm : (a + b) / 2 < 0 := div_neg_of_neg_of_pos (add_neg h.1 h.2) (by norm_num)
    exact ⟨mul_pos_of_neg_of_neg h.1 hm, mul_pos_of_neg_of_neg hm h.2⟩

private theorem walk_values_eq {A W : Type*} {G : SimpleGraph W} (f : W → A)
    (h : ∀ {u v}, G.Adj u v → f u = f v) {u v : W} (p : G.Walk u v) :
    f u = f v := by
  induction p with
  | nil => rfl
  | cons he _ ih => exact (h he).trans ih

section Series

variable [DecidableEq V]

omit [DecidableEq V] in
/-- Positive conductance survives after retaining the direct boundary edges. -/
theorem residualBoundary_weight_pos_iff (G : WeightedGraph V) (B : SimpleGraph V) (u v : V) :
    0 < (G.residualBoundary B).w u v ↔ 0 < G.w u v := by
  classical
  change (0 < G.w u v - (if B.Adj u v then G.w u v / 2 else 0)) ↔ _
  by_cases h : B.Adj u v
  · rw [if_pos h]
    constructor <;> intro h' <;> linarith only [h']
  · rw [if_neg h, sub_zero]

/-- An interior vertex is wired to its two endpoints precisely when its
effective conductance is positive. -/
theorem seriesNetwork_wire_weight_pos_iff (G : WeightedGraph V) (B : SimpleGraph V)
    (u : V) (p : SeriesInterior V) :
    0 < (G.seriesNetwork B).w (.inl u) (.inr p) ↔
      (u = p.1.1 ∨ u = p.1.2) ∧ 0 < G.w p.1.1 p.1.2 := by
  let w := (G.residualBoundary B).w p.1.1 p.1.2
  change (0 < (if u = p.1.1 then w else 0) + (if u = p.1.2 then w else 0)) ↔ _
  by_cases h₁ : u = p.1.1
  · have h₂ : u ≠ p.1.2 := fun h => p.2 (h₁.symm.trans h)
    rw [if_pos h₁, if_neg h₂, add_zero]
    simp only [h₁, true_or, true_and]
    exact residualBoundary_weight_pos_iff G B p.1.1 p.1.2
  · by_cases h₂ : u = p.1.2
    · rw [if_neg h₁, if_pos h₂, zero_add]
      simp only [h₂, or_true, true_and]
      exact residualBoundary_weight_pos_iff G B p.1.1 p.1.2
    · rw [if_neg h₁, if_neg h₂, add_zero]
      simp only [lt_irrefl, h₁, h₂, or_self, false_and]

/-- The isolated interior vertices that survive in the nonzero support. -/
abbrev InactiveNodalMidpoint (G : WeightedGraph V) (x : V → ℝ) :=
  {p : SeriesInterior V // G.w p.1.1 p.1.2 = 0 ∧ seriesMidpointExtension x (.inr p) ≠ 0}

/-- Nodal connectivity in the effective boundary network. -/
abbrev effectiveNodalGraph (G : WeightedGraph V) (x : V → ℝ) :=
  signedSupportGraph (positiveNetworkSupport G) x

/-- Nodal connectivity in the full network after harmonic extension. -/
abbrev midpointNodalGraph (G : WeightedGraph V) (B : SimpleGraph V) (x : V → ℝ) :=
  signedSupportGraph (positiveNetworkSupport (G.seriesNetwork B)) (seriesMidpointExtension x)

private def boundaryNode (x : V → ℝ) (v : NodalSupport x) : NodalSupport (seriesMidpointExtension x) :=
  ⟨.inl v.1, v.2⟩

omit [DecidableEq V] in
private theorem midpoint_has_signed_endpoint (x : V → ℝ) (p : SeriesInterior V)
    (h : seriesMidpointExtension x (.inr p) ≠ 0) :
    ∃ v : V, (v = p.1.1 ∨ v = p.1.2) ∧ 0 < seriesMidpointExtension x (.inr p) * x v := by
  let m := seriesMidpointExtension x (.inr p)
  have hp : 0 < m * m := mul_self_pos.mpr h
  have hsum : m * x p.1.1 + m * x p.1.2 = 2 * (m * m) := by
    rw [← mul_add]
    have hm : x p.1.1 + x p.1.2 = 2 * m := by dsimp only [m, seriesMidpointExtension]; ring
    rw [hm]
    ring
  by_cases h₁ : 0 < m * x p.1.1
  · exact ⟨p.1.1, Or.inl rfl, h₁⟩
  · exact ⟨p.1.2, Or.inr rfl, by linarith only [hsum, hp, le_of_not_gt h₁]⟩

private def signedEndpoint (x : V → ℝ) (p : SeriesInterior V)
    (h : seriesMidpointExtension x (.inr p) ≠ 0) : NodalSupport x :=
  ⟨(midpoint_has_signed_endpoint x p h).choose, fun he => by
    have hp := (midpoint_has_signed_endpoint x p h).choose_spec.2
    rw [he, mul_zero] at hp
    exact (lt_irrefl 0) hp⟩

omit [DecidableEq V] in
private theorem signedEndpoint_mem (x : V → ℝ) (p : SeriesInterior V)
    (h : seriesMidpointExtension x (.inr p) ≠ 0) :
    (signedEndpoint x p h).1 = p.1.1 ∨ (signedEndpoint x p h).1 = p.1.2 :=
  (midpoint_has_signed_endpoint x p h).choose_spec.1

omit [DecidableEq V] in
private theorem signedEndpoint_product_pos (x : V → ℝ) (p : SeriesInterior V)
    (h : seriesMidpointExtension x (.inr p) ≠ 0) :
    0 < seriesMidpointExtension x (.inr p) * x (signedEndpoint x p h).1 :=
  (midpoint_has_signed_endpoint x p h).choose_spec.2

private def projectNode (G : WeightedGraph V) (x : V → ℝ) :
    NodalSupport (seriesMidpointExtension x) → NodalSupport x ⊕ InactiveNodalMidpoint G x
  | ⟨.inl v, h⟩ => .inl ⟨v, h⟩
  | ⟨.inr p, h⟩ => if hp : 0 < G.w p.1.1 p.1.2 then .inl (signedEndpoint x p h)
      else .inr ⟨p, le_antisymm (le_of_not_gt hp) (G.w_nonneg ..), h⟩

private def embedInactive (G : WeightedGraph V) (x : V → ℝ) (p : InactiveNodalMidpoint G x) :
    NodalSupport (seriesMidpointExtension x) :=
  ⟨.inr p.1, p.2.2⟩

omit [DecidableEq V] in
private theorem projectNode_active (G : WeightedGraph V) (x : V → ℝ) (p : SeriesInterior V)
    (h : seriesMidpointExtension x (.inr p) ≠ 0) (hp : 0 < G.w p.1.1 p.1.2) :
    projectNode G x ⟨.inr p, h⟩ = .inl (signedEndpoint x p h) := by
  simp only [projectNode, dif_pos hp]

omit [DecidableEq V] in
private theorem projectNode_inactive (G : WeightedGraph V) (x : V → ℝ) (p : InactiveNodalMidpoint G x) :
    projectNode G x (embedInactive G x p) = .inr p := by
  have hp : ¬0 < G.w p.1.1.1 p.1.1.2 := by rw [p.2.1]; exact lt_irrefl 0
  simp only [embedInactive, projectNode, dif_neg hp]

private def embedNode (G : WeightedGraph V) (x : V → ℝ) :
    NodalSupport x ⊕ InactiveNodalMidpoint G x → NodalSupport (seriesMidpointExtension x)
  | .inl v => boundaryNode x v
  | .inr p => embedInactive G x p

private theorem reachable_embed_project (G : WeightedGraph V) (B : SimpleGraph V) (x : V → ℝ)
    (z : NodalSupport (seriesMidpointExtension x)) :
    (midpointNodalGraph G B x).Reachable z (embedNode G x (projectNode G x z)) := by
  rcases z with ⟨v, hv⟩
  cases v with
  | inl v => exact SimpleGraph.Reachable.rfl
  | inr p =>
    by_cases hp : 0 < G.w p.1.1 p.1.2
    · rw [projectNode_active G x p hv hp]
      apply SimpleGraph.Adj.reachable
      change 0 < (G.seriesNetwork B).w (.inr p) (.inl (signedEndpoint x p hv).1) ∧
        0 < seriesMidpointExtension x (.inr p) * x (signedEndpoint x p hv).1
      rw [(G.seriesNetwork B).w_symm (.inr p) (.inl (signedEndpoint x p hv).1)]
      exact ⟨(seriesNetwork_wire_weight_pos_iff G B _ p).mpr ⟨signedEndpoint_mem x p hv, hp⟩,
        signedEndpoint_product_pos x p hv⟩
    · let q : InactiveNodalMidpoint G x := ⟨p, le_antisymm (le_of_not_gt hp) (G.w_nonneg ..), hv⟩
      change (midpointNodalGraph G B x).Reachable (embedInactive G x q)
        (embedNode G x (projectNode G x (embedInactive G x q)))
      rw [projectNode_inactive]
      exact SimpleGraph.Reachable.rfl

private def projectedComponent (G : WeightedGraph V) (x : V → ℝ)
    (z : NodalSupport (seriesMidpointExtension x)) :
    (effectiveNodalGraph G x).ConnectedComponent ⊕ InactiveNodalMidpoint G x :=
  match projectNode G x z with
  | .inl v => .inl ((effectiveNodalGraph G x).connectedComponentMk v)
  | .inr p => .inr p

omit [DecidableEq V] in
private theorem endpoint_weight_pos (G : WeightedGraph V) (p : SeriesInterior V) {u v : V}
    (hu : u = p.1.1 ∨ u = p.1.2) (hv : v = p.1.1 ∨ v = p.1.2) (hne : u ≠ v)
    (hp : 0 < G.w p.1.1 p.1.2) : 0 < G.w u v := by
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
  · exact (hne rfl).elim
  · exact hp
  · rw [G.w_symm]
    exact hp
  · exact (hne rfl).elim

private theorem projectedComponent_eq_of_wire_adj (G : WeightedGraph V) (B : SimpleGraph V)
    (x : V → ℝ) (v : NodalSupport x) (p : SeriesInterior V)
    (h : seriesMidpointExtension x (.inr p) ≠ 0)
    (he : (midpointNodalGraph G B x).Adj (boundaryNode x v) ⟨.inr p, h⟩) :
    projectedComponent G x (boundaryNode x v) = projectedComponent G x ⟨.inr p, h⟩ := by
  have hw : 0 < (G.seriesNetwork B).w (.inl v.1) (.inr p) := he.1
  obtain ⟨hv, hp⟩ := (seriesNetwork_wire_weight_pos_iff G B v.1 p).mp hw
  let u := signedEndpoint x p h
  have hproj : projectNode G x ⟨.inr p, h⟩ = .inl u := projectNode_active G x p h hp
  change Sum.inl ((effectiveNodalGraph G x).connectedComponentMk v) = _
  rw [projectedComponent, hproj]
  apply congrArg Sum.inl
  apply SimpleGraph.ConnectedComponent.sound
  by_cases hn : v.1 = u.1
  · have e : v = u := Subtype.ext hn
    rw [e]
  · apply SimpleGraph.Adj.reachable
    have hvp : 0 < x v.1 * seriesMidpointExtension x (.inr p) := he.2
    exact ⟨endpoint_weight_pos G p hv (signedEndpoint_mem x p h) hn hp,
      sameSign_trans hvp (signedEndpoint_product_pos x p h)⟩

private theorem projectedComponent_eq_of_adj (G : WeightedGraph V) (B : SimpleGraph V) (x : V → ℝ)
    {z w : NodalSupport (seriesMidpointExtension x)} (h : (midpointNodalGraph G B x).Adj z w) :
    projectedComponent G x z = projectedComponent G x w := by
  rcases z with ⟨z, hz⟩
  rcases w with ⟨w, hw⟩
  cases z with
  | inl u =>
    cases w with
    | inl v =>
      have hw' : 0 < (G.retainedBoundary B).w u v := h.1
      have hres : 0 ≤ G.w u v - (G.retainedBoundary B).w u v :=
        (G.residualBoundary B).w_nonneg u v
      have he : (effectiveNodalGraph G x).Adj ⟨u, hz⟩ ⟨v, hw⟩ :=
        ⟨hw'.trans_le (sub_nonneg.mp hres), h.2⟩
      exact congrArg Sum.inl (SimpleGraph.ConnectedComponent.sound he.reachable)
    | inr p =>
      exact projectedComponent_eq_of_wire_adj G B x ⟨u, hz⟩ p hw h
  | inr p =>
    cases w with
    | inl v =>
      exact (projectedComponent_eq_of_wire_adj G B x ⟨v, hw⟩ p hz h.symm).symm
    | inr q =>
      have hb : (0 : ℝ) < 0 := h.1
      exact ((lt_irrefl 0) hb).elim

private theorem lift_boundary_adj (G : WeightedGraph V) (B : SimpleGraph V) (x : V → ℝ)
    {u v : NodalSupport x} (h : (effectiveNodalGraph G x).Adj u v) :
    (midpointNodalGraph G B x).Reachable (boundaryNode x u) (boundaryNode x v) := by
  have hweight : 0 < G.w u.1 v.1 := h.1
  have hn : u.1 ≠ v.1 := fun h' => by rw [h', G.w_diag] at hweight; exact (lt_irrefl 0) hweight
  let p : SeriesInterior V := ⟨(u.1, v.1), hn⟩
  have hsign : 0 < x u.1 * x v.1 := h.2
  obtain ⟨hleft, hright⟩ := sameSign_with_midpoint hsign
  have hnz : seriesMidpointExtension x (.inr p) ≠ 0 := by
    intro h'
    change (x u.1 + x v.1) / 2 = 0 at h'
    rw [h', mul_zero] at hleft
    exact (lt_irrefl 0) hleft
  let m : NodalSupport (seriesMidpointExtension x) := ⟨.inr p, hnz⟩
  have hl : (midpointNodalGraph G B x).Adj (boundaryNode x u) m := by
    refine ⟨(seriesNetwork_wire_weight_pos_iff G B u.1 p).mpr ⟨Or.inl rfl, hweight⟩, hleft⟩
  have hr : (midpointNodalGraph G B x).Adj (boundaryNode x v) m := by
    refine ⟨(seriesNetwork_wire_weight_pos_iff G B v.1 p).mpr ⟨Or.inr rfl, hweight⟩, ?_⟩
    change 0 < x v.1 * ((x u.1 + x v.1) / 2)
    rw [mul_comm]
    exact hright
  exact hl.reachable.trans hr.reachable.symm

/-- Harmonic midpoint extension preserves every effective nodal component.
The other components are precisely the nonzero midpoints of zero conductance. -/
def midpointNodalComponentsEquiv (G : WeightedGraph V) (B : SimpleGraph V) (x : V → ℝ) :
    (midpointNodalGraph G B x).ConnectedComponent ≃
      (effectiveNodalGraph G x).ConnectedComponent ⊕ InactiveNodalMidpoint G x := by
  let P := midpointNodalGraph G B x
  let E := effectiveNodalGraph G x
  let liftBoundary : E.ConnectedComponent → P.ConnectedComponent :=
    SimpleGraph.ConnectedComponent.lift (fun v => P.connectedComponentMk (boundaryNode x v))
      (fun _ _ p _ => walk_values_eq _ (fun h => SimpleGraph.ConnectedComponent.sound (lift_boundary_adj G B x h)) p)
  let forward : P.ConnectedComponent → E.ConnectedComponent ⊕ InactiveNodalMidpoint G x :=
    SimpleGraph.ConnectedComponent.lift (projectedComponent G x)
      (fun _ _ p _ => walk_values_eq _ (projectedComponent_eq_of_adj G B x) p)
  let backward : E.ConnectedComponent ⊕ InactiveNodalMidpoint G x → P.ConnectedComponent :=
    Sum.elim liftBoundary (fun p => P.connectedComponentMk (embedInactive G x p))
  refine ⟨forward, backward, ?_, ?_⟩
  · intro c
    induction c using SimpleGraph.ConnectedComponent.ind with
    | _ z =>
      change backward (projectedComponent G x z) = P.connectedComponentMk z
      have hz := reachable_embed_project G B x z
      cases h : projectNode G x z with
      | inl v =>
        have he : projectedComponent G x z = .inl (E.connectedComponentMk v) := by
          simp only [projectedComponent, h, E]
        rw [he]
        rw [h] at hz
        exact (SimpleGraph.ConnectedComponent.sound hz).symm
      | inr p =>
        have he : projectedComponent G x z = .inr p := by simp only [projectedComponent, h]
        rw [he]
        rw [h] at hz
        exact (SimpleGraph.ConnectedComponent.sound hz).symm
  · intro c
    cases c with
    | inl c =>
      induction c using SimpleGraph.ConnectedComponent.ind with
      | _ v => rfl
    | inr p =>
      change projectedComponent G x (embedInactive G x p) = .inr p
      simp only [projectedComponent, projectNode_inactive]

/-- The finite nodal-domain count splits into effective components and
isolated inactive midpoints. -/
theorem card_midpointNodalComponents [Finite V] (G : WeightedGraph V) (B : SimpleGraph V) (x : V → ℝ) :
    Nat.card (midpointNodalGraph G B x).ConnectedComponent =
      Nat.card (effectiveNodalGraph G x).ConnectedComponent + Nat.card (InactiveNodalMidpoint G x) :=
  (Nat.card_congr (midpointNodalComponentsEquiv G B x)).trans Nat.card_sum

end Series

/-- Nodal connectivity using only the retained direct boundary edges. -/
abbrev directBoundaryNodalGraph (G : WeightedGraph V) (B : SimpleGraph V) (x : V → ℝ) :=
  signedSupportGraph (positiveNetworkSupport (G.retainedBoundary B)) x

/-- An effective nodal domain collects the direct boundary domains that
are joined by the interior paths. -/
def directNodalComponentToEffective (G : WeightedGraph V) (B : SimpleGraph V) (x : V → ℝ) :
    (directBoundaryNodalGraph G B x).ConnectedComponent → (effectiveNodalGraph G x).ConnectedComponent :=
  SimpleGraph.ConnectedComponent.lift (effectiveNodalGraph G x).connectedComponentMk fun _ _ w _ =>
    walk_values_eq _ (fun {u v} h => by
      have hw : 0 < (G.retainedBoundary B).w u.1 v.1 := h.1
      have hr : 0 ≤ G.w u.1 v.1 - (G.retainedBoundary B).w u.1 v.1 :=
        (G.residualBoundary B).w_nonneg u.1 v.1
      have he : (effectiveNodalGraph G x).Adj u v := ⟨hw.trans_le (sub_nonneg.mp hr), h.2⟩
      exact SimpleGraph.ConnectedComponent.sound he.reachable) w

theorem directNodalComponentToEffective_surjective (G : WeightedGraph V) (B : SimpleGraph V)
    (x : V → ℝ) : Function.Surjective (directNodalComponentToEffective G B x) := by
  intro c
  induction c using SimpleGraph.ConnectedComponent.ind with
  | _ v => exact ⟨(directBoundaryNodalGraph G B x).connectedComponentMk v, rfl⟩

/-- With positive conductance between every distinct pair, a boundary
function of both signs has exactly two effective strong nodal domains. -/
def effectiveNodalComponentsEquivBool (G : WeightedGraph V) (x : V → ℝ)
    (hfull : ∀ u v : V, u ≠ v → 0 < G.w u v) (p m : NodalSupport x)
    (hp : 0 < x p.1) (hm : x m.1 < 0) : Bool ≃ (effectiveNodalGraph G x).ConnectedComponent := by
  let E := effectiveNodalGraph G x
  let f : Bool → E.ConnectedComponent := fun b => if b then E.connectedComponentMk m else E.connectedComponentMk p
  have hsign {u v : NodalSupport x} (h : E.Adj u v) :
      (0 < x u.1) = (0 < x v.1) := by
    rcases mul_pos_iff.mp h.2 with h' | h'
    · exact propext ⟨fun _ => h'.2, fun _ => h'.1⟩
    · exact propext ⟨fun hh => (not_lt_of_gt hh h'.1).elim, fun hh => (not_lt_of_gt hh h'.2).elim⟩
  have hdistinct : E.connectedComponentMk p ≠ E.connectedComponentMk m := by
    intro h
    obtain ⟨w⟩ := SimpleGraph.ConnectedComponent.exact h
    have he := walk_values_eq (fun v : NodalSupport x => 0 < x v.1) (fun h => hsign h) w
    exact not_lt_of_gt (Eq.mp he hp) hm
  have hreach (u v : NodalSupport x) (h : 0 < x u.1 * x v.1) : E.Reachable u v := by
    by_cases hu : u = v
    · subst v
      exact SimpleGraph.Reachable.rfl
    · have hne : u.1 ≠ v.1 := fun e => hu (Subtype.ext e)
      exact (show E.Adj u v from ⟨hfull u.1 v.1 hne, h⟩).reachable
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro a b h
    cases a <;> cases b
    · rfl
    · exact (hdistinct h).elim
    · exact (hdistinct h.symm).elim
    · rfl
  · intro c
    induction c using SimpleGraph.ConnectedComponent.ind with
    | _ v =>
      by_cases hv : 0 < x v.1
      · exact ⟨false, SimpleGraph.ConnectedComponent.sound (hreach p v (mul_pos hp hv))⟩
      · have hv' : x v.1 < 0 := lt_of_le_of_ne (le_of_not_gt hv) v.2
        exact ⟨true, SimpleGraph.ConnectedComponent.sound (hreach m v (mul_pos_of_neg_of_neg hm hv'))⟩

/-- Midpoint extension has two strong nodal domains when the effective
network is complete with positive weights and the data have both signs. -/
theorem card_midpointNodalComponents_of_full [DecidableEq V] (G : WeightedGraph V)
    (B : SimpleGraph V) (x : V → ℝ) (hfull : ∀ u v : V, u ≠ v → 0 < G.w u v)
    (p m : NodalSupport x) (hp : 0 < x p.1) (hm : x m.1 < 0) :
    Nat.card (midpointNodalGraph G B x).ConnectedComponent = 2 := by
  letI : IsEmpty (InactiveNodalMidpoint G x) :=
    ⟨fun q => (hfull q.1.1.1 q.1.1.2 q.1.2).ne' q.2.1⟩
  let e := (midpointNodalComponentsEquiv G B x).trans
    ((Equiv.sumEmpty _ _).trans (effectiveNodalComponentsEquivBool G x hfull p m hp hm).symm)
  exact (Nat.card_congr e).trans (by rw [Nat.card_eq_fintype_card, Fintype.card_bool])

/-- Each low response mode has two domains in the full physical network. -/
theorem card_colorMode_interiorNodalDomains (K N : ℕ) (i : Fin (N + 1)) :
    Nat.card (midpointNodalGraph (layeredBoundaryGraph K N) (layerBoundaryGraph K N)
      (colorMode i)).ConnectedComponent = 2 := by
  let x : LayeredBoundary K N → ℝ := colorMode i
  let v : LayeredBoundary K N := (i, (false, 0))
  let u : LayeredBoundary K N := (i, (true, 0))
  have hv : 0 < x v := by
    change 0 < colorMode i ((i, (false, 0)) : LayeredBoundary K N)
    rw [colorMode, if_pos rfl]
    exact one_pos
  have hu : x u < 0 := by
    change colorMode i ((i, (true, 0)) : LayeredBoundary K N) < 0
    rw [colorMode, if_pos rfl]
    exact neg_lt_zero.mpr one_pos
  exact card_midpointNodalComponents_of_full (layeredBoundaryGraph K N) (layerBoundaryGraph K N) x
    (fun _ _ h => layeredBoundaryGraph_weight_pos h) ⟨v, hv.ne'⟩ ⟨u, hu.ne⟩ hv hu

/-- The full network has two nodal domains and the direct boundary has
`2(K+1)`, for each of the first `N+1` response modes. -/
theorem colorMode_full_and_boundary_nodal_counts (K N : ℕ) (i : Fin (N + 1)) :
    Nat.card (midpointNodalGraph (layeredBoundaryGraph K N) (layerBoundaryGraph K N)
      (colorMode i)).ConnectedComponent = 2 ∧
    Nat.card (colorNodalGraph K i).ConnectedComponent = 2 * (K + 1) :=
  ⟨card_colorMode_interiorNodalDomains K N i, card_colorNodalDomains K i⟩

#print axioms midpointNodalComponentsEquiv
#print axioms card_midpointNodalComponents
#print axioms directNodalComponentToEffective_surjective
#print axioms card_midpointNodalComponents_of_full
#print axioms colorMode_full_and_boundary_nodal_counts

end

end GaloisForLFunctions.HTGeometry.BoundaryResponse
