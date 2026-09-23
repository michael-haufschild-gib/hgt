import Mathlib

/-!
# Connected parity contexts, proper-face blindness, and the positive-state law

Each vertex of a finite connected simple graph is a classical observer context; each edge is a
binary observable shared by its two endpoint contexts.  A parity charge `b : V → ZMod 2` prescribes
at every context the required sum of its incident edge values, and a *global classical law* is a
single edge assignment `x` realizing every context equation simultaneously, i.e. a solution of

`∂_G x = b`

for the unsigned incidence (boundary) map `∂_G : (edges → ZMod 2) → (V → ZMod 2)`.

This file certifies the three theorems of the universal-law-field card
`connected-parity-context-proper-face-blindness-and-positive-state-law`:

* `range_parityBoundary` — for connected `G` the image of `∂_G` is *exactly* the even-charge
  hyperplane, so a global classical law exists iff the total parity charge vanishes
  (`exists_parityBoundary_eq_iff`); the obstruction group `coker ∂_G` is canonically one
  dimensional (`finrank_parityCoker`), the obstruction being the total charge;
* `exists_parityBoundary_eq_on_of_ne_univ` — under an odd total charge no global law exists, yet
  *every proper* set of contexts is jointly satisfiable: the obstruction is invisible on each
  proper observer face (`properFace_blindness`);
* `localLaw_marginal_prob` / `positive_state_no_global_law` — the uniform distributions on the local
  context solution sets have uniform (hence pairwise compatible) edge marginals, so a compatible
  positive empirical state exists on the whole cover while no deterministic global law does.

Everything is unconditional: no hypothesis beyond finiteness, connectedness, and (for the positive
state) minimum degree two.
-/

namespace GaloisForLFunctions.HTGeometry

open SimpleGraph Finset

/-- The two-element scalar dichotomy. -/
theorem zmodTwo_eq_zero_or_one_constitutiveParityContextuality (a : ZMod 2) : a = 0 ∨ a = 1 := by
  have hv : a.val < 2 := ZMod.val_lt a
  have hcast : ((a.val : ℕ) : ZMod 2) = a := ZMod.natCast_rightInverse a
  interval_cases h : a.val
  · left; rw [← hcast]; simp
  · right; rw [← hcast]; simp

/-- A nonzero two-element scalar is the unit. -/
theorem zmodTwo_eq_one_of_ne_zero {a : ZMod 2} (ha : a ≠ 0) : a = 1 :=
  (zmodTwo_eq_zero_or_one_constitutiveParityContextuality a).resolve_left ha

section Boundary

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **The unsigned incidence (parity boundary) map.**  `(∂_G x) v` is the sum of the values of `x`
on the edges incident to `v`, computed in `ZMod 2`. -/
noncomputable def parityBoundary : (G.edgeSet → ZMod 2) →ₗ[ZMod 2] (V → ZMod 2) where
  toFun x := fun v => ∑ e : G.edgeSet, if v ∈ (e : Sym2 V) then x e else 0
  map_add' x y := by
    funext v
    simp only [Pi.add_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    by_cases h : v ∈ (e : Sym2 V) <;> simp [h]
  map_smul' c x := by
    funext v
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    by_cases h : v ∈ (e : Sym2 V) <;> simp [h]

theorem parityBoundary_apply (x : G.edgeSet → ZMod 2) (v : V) :
    parityBoundary G x v = ∑ e : G.edgeSet, if v ∈ (e : Sym2 V) then x e else 0 := rfl

/-- **The context equation is the local incidence sum.**  The boundary value at `v` is the sum of
`x` over the edges incident to `v`. -/
theorem parityBoundary_apply_incidence (x : G.edgeSet → ZMod 2) (v : V) :
    parityBoundary G x v = ∑ e : {e : G.edgeSet // v ∈ (e : Sym2 V)}, x e := by
  rw [parityBoundary_apply, ← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) _

/-- The boundary of a single-edge assignment is the indicator of that edge's endpoint pair. -/
theorem parityBoundary_single (e₀ : G.edgeSet) (c : ZMod 2) (v : V) :
    parityBoundary G (Pi.single e₀ c) v = if v ∈ (e₀ : Sym2 V) then c else 0 := by
  rw [parityBoundary_apply]
  rw [Finset.sum_eq_single e₀]
  · simp
  · intro e _ hne
    rw [Pi.single_eq_of_ne hne]
    simp
  · intro h
    exact absurd (Finset.mem_univ e₀) h

/-- Cancellation of a repeated middle term in characteristic two. -/
theorem charTwo_mid_cancel (A B C : ZMod 2) : A + B + (B + C) = A + C := by
  have h : A + B + (B + C) = A + C + (B + B) := by ring
  rw [h, CharTwo.add_self_eq_zero, add_zero]

omit [Fintype V] in
/-- The endpoint indicator of an edge splits as the sum of the two vertex indicators. -/
theorem edge_indicator_eq_single_add_single {a b : V} (hab : a ≠ b) (v : V) :
    (if v ∈ (s(a, b) : Sym2 V) then (1 : ZMod 2) else 0)
      = (Pi.single a 1 + Pi.single b 1 : V → ZMod 2) v := by
  simp only [Pi.add_apply]
  by_cases hva : v = a
  · subst hva
    rw [if_pos (by simp), Pi.single_eq_same, Pi.single_eq_of_ne hab, add_zero]
  · by_cases hvb : v = b
    · subst hvb
      rw [if_pos (by simp), Pi.single_eq_same, Pi.single_eq_of_ne hva, zero_add]
    · rw [if_neg (by simp [Sym2.mem_iff, hva, hvb]), Pi.single_eq_of_ne hva,
        Pi.single_eq_of_ne hvb, add_zero]

/-- The boundary of a single edge is the sum of its two endpoint indicators. -/
theorem parityBoundary_single_endpoints {a b : V} (h : G.Adj a b) :
    parityBoundary G (Pi.single (⟨s(a, b), (G.mem_edgeSet).mpr h⟩ : G.edgeSet) 1)
      = (Pi.single a 1 + Pi.single b 1 : V → ZMod 2) := by
  funext v
  rw [parityBoundary_single]
  exact edge_indicator_eq_single_add_single (G.ne_of_adj h) v

/-- **Every edge column has even weight.**  The total parity charge of any boundary vanishes: the
image of `∂_G` lies in the even-charge hyperplane. -/
theorem sum_parityBoundary_eq_zero (x : G.edgeSet → ZMod 2) :
    ∑ v : V, parityBoundary G x v = 0 := by
  simp only [parityBoundary_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun e _ => ?_
  obtain ⟨e, he⟩ := e
  induction e using Sym2.ind with
  | _ a b =>
    have hab : a ≠ b := G.ne_of_adj ((G.mem_edgeSet).mp he)
    rw [← Finset.sum_filter]
    have hfilter : (Finset.univ.filter (fun v : V => v ∈ (s(a, b) : Sym2 V))) = {a, b} := by
      ext v; simp [Sym2.mem_iff]
    rw [hfilter, Finset.sum_pair hab]
    exact CharTwo.add_self_eq_zero _

end Boundary

section Walks

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The mod-two edge multiplicity of a walk, viewed as an edge assignment. -/
noncomputable def walkParity {u v : V} (p : G.Walk u v) : G.edgeSet → ZMod 2 :=
  fun e => (p.edges.count (e : Sym2 V) : ZMod 2)

omit [Fintype V] [DecidableRel G.Adj] in
theorem walkParity_nil (u : V) : walkParity G (SimpleGraph.Walk.nil : G.Walk u u) = 0 := by
  funext e
  simp [walkParity]

omit [Fintype V] [DecidableRel G.Adj] in
theorem walkParity_cons {u w v : V} (h : G.Adj u w) (p : G.Walk w v) :
    walkParity G (SimpleGraph.Walk.cons h p)
      = Pi.single (⟨s(u, w), (G.mem_edgeSet).mpr h⟩ : G.edgeSet) 1 + walkParity G p := by
  funext e
  simp only [walkParity, SimpleGraph.Walk.edges_cons, List.count_cons, Pi.add_apply,
    Nat.cast_add, Pi.single_apply]
  have : ((if (s(u, w) == (e : Sym2 V)) = true then 1 else 0 : ℕ) : ZMod 2)
      = if e = (⟨s(u, w), (G.mem_edgeSet).mpr h⟩ : G.edgeSet) then (1 : ZMod 2) else 0 := by
    by_cases hE : (e : Sym2 V) = s(u, w)
    · rw [if_pos (by simp [hE]), if_pos (Subtype.ext hE)]
      simp
    · rw [if_neg (by simp only [beq_iff_eq]; exact fun hc => hE hc.symm),
        if_neg (fun hc => hE (by rw [hc]))]
      simp
  rw [this]
  ring

/-- **Walks realize endpoint charges.**  The boundary of the mod-two edge multiplicity of any walk
is the sum of the two endpoint indicators. -/
theorem parityBoundary_walkParity {u v : V} (p : G.Walk u v) :
    parityBoundary G (walkParity G p) = Pi.single u 1 + Pi.single v 1 := by
  induction p with
  | nil =>
    rw [walkParity_nil, map_zero]
    funext z
    exact (CharTwo.add_self_eq_zero _).symm
  | cons h p ih =>
    rw [walkParity_cons, map_add, ih, parityBoundary_single_endpoints G h]
    funext z
    simp only [Pi.add_apply]
    exact charTwo_mid_cancel _ _ _

end Walks


section Surjectivity

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The total parity charge of a context assignment. -/
def totalCharge (V : Type*) [Fintype V] : (V → ZMod 2) →ₗ[ZMod 2] ZMod 2 where
  toFun b := ∑ v, b v
  map_add' b c := by simp [Finset.sum_add_distrib]
  map_smul' r b := by simp [Finset.mul_sum]

omit [DecidableEq V] in
theorem totalCharge_apply (b : V → ZMod 2) : totalCharge V b = ∑ v, b v := rfl

/-- Cancellation of a repeated summand in characteristic two. -/
theorem charTwo_add_cancel (A B : ZMod 2) : A + B + B = A := by
  rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]

private theorem exists_parityBoundary_aux (hG : G.Connected) :
    ∀ n : ℕ, ∀ b : V → ZMod 2,
      (Finset.univ.filter (fun v => b v ≠ 0)).card = n → (∑ v, b v) = 0 →
      ∃ x, parityBoundary G x = b := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro b hcard hsum
    rcases Nat.lt_or_ge n 2 with hn | hn
    · interval_cases n
      · refine ⟨0, ?_⟩
        have hempty : (Finset.univ.filter (fun v => b v ≠ 0)) = ∅ := Finset.card_eq_zero.mp hcard
        funext z
        have hz : z ∉ (Finset.univ.filter (fun v => b v ≠ 0)) := by
          rw [hempty]; simp
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hz
        rw [map_zero]
        simp [hz]
      · exfalso
        obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hcard
        have hsum' : ∑ v ∈ Finset.univ.filter (fun v => b v ≠ 0), b v = ∑ v : V, b v :=
          Finset.sum_filter_ne_zero Finset.univ
        rw [hu, Finset.sum_singleton, hsum] at hsum'
        have humem : u ∈ Finset.univ.filter (fun v => b v ≠ 0) := by rw [hu]; exact Finset.mem_singleton_self u
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at humem
        exact humem hsum'
    · obtain ⟨u, hu, v, hv, huv⟩ :=
        Finset.one_lt_card.mp (by omega : 1 < (Finset.univ.filter (fun v => b v ≠ 0)).card)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu hv
      have hbu : b u = 1 := zmodTwo_eq_one_of_ne_zero hu
      have hbv : b v = 1 := zmodTwo_eq_one_of_ne_zero hv
      set S : V → ZMod 2 := Pi.single u 1 + Pi.single v 1 with hS
      have hSapp : ∀ z, S z = (if z = u then (1 : ZMod 2) else 0) + (if z = v then 1 else 0) := by
        intro z; simp [hS, Pi.single_apply]
      set b' : V → ZMod 2 := b + S with hb'
      have hb'eq : ∀ z, b' z = if z = u then 0 else if z = v then 0 else b z := by
        intro z
        simp only [hb', Pi.add_apply, hSapp]
        by_cases hzu : z = u
        · subst hzu
          rw [if_pos rfl, if_pos rfl, if_neg huv, hbu, add_zero]
          exact CharTwo.add_self_eq_zero 1
        · by_cases hzv : z = v
          · subst hzv
            rw [if_neg hzu, if_neg hzu, if_pos rfl, if_pos rfl, hbv, zero_add]
            exact CharTwo.add_self_eq_zero 1
          · rw [if_neg hzu, if_neg hzu, if_neg hzv, if_neg hzv, add_zero, add_zero]
      have hsupp : Finset.univ.filter (fun z => b' z ≠ 0)
          = ((Finset.univ.filter (fun z => b z ≠ 0)).erase u).erase v := by
        ext z
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, hb'eq]
        by_cases hzu : z = u
        · subst hzu; simp [huv]
        · by_cases hzv : z = v
          · subst hzv; simp [hzu]
          · simp [hzu, hzv]
      have hvmem : v ∈ (Finset.univ.filter (fun z => b z ≠ 0)).erase u := by
        rw [Finset.mem_erase]
        exact ⟨Ne.symm huv, by simp [hv]⟩
      have humem : u ∈ Finset.univ.filter (fun z => b z ≠ 0) := by simp [hu]
      have hcard' : (Finset.univ.filter (fun z => b' z ≠ 0)).card = n - 2 := by
        rw [hsupp, Finset.card_erase_of_mem hvmem, Finset.card_erase_of_mem humem, hcard]
        omega
      have hsumS : ∑ z : V, S z = 0 := by
        simp only [hSapp, Finset.sum_add_distrib]
        rw [Finset.sum_ite_eq' Finset.univ u (fun _ => (1 : ZMod 2)),
          Finset.sum_ite_eq' Finset.univ v (fun _ => (1 : ZMod 2))]
        simp
        exact CharTwo.add_self_eq_zero 1
      have hsum' : ∑ z : V, b' z = 0 := by
        simp only [hb', Pi.add_apply, Finset.sum_add_distrib, hsum, hsumS, add_zero]
      obtain ⟨x', hx'⟩ := ih (n - 2) (by omega) b' hcard' hsum'
      refine ⟨x' + walkParity G ((hG.preconnected u v).some), ?_⟩
      rw [map_add, hx', parityBoundary_walkParity]
      funext z
      simp only [hb', Pi.add_apply, hS]
      exact charTwo_add_cancel _ _

/-- **Exact contextuality criterion, existence half.**  On a connected graph every even total parity
charge is realized by a global classical law. -/
theorem exists_parityBoundary_eq_of_sum_eq_zero (hG : G.Connected) {b : V → ZMod 2}
    (hb : ∑ v, b v = 0) : ∃ x, parityBoundary G x = b :=
  exists_parityBoundary_aux G hG _ b rfl hb

/-- **Exact contextuality criterion.**  A global classical law exists if and only if the total
parity charge vanishes. -/
theorem exists_parityBoundary_eq_iff (hG : G.Connected) (b : V → ZMod 2) :
    (∃ x, parityBoundary G x = b) ↔ ∑ v, b v = 0 := by
  constructor
  · rintro ⟨x, rfl⟩
    exact sum_parityBoundary_eq_zero G x
  · exact exists_parityBoundary_eq_of_sum_eq_zero G hG

/-- **The image of the parity boundary is the even-charge hyperplane.** -/
theorem range_parityBoundary (hG : G.Connected) :
    LinearMap.range (parityBoundary G) = LinearMap.ker (totalCharge V) := by
  ext b
  simp only [LinearMap.mem_range, LinearMap.mem_ker, totalCharge_apply]
  exact exists_parityBoundary_eq_iff G hG b

theorem totalCharge_surjective [Nonempty V] : Function.Surjective (totalCharge V) := by
  intro c
  refine ⟨Pi.single (Classical.arbitrary V) c, ?_⟩
  rw [totalCharge_apply]
  simp only [Pi.single_apply]
  rw [Finset.sum_ite_eq' Finset.univ (Classical.arbitrary V) (fun _ => c)]
  simp

/-- **The obstruction group is canonically the two-element group**, the obstruction being the total
parity charge. -/
noncomputable def parityCokerEquiv [Nonempty V] (hG : G.Connected) :
    ((V → ZMod 2) ⧸ LinearMap.range (parityBoundary G)) ≃ₗ[ZMod 2] ZMod 2 :=
  (Submodule.quotEquivOfEq _ _ (range_parityBoundary G hG)).trans
    (LinearMap.quotKerEquivOfSurjective (totalCharge V) totalCharge_surjective)

/-- **The obstruction group is one dimensional.** -/
theorem finrank_parityCoker [Nonempty V] (hG : G.Connected) :
    Module.finrank (ZMod 2) ((V → ZMod 2) ⧸ LinearMap.range (parityBoundary G)) = 1 := by
  rw [(parityCokerEquiv G hG).finrank_eq, Module.finrank_self]

/-- **The parity boundary has rank `|V| − 1`.** -/
theorem finrank_range_parityBoundary [Nonempty V] (hG : G.Connected) :
    Module.finrank (ZMod 2) (LinearMap.range (parityBoundary G)) = Fintype.card V - 1 := by
  have hq := Submodule.finrank_quotient_add_finrank (LinearMap.range (parityBoundary G))
  rw [finrank_parityCoker G hG, Module.finrank_pi] at hq
  omega

end Surjectivity

section ProperFace

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

omit [DecidableRel G.Adj] in
theorem sum_pi_single_eq (v₀ : V) (c : ZMod 2) :
    ∑ v : V, (Pi.single v₀ c : V → ZMod 2) v = c := by
  simp only [Pi.single_apply]
  rw [Finset.sum_ite_eq' Finset.univ v₀ (fun _ => c)]
  simp

/-- **Proper-face solvability.**  On a connected graph every proper set of contexts is jointly
satisfiable, for an arbitrary parity charge: the total-charge obstruction is invisible on each
proper observer face. -/
theorem exists_parityBoundary_eq_on_of_ne_univ (hG : G.Connected) (W : Finset V)
    (hW : W ≠ Finset.univ) (b : V → ZMod 2) :
    ∃ x, ∀ v ∈ W, parityBoundary G x v = b v := by
  obtain ⟨v₀, hv₀⟩ : ∃ v₀ : V, v₀ ∉ W := by
    by_contra hcon
    exact hW (Finset.eq_univ_iff_forall.mpr (fun x => not_not.mp (fun hx => hcon ⟨x, hx⟩)))
  have hsum : ∑ v, (b + Pi.single v₀ (∑ v, b v) : V → ZMod 2) v = 0 := by
    simp only [Pi.add_apply, Finset.sum_add_distrib, sum_pi_single_eq]
    exact CharTwo.add_self_eq_zero _
  obtain ⟨x, hx⟩ := exists_parityBoundary_eq_of_sum_eq_zero G hG hsum
  refine ⟨x, fun v hv => ?_⟩
  have hvv₀ : v ≠ v₀ := fun h => hv₀ (h ▸ hv)
  rw [hx]
  simp [hvv₀]

/-- **Proper-face blindness.**  Under an odd total parity charge the whole context cover admits no
global classical law, while every proper observer face does. -/
theorem properFace_blindness (hG : G.Connected) {b : V → ZMod 2} (hb : ∑ v, b v = 1) :
    (¬ ∃ x, parityBoundary G x = b) ∧
      ∀ W : Finset V, W ≠ Finset.univ → ∃ x, ∀ v ∈ W, parityBoundary G x v = b v := by
  refine ⟨?_, fun W hW => exists_parityBoundary_eq_on_of_ne_univ G hG W hW b⟩
  rw [exists_parityBoundary_eq_iff G hG b, hb]
  exact one_ne_zero

end ProperFace

section Counting

/-- **Halving by a parity-flipping involution.**  A two-valued observable on a finite type that is
flipped by an involution has both fibres of exactly half the size. -/
theorem two_mul_card_fiber_of_flip {β : Type*} [Fintype β] [DecidableEq β]
    (q : β → ZMod 2) (σ : β → β) (hσ : ∀ y, σ (σ y) = y) (hq : ∀ y, q (σ y) = q y + 1)
    (d : ZMod 2) :
    2 * (Finset.univ.filter (fun y => q y = d)).card = Fintype.card β := by
  have hflip : ∀ d' : ZMod 2, (Finset.univ.filter (fun y => q y = d')).card
      = (Finset.univ.filter (fun y => q y = d' + 1)).card := by
    intro d'
    refine Finset.card_bij' (fun y _ => σ y) (fun y _ => σ y) ?_ ?_ ?_ ?_
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      rw [hq, ha]
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      rw [hq, ha]
      exact charTwo_add_cancel d' 1
    · intro a _; exact hσ a
    · intro a _; exact hσ a
  have hpart : (Finset.univ.filter (fun y => q y = (0 : ZMod 2))).card
      + (Finset.univ.filter (fun y => q y = (1 : ZMod 2))).card = Fintype.card β := by
    have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset β))
      (fun y => q y = (0 : ZMod 2))
    have hne : (Finset.univ.filter (fun y => ¬ (q y = (0 : ZMod 2))))
        = Finset.univ.filter (fun y => q y = (1 : ZMod 2)) := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => zmodTwo_eq_one_of_ne_zero h, fun h => by rw [h]; exact one_ne_zero⟩
    rw [hne] at h
    rw [h, Finset.card_univ]
  rcases zmodTwo_eq_zero_or_one_constitutiveParityContextuality d with rfl | rfl
  · have h0 := hflip 0
    rw [zero_add] at h0
    omega
  · have h1 := hflip 1
    rw [CharTwo.add_self_eq_zero (1 : ZMod 2)] at h1
    omega

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- **Parity fibre count.**  Exactly half of all binary assignments have a prescribed parity. -/
theorem card_parityFiber (a₀ : α) (c : ZMod 2) :
    (Finset.univ.filter (fun y : α → ZMod 2 => ∑ i, y i = c)).card
      = 2 ^ (Fintype.card α - 1) := by
  have hhalf := two_mul_card_fiber_of_flip (β := α → ZMod 2) (fun y => ∑ i, y i)
      (fun y => y + Pi.single a₀ 1)
      (fun y => by funext i; exact charTwo_add_cancel _ _)
      (fun y => by
        simp only [Pi.add_apply, Finset.sum_add_distrib]
        rw [sum_pi_single_eq]) c
  have hcard : Fintype.card (α → ZMod 2) = 2 ^ Fintype.card α := by simp
  rw [hcard] at hhalf
  have hn : 1 ≤ Fintype.card α := Fintype.card_pos_iff.mpr ⟨a₀⟩
  have hpow : (2 : ℕ) ^ Fintype.card α = 2 * 2 ^ (Fintype.card α - 1) := by
    conv_lhs => rw [show Fintype.card α = (Fintype.card α - 1) + 1 by omega]
    ring
  omega

/-- **Value fibre count.**  Exactly half of all binary assignments take a prescribed value at a
prescribed coordinate. -/
theorem card_valueFiber (a₀ : α) (t : ZMod 2) :
    (Finset.univ.filter (fun y : α → ZMod 2 => y a₀ = t)).card
      = 2 ^ (Fintype.card α - 1) := by
  have hhalf := two_mul_card_fiber_of_flip (β := α → ZMod 2) (fun y => y a₀)
      (fun y => y + Pi.single a₀ 1)
      (fun y => by funext i; exact charTwo_add_cancel _ _)
      (fun y => by simp) t
  have hcard : Fintype.card (α → ZMod 2) = 2 ^ Fintype.card α := by simp
  rw [hcard] at hhalf
  have hn : 1 ≤ Fintype.card α := Fintype.card_pos_iff.mpr ⟨a₀⟩
  have hpow : (2 : ℕ) ^ Fintype.card α = 2 * 2 ^ (Fintype.card α - 1) := by
    conv_lhs => rw [show Fintype.card α = (Fintype.card α - 1) + 1 by omega]
    ring
  omega

/-- **Marginal fibre count.**  Fixing one coordinate value inside a parity fibre leaves
`2 ^ (n − 2)` assignments, independently of the fixed value and of the prescribed parity. -/
theorem card_parityFiber_fixed (a₀ a₁ : α) (ha : a₁ ≠ a₀) (c t : ZMod 2) :
    Fintype.card {y : α → ZMod 2 // y a₀ = t ∧ ∑ i, y i = c}
      = 2 ^ (Fintype.card α - 2) := by
  have hsub : Fintype.card {y : α → ZMod 2 // y a₀ = t} = 2 ^ (Fintype.card α - 1) := by
    rw [Fintype.card_subtype]
    exact card_valueFiber a₀ t
  have hhalf := two_mul_card_fiber_of_flip (β := {y : α → ZMod 2 // y a₀ = t})
      (fun z => ∑ i, (z : α → ZMod 2) i)
      (fun z => ⟨(z : α → ZMod 2) + Pi.single a₁ 1, by
        have hz : ((z : α → ZMod 2) + Pi.single a₁ 1 : α → ZMod 2) a₀ = (z : α → ZMod 2) a₀ := by
          simp [Ne.symm ha]
        rw [hz]; exact z.2⟩)
      (fun z => by
        apply Subtype.ext
        funext i
        exact charTwo_add_cancel _ _)
      (fun z => by
        simp only [Pi.add_apply, Finset.sum_add_distrib]
        rw [sum_pi_single_eq]) c
  rw [hsub] at hhalf
  have hcard : Fintype.card {y : α → ZMod 2 // y a₀ = t ∧ ∑ i, y i = c}
      = (Finset.univ.filter (fun z : {y : α → ZMod 2 // y a₀ = t} =>
          ∑ i, (z : α → ZMod 2) i = c)).card := by
    rw [← Fintype.card_subtype]
    exact Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter _ _).symm
  have hn : 2 ≤ Fintype.card α := by
    have : ({a₀, a₁} : Finset α).card ≤ Fintype.card α := Finset.card_le_univ _
    rw [Finset.card_insert_of_notMem (by simp [Ne.symm ha]), Finset.card_singleton] at this
    omega
  have hpow : (2 : ℕ) ^ (Fintype.card α - 1) = 2 * 2 ^ (Fintype.card α - 2) := by
    conv_lhs => rw [show Fintype.card α - 1 = (Fintype.card α - 2) + 1 by omega]
    ring
  omega

end Counting

section PositiveState

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The observables of the observer context at `v`: the edges incident to `v`. -/
abbrev ContextEdges (v : V) := {e : G.edgeSet // v ∈ (e : Sym2 V)}

/-- The observables of a context are exactly its incident edges. -/
def contextEdgesEquivIncidence (v : V) : ContextEdges G v ≃ G.incidenceSet v where
  toFun e := ⟨(e : Sym2 V), e.1.2, e.2⟩
  invFun e := ⟨⟨(e : Sym2 V), e.2.1⟩, e.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- A context has exactly `deg v` observables. -/
theorem card_contextEdges (v : V) : Fintype.card (ContextEdges G v) = G.degree v := by
  rw [← SimpleGraph.card_incidenceSet_eq_degree G v]
  exact Fintype.card_congr (contextEdgesEquivIncidence G v)

/-- **Local classical laws.**  A context of degree at least one admits exactly `2 ^ (deg v − 1)`
assignments of its observables obeying its parity equation. -/
theorem card_localLaws (b : V → ZMod 2) (v : V) (hv : 1 ≤ G.degree v) :
    Fintype.card {y : ContextEdges G v → ZMod 2 // ∑ e, y e = b v} = 2 ^ (G.degree v - 1) := by
  have hcard : 0 < Fintype.card (ContextEdges G v) := by rw [card_contextEdges]; omega
  obtain ⟨a₀⟩ := Fintype.card_pos_iff.mp hcard
  rw [Fintype.card_subtype, card_parityFiber a₀ (b v), card_contextEdges]

/-- **Uniform marginals of the local laws.**  In a context of degree at least two, prescribing the
value of one incident observable leaves exactly `2 ^ (deg v − 2)` local classical laws, the same
count for either value. -/
theorem card_localLaws_fixed (b : V → ZMod 2) (v : V) (hv : 2 ≤ G.degree v)
    (e : ContextEdges G v) (t : ZMod 2) :
    Fintype.card {y : ContextEdges G v → ZMod 2 // y e = t ∧ ∑ f, y f = b v}
      = 2 ^ (G.degree v - 2) := by
  have hcard : 1 < Fintype.card (ContextEdges G v) := by rw [card_contextEdges]; omega
  obtain ⟨a₁, ha₁⟩ := Fintype.exists_ne_of_one_lt_card hcard e
  rw [card_parityFiber_fixed e a₁ ha₁ (b v) t, card_contextEdges]

/-- Local classical laws always exist at a context of positive degree. -/
theorem card_localLaws_pos (b : V → ZMod 2) (v : V) (hv : 1 ≤ G.degree v) :
    0 < Fintype.card {y : ContextEdges G v → ZMod 2 // ∑ e, y e = b v} := by
  rw [card_localLaws G b v hv]
  positivity

/-- **The uniform local law has uniform edge marginals.**  In a context of degree at least two, the
uniform distribution on the local classical laws assigns probability `1/2` to each value of each
incident observable. -/
theorem localLaw_marginal_prob (b : V → ZMod 2) (v : V) (hv : 2 ≤ G.degree v)
    (e : ContextEdges G v) (t : ZMod 2) :
    (Fintype.card {y : ContextEdges G v → ZMod 2 // y e = t ∧ ∑ f, y f = b v} : ℚ)
      / (Fintype.card {y : ContextEdges G v → ZMod 2 // ∑ f, y f = b v} : ℚ) = 1 / 2 := by
  rw [card_localLaws_fixed G b v hv e t, card_localLaws G b v (by omega)]
  have hd : G.degree v - 1 = (G.degree v - 2) + 1 := by omega
  rw [hd]
  push_cast [pow_succ]
  have h2 : ((2 : ℚ) ^ (G.degree v - 2)) ≠ 0 := by positivity
  field_simp

/-- **Compatibility on shared observables.**  Two contexts sharing an observable assign it the same
marginal, so the uniform local laws form a compatible positive empirical state on the whole cover. -/
theorem localLaw_marginal_compatible (b : V → ZMod 2) {u v : V} (hu : 2 ≤ G.degree u)
    (hv : 2 ≤ G.degree v) (e : G.edgeSet) (heu : u ∈ (e : Sym2 V)) (hev : v ∈ (e : Sym2 V))
    (t : ZMod 2) :
    (Fintype.card {y : ContextEdges G u → ZMod 2 // y ⟨e, heu⟩ = t ∧ ∑ f, y f = b u} : ℚ)
        / (Fintype.card {y : ContextEdges G u → ZMod 2 // ∑ f, y f = b u} : ℚ)
      = (Fintype.card {y : ContextEdges G v → ZMod 2 // y ⟨e, hev⟩ = t ∧ ∑ f, y f = b v} : ℚ)
        / (Fintype.card {y : ContextEdges G v → ZMod 2 // ∑ f, y f = b v} : ℚ) := by
  rw [localLaw_marginal_prob G b u hu, localLaw_marginal_prob G b v hv]

/-- A global classical law restricts at every context to a local classical law. -/
theorem restrict_eq_of_parityBoundary_eq {x : G.edgeSet → ZMod 2} {b : V → ZMod 2}
    (hx : parityBoundary G x = b) (v : V) :
    ∑ e : ContextEdges G v, x (e : G.edgeSet) = b v := by
  rw [← parityBoundary_apply_incidence, hx]

/-- **Global classical laws are exactly the solutions of the boundary equation.** -/
theorem exists_global_law_iff (b : V → ZMod 2) :
    (∃ x : G.edgeSet → ZMod 2, ∀ v, ∑ e : ContextEdges G v, x (e : G.edgeSet) = b v)
      ↔ ∃ x, parityBoundary G x = b := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, funext fun v => (parityBoundary_apply_incidence G x v).trans (hx v)⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, restrict_eq_of_parityBoundary_eq G hx⟩

/-- **Positivity does not classicalize.**  On a connected graph of minimum degree two carrying an
odd total parity charge: every context admits local classical laws; their uniform distributions give
every incident observable the uniform marginal `1/2`, hence agree on every shared observable; and
still no global classical law exists. -/
theorem positive_state_no_global_law (hG : G.Connected) {b : V → ZMod 2}
    (hdeg : ∀ v, 2 ≤ G.degree v) (hb : ∑ v, b v = 1) :
    (∀ v, 0 < Fintype.card {y : ContextEdges G v → ZMod 2 // ∑ e, y e = b v}) ∧
      (∀ (v : V) (e : ContextEdges G v) (t : ZMod 2),
        (Fintype.card {y : ContextEdges G v → ZMod 2 // y e = t ∧ ∑ f, y f = b v} : ℚ)
          / (Fintype.card {y : ContextEdges G v → ZMod 2 // ∑ f, y f = b v} : ℚ) = 1 / 2) ∧
      ¬ ∃ x : G.edgeSet → ZMod 2, ∀ v, ∑ e : ContextEdges G v, x (e : G.edgeSet) = b v := by
  refine ⟨fun v => card_localLaws_pos G b v (by have := hdeg v; omega),
    fun v e t => localLaw_marginal_prob G b v (hdeg v) e t, ?_⟩
  rw [exists_global_law_iff G b, exists_parityBoundary_eq_iff G hG b, hb]
  exact one_ne_zero

end PositiveState

section NativeModels

/-- The triangle context system: three observers, each pair sharing one binary observable. -/
abbrev triangleContexts : SimpleGraph (Fin 3) := ⊤

theorem triangleContexts_connected : triangleContexts.Connected := SimpleGraph.connected_top

theorem triangleContexts_degree (v : Fin 3) : triangleContexts.degree v = 2 := by
  have h := SimpleGraph.complete_graph_degree (V := Fin 3) v
  rw [Fintype.card_fin] at h
  exact h

/-- **The triangle is contextual.**  With an odd total parity charge the triangle admits no global
classical law, every proper set of its observers is jointly satisfiable, and the uniform local laws
give every observable the marginal `1/2`. -/
theorem triangle_contextual (v₀ : Fin 3) :
    (¬ ∃ x, parityBoundary triangleContexts x = Pi.single v₀ 1) ∧
      (∀ W : Finset (Fin 3), W ≠ Finset.univ →
        ∃ x, ∀ v ∈ W, parityBoundary triangleContexts x v = (Pi.single v₀ 1 : Fin 3 → ZMod 2) v) ∧
      (∀ (v : Fin 3) (e : ContextEdges triangleContexts v) (t : ZMod 2),
        (Fintype.card {y : ContextEdges triangleContexts v → ZMod 2 //
            y e = t ∧ ∑ f, y f = (Pi.single v₀ 1 : Fin 3 → ZMod 2) v} : ℚ)
          / (Fintype.card {y : ContextEdges triangleContexts v → ZMod 2 //
              ∑ f, y f = (Pi.single v₀ 1 : Fin 3 → ZMod 2) v} : ℚ) = 1 / 2) := by
  have hb : ∑ v, (Pi.single v₀ 1 : Fin 3 → ZMod 2) v = 1 := sum_pi_single_eq v₀ 1
  obtain ⟨h1, h2, h3⟩ :=
    positive_state_no_global_law triangleContexts triangleContexts_connected
      (b := Pi.single v₀ 1) (fun v => by rw [triangleContexts_degree]) hb
  refine ⟨?_, ?_, h2⟩
  · rw [← exists_global_law_iff]
    exact h3
  · exact (properFace_blindness triangleContexts triangleContexts_connected hb).2

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

instance completeBipartiteGraph.instDecidableRelAdj :
    DecidableRel (completeBipartiteGraph V W).Adj := by
  intro a b
  cases a <;> cases b <;> simp [completeBipartiteGraph] <;> infer_instance

omit [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] in
theorem completeBipartiteGraph_adj_inl_inr (x : V) (y : W) :
    (completeBipartiteGraph V W).Adj (Sum.inl x) (Sum.inr y) := Or.inl ⟨rfl, rfl⟩

omit [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] in
/-- A complete bipartite graph with both sides inhabited is connected. -/
theorem completeBipartiteGraph_connected [Nonempty V] [Nonempty W] :
    (completeBipartiteGraph V W).Connected := by
  refine ⟨?_⟩
  intro a b
  cases a with
  | inl x =>
    cases b with
    | inl y =>
      exact ((completeBipartiteGraph_adj_inl_inr x (Classical.arbitrary W)).reachable).trans
        ((completeBipartiteGraph_adj_inl_inr y (Classical.arbitrary W)).reachable.symm)
    | inr y => exact (completeBipartiteGraph_adj_inl_inr x y).reachable
  | inr x =>
    cases b with
    | inl y => exact (completeBipartiteGraph_adj_inl_inr y x).reachable.symm
    | inr y =>
      exact ((completeBipartiteGraph_adj_inl_inr (Classical.arbitrary V) x).reachable.symm).trans
        (completeBipartiteGraph_adj_inl_inr (Classical.arbitrary V) y).reachable

theorem completeBipartiteGraph_degree_inl (x : V) :
    (completeBipartiteGraph V W).degree (Sum.inl x) = Fintype.card W := by
  have hnb : (completeBipartiteGraph V W).neighborFinset (Sum.inl x)
      = Finset.univ.image Sum.inr := by
    ext w; cases w <;> simp [SimpleGraph.mem_neighborFinset, completeBipartiteGraph]
  simp only [SimpleGraph.degree, hnb]
  rw [Finset.card_image_of_injective _ Sum.inr_injective, Finset.card_univ]

theorem completeBipartiteGraph_degree_inr (y : W) :
    (completeBipartiteGraph V W).degree (Sum.inr y) = Fintype.card V := by
  have hnb : (completeBipartiteGraph V W).neighborFinset (Sum.inr y)
      = Finset.univ.image Sum.inl := by
    ext w; cases w <;> simp [SimpleGraph.mem_neighborFinset, completeBipartiteGraph]
  simp only [SimpleGraph.degree, hnb]
  rw [Finset.card_image_of_injective _ Sum.inl_injective, Finset.card_univ]

/-- The Peres–Mermin context skeleton: three row contexts and three column contexts sharing nine
binary observables. -/
abbrev peresMerminContexts : SimpleGraph (Fin 3 ⊕ Fin 3) := completeBipartiteGraph (Fin 3) (Fin 3)

theorem peresMerminContexts_degree (v : Fin 3 ⊕ Fin 3) : peresMerminContexts.degree v = 3 := by
  cases v with
  | inl x => rw [show peresMerminContexts.degree (Sum.inl x) = Fintype.card (Fin 3) from
      completeBipartiteGraph_degree_inl x, Fintype.card_fin]
  | inr y => rw [show peresMerminContexts.degree (Sum.inr y) = Fintype.card (Fin 3) from
      completeBipartiteGraph_degree_inr y, Fintype.card_fin]

/-- **The Peres–Mermin skeleton is contextual.**  Charging exactly one of the six contexts oddly
leaves no global classical law, keeps every proper set of contexts jointly satisfiable, and still
supports the compatible uniform positive state. -/
theorem peresMermin_contextual (v₀ : Fin 3 ⊕ Fin 3) :
    (¬ ∃ x, parityBoundary peresMerminContexts x = Pi.single v₀ 1) ∧
      (∀ S : Finset (Fin 3 ⊕ Fin 3), S ≠ Finset.univ →
        ∃ x, ∀ v ∈ S, parityBoundary peresMerminContexts x v
          = (Pi.single v₀ 1 : (Fin 3 ⊕ Fin 3) → ZMod 2) v) ∧
      (∀ (v : Fin 3 ⊕ Fin 3) (e : ContextEdges peresMerminContexts v) (t : ZMod 2),
        (Fintype.card {y : ContextEdges peresMerminContexts v → ZMod 2 //
            y e = t ∧ ∑ f, y f = (Pi.single v₀ 1 : (Fin 3 ⊕ Fin 3) → ZMod 2) v} : ℚ)
          / (Fintype.card {y : ContextEdges peresMerminContexts v → ZMod 2 //
              ∑ f, y f = (Pi.single v₀ 1 : (Fin 3 ⊕ Fin 3) → ZMod 2) v} : ℚ) = 1 / 2) := by
  have hb : ∑ v, (Pi.single v₀ 1 : (Fin 3 ⊕ Fin 3) → ZMod 2) v = 1 := sum_pi_single_eq v₀ 1
  have hconn : peresMerminContexts.Connected := completeBipartiteGraph_connected
  obtain ⟨h1, h2, h3⟩ :=
    positive_state_no_global_law peresMerminContexts hconn (b := Pi.single v₀ 1)
      (fun v => by rw [peresMerminContexts_degree]; omega) hb
  refine ⟨?_, ?_, h2⟩
  · rw [← exists_global_law_iff]
    exact h3
  · exact (properFace_blindness peresMerminContexts hconn hb).2

end NativeModels

end GaloisForLFunctions.HTGeometry
