import GaloisForLFunctions.HTGeometry.LocalSpectralExtensionRelationRigidity
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions

/-!
# Parity-complete interaction-lift rigidity

The two-layer interaction lift of a connected graph is connected exactly
when odd-walk parity can be changed in the old graph.  This module removes
the earlier triangle hypothesis: an odd closed walk of arbitrary length is
enough.  Together with the spare-label argument for three or more layers,
this gives one theorem for every finite local alphabet of cardinality at
least two.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Cross-layer coefficient equality alternates the Boolean label along a
walk.  Even walks preserve the label and odd walks reverse it. -/
theorem crossLayerEquality_walk_bool
    {α β : Type*}
    (G : SimpleGraph α) (coefficient : α → Bool → β)
    (hcross :
      ∀ ⦃a b⦄, G.Adj a b →
        ∀ ⦃r s : Bool⦄, r ≠ s →
          coefficient a r = coefficient b s) :
    ∀ ⦃a b⦄ (p : G.Walk a b),
      (Even p.length →
        ∀ r, coefficient a r = coefficient b r) ∧
      (Odd p.length →
        ∀ r, coefficient a r = coefficient b (!r)) := by
  intro a b p
  induction p with
  | nil =>
      constructor
      · intro _ r
        rfl
      · intro hodd
        simp at hodd
  | @cons a b c hab p ih =>
      constructor
      · intro heven r
        have hpodd : Odd p.length := by
          rw [SimpleGraph.Walk.length_cons, Nat.even_add_one] at heven
          exact Nat.not_even_iff_odd.mp heven
        calc
          coefficient a r = coefficient b (!r) :=
            hcross hab (Bool.not_ne_self r).symm
          _ = coefficient c (!(!r)) := ih.2 hpodd (!r)
          _ = coefficient c r := by cases r <;> rfl
      · intro hodd r
        have hpeven : Even p.length := by
          rw [SimpleGraph.Walk.length_cons, Nat.odd_add_one] at hodd
          exact Nat.not_odd_iff_even.mp hodd
        calc
          coefficient a r = coefficient b (!r) :=
            hcross hab (Bool.not_ne_self r).symm
          _ = coefficient c (!r) := ih.1 hpeven (!r)

/-- A connected nonbipartite graph removes the Boolean parity obstruction
from every cross-layer coefficient packet.  No triangle is required. -/
theorem crossLayerEquality_constant_bool_of_not_isBipartite
    {α β : Type*}
    (G : SimpleGraph α) (coefficient : α → Bool → β)
    (hconnected : G.Preconnected)
    (hnonbipartite : ¬ G.IsBipartite)
    (hcross :
      ∀ ⦃a b⦄, G.Adj a b →
        ∀ ⦃r s : Bool⦄, r ≠ s →
          coefficient a r = coefficient b s) :
    ∀ a r b s, coefficient a r = coefficient b s := by
  have hnotEven :
      ¬ ∀ u, ∀ w : G.Walk u u, Even w.length := by
    intro hall
    exact hnonbipartite
      (SimpleGraph.two_colorable_iff_forall_loop_even.mpr hall)
  push Not at hnotEven
  obtain ⟨root, loop, hloopNotEven⟩ := hnotEven
  have hloopOdd : Odd loop.length :=
    Nat.not_even_iff_odd.mp hloopNotEven
  have hrootFalseTrue :
      coefficient root false = coefficient root true := by
    simpa using
      (crossLayerEquality_walk_bool G coefficient hcross
        loop).2 hloopOdd false
  have hroot :
      ∀ r, coefficient root r = coefficient root false := by
    intro r
    cases r
    · rfl
    · exact hrootFalseTrue.symm
  have hedge :
      ∀ ⦃u v⦄, G.Adj u v →
        (∀ r, coefficient u r = coefficient root false) →
        ∀ s, coefficient v s = coefficient root false := by
    intro u v huv hu s
    calc
      coefficient v s = coefficient u (!s) :=
        (hcross huv (Bool.not_ne_self s)).symm
      _ = coefficient root false := hu (!s)
  have hwalk :
      ∀ ⦃u v⦄ (p : G.Walk u v),
        (∀ r, coefficient u r = coefficient root false) →
        ∀ s, coefficient v s = coefficient root false := by
    intro u v p
    induction p with
    | nil =>
        intro hu
        exact hu
    | cons huv p ih =>
        intro hu
        exact ih (hedge huv hu)
  intro a r b s
  obtain ⟨pa⟩ := hconnected root a
  obtain ⟨pb⟩ := hconnected root b
  exact (hwalk pa hroot r).trans (hwalk pb hroot s).symm

/-- The Boolean interaction lift of every connected nonbipartite graph is
connected.  Odd cycles of any length, not merely triangles, suffice. -/
theorem crossLayerLiftGraph_bool_preconnected_of_not_isBipartite
    {α : Type*}
    (G : SimpleGraph α)
    (hconnected : G.Preconnected)
    (hnonbipartite : ¬ G.IsBipartite) :
    (crossLayerLiftGraph G Bool).Preconnected := by
  intro x y
  apply SimpleGraph.ConnectedComponent.exact
  have hconstant :=
    crossLayerEquality_constant_bool_of_not_isBipartite G
      (fun a r =>
        (crossLayerLiftGraph G Bool).connectedComponentMk (a, r))
      hconnected hnonbipartite
      (fun {_ _} hab {_ _} hrs =>
        SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
          ((crossLayerLiftGraph_adj G _ _ _ _).2 ⟨hab, hrs⟩))
  exact hconstant x.1 x.2 y.1 y.2

/-- Every two-element alphabet is equivalent to the Boolean alphabet. -/
noncomputable def twoElementAlphabetEquivBool
    (ρ : Type*) [Fintype ρ]
    (hcard : Fintype.card ρ = 2) :
    ρ ≃ Bool :=
  Fintype.equivOfCardEq (by simpa using hcard)

/-- For an arbitrary finite alphabet of cardinality two, connected
nonbipartite old transition geometry leaves only the trace direction. -/
theorem crossLayerEquality_constant_of_card_eq_two
    {α ρ β : Type*} [Fintype ρ]
    (G : SimpleGraph α) (coefficient : α → ρ → β)
    (hcard : Fintype.card ρ = 2)
    (hconnected : G.Preconnected)
    (hnonbipartite : ¬ G.IsBipartite)
    (hcross :
      ∀ ⦃a b⦄, G.Adj a b →
        ∀ ⦃r s : ρ⦄, r ≠ s →
          coefficient a r = coefficient b s) :
    ∀ a r b s, coefficient a r = coefficient b s := by
  let e : ρ ≃ Bool := twoElementAlphabetEquivBool ρ hcard
  have hbool :=
    crossLayerEquality_constant_bool_of_not_isBipartite G
      (fun a r => coefficient a (e.symm r))
      hconnected hnonbipartite
      (fun {_ _} hab {_ _} hrs =>
        hcross hab (e.symm.injective.ne hrs))
  intro a r b s
  simpa using hbool a (e r) b (e s)

/-- The interaction lift is connected for every finite local alphabet with
at least two labels whenever the old graph is connected and nonbipartite.
This is the dimension-uniform parity theorem needed by heterogeneous leaf
extension. -/
theorem crossLayerLiftGraph_preconnected_of_two_le_card
    {α ρ : Type*} [Fintype ρ] [DecidableEq ρ] [Nonempty ρ]
    (G : SimpleGraph α)
    (hcard : 2 ≤ Fintype.card ρ)
    (hconnected : G.Preconnected)
    (hnonbipartite : ¬ G.IsBipartite) :
    (crossLayerLiftGraph G ρ).Preconnected := by
  by_cases hthree : 3 ≤ Fintype.card ρ
  · have hneighbour : ∀ a, ∃ b, G.Adj a b := by
      intro a
      by_contra hnone
      push Not at hnone
      have hallEq : ∀ b, b = a := by
        intro b
        obtain ⟨p⟩ := hconnected a b
        cases p with
        | nil => rfl
        | cons hab _ => exact (hnone _ hab).elim
      apply hnonbipartite
      change G.Colorable 2
      rw [SimpleGraph.two_colorable_iff_forall_loop_even]
      intro u w
      cases w with
      | nil => simp
      | cons huv _ =>
          exact
            (huv.ne ((hallEq _).trans (hallEq _).symm)).elim
    exact crossLayerLiftGraph_preconnected_of_spareLabel
      G (hasSpareLabel_of_three_le_card ρ hthree)
      hneighbour hconnected
  · have htwo : Fintype.card ρ = 2 := by omega
    intro x y
    apply SimpleGraph.ConnectedComponent.exact
    have hconstant :=
      crossLayerEquality_constant_of_card_eq_two G
        (fun a r =>
          (crossLayerLiftGraph G ρ).connectedComponentMk (a, r))
        htwo hconnected hnonbipartite
        (fun {_ _} hab {_ _} hrs =>
          SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
            ((crossLayerLiftGraph_adj G _ _ _ _).2 ⟨hab, hrs⟩))
    exact hconstant x.1 x.2 y.1 y.2

end

end GaloisForLFunctions.HTGeometry
