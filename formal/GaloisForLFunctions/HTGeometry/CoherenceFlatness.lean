import GaloisForLFunctions.HTGeometry.CoherenceEndReconstruction

/-!
# Flat Boolean edge fields

A symmetric Boolean edge field on a connected graph is induced by a vertex orientation exactly
when every finite closed walk has trivial XOR holonomy. The inducing orientation is unique up to
global complement by the exact reconstruction theorem.
-/

namespace GaloisForLFunctions.HTGeometry

universe u
variable {V : Type u}

/-- Boolean sum of edge labels along a finite walk. -/
def walkXor {G : SimpleGraph V} (c : V → V → Bool) :
    {u v : V} → G.Walk u v → Bool
  | _, _, .nil => false
  | u, _, .cons (v := v) _ p => Bool.xor (c u v) (walkXor c p)

@[simp] theorem walkXor_nil {G : SimpleGraph V} (c : V → V → Bool) (u : V) :
    walkXor c (SimpleGraph.Walk.nil : G.Walk u u) = false := rfl

@[simp] theorem walkXor_cons {G : SimpleGraph V} (c : V → V → Bool)
    {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    walkXor c (.cons h p) = Bool.xor (c u v) (walkXor c p) := rfl

theorem walkXor_append {G : SimpleGraph V} (c : V → V → Bool)
    {u v w : V} (p : G.Walk u v) (q : G.Walk v w) :
    walkXor c (p.append q) = Bool.xor (walkXor c p) (walkXor c q) := by
  induction p with
  | nil => simp
  | cons h p ih => simp [ih]

/-- Symmetry of a Boolean edge label on graph edges. -/
def BooleanEdgeFieldSymmetric (G : SimpleGraph V) (c : V → V → Bool) : Prop :=
  ∀ ⦃u v⦄, G.Adj u v → c u v = c v u

theorem walkXor_reverse {G : SimpleGraph V} (c : V → V → Bool)
    (hc : BooleanEdgeFieldSymmetric G c)
    {u v : V} (p : G.Walk u v) :
    walkXor c p.reverse = walkXor c p := by
  induction p with
  | nil => rfl
  | @cons u v w h p ih =>
      rw [SimpleGraph.Walk.reverse_cons, walkXor_append, ih]
      simp only [walkXor_cons, walkXor_nil, Bool.xor_false]
      rw [hc h]
      exact Bool.xor_comm _ _

/-- A Boolean edge field is flat when every finite closed walk has trivial XOR holonomy. -/
def BooleanEdgeFieldFlat (G : SimpleGraph V) (c : V → V → Bool) : Prop :=
  ∀ (u : V) (p : G.Walk u u), walkXor c p = false

theorem walkXor_of_booleanCoboundary
    {G : SimpleGraph V} (ε : V → Bool) (c : V → V → Bool)
    (hc : ∀ ⦃u v⦄, G.Adj u v → c u v = Bool.xor (ε u) (ε v))
    {u v : V} (p : G.Walk u v) :
    walkXor c p = Bool.xor (ε u) (ε v) := by
  induction p with
  | nil => exact (Bool.xor_self _).symm
  | @cons u v w h p ih =>
      rw [walkXor_cons, hc h, ih]
      cases ε u <;> cases ε v <;> cases ε w <;> rfl

theorem booleanEdgeFieldFlat_of_coboundary
    {G : SimpleGraph V} (ε : V → Bool) (c : V → V → Bool)
    (hc : ∀ ⦃u v⦄, G.Adj u v → c u v = Bool.xor (ε u) (ε v)) :
    BooleanEdgeFieldFlat G c := by
  intro u p
  rw [walkXor_of_booleanCoboundary ε c hc p]
  exact Bool.xor_self _

/-- **Boolean flatness criterion.**  On a connected graph, a symmetric Boolean edge field is a
vertex coboundary exactly when every finite closed walk has trivial holonomy. -/
theorem exists_booleanOrientation_of_flat
    {G : SimpleGraph V} (hG : G.Connected) (c : V → V → Bool)
    (hsymm : BooleanEdgeFieldSymmetric G c)
    (hflat : BooleanEdgeFieldFlat G c) :
    ∃ ε : V → Bool, ∀ ⦃u v⦄, G.Adj u v →
      c u v = Bool.xor (ε u) (ε v) := by
  classical
  let root : V := Classical.choice hG.nonempty
  let path : ∀ v : V, G.Walk root v := fun v => Classical.choice (hG root v)
  let ε : V → Bool := fun v => walkXor c (path v)
  refine ⟨ε, ?_⟩
  intro u v huv
  let closed : G.Walk root root :=
    (path u).append (huv.toWalk.append (path v).reverse)
  have hclosed := hflat root closed
  rw [walkXor_append, walkXor_append, walkXor_reverse c hsymm] at hclosed
  simp only [walkXor_cons, walkXor_nil, Bool.xor_false] at hclosed
  change Bool.xor (ε u) (Bool.xor (c u v) (ε v)) = false at hclosed
  cases hεu : ε u <;> cases hεv : ε v <;> cases hcuv : c u v <;> simp_all

theorem booleanEdgeField_coboundary_iff_flat
    {G : SimpleGraph V} (hG : G.Connected) (c : V → V → Bool)
    (hsymm : BooleanEdgeFieldSymmetric G c) :
    (∃ ε : V → Bool, ∀ ⦃u v⦄, G.Adj u v →
      c u v = Bool.xor (ε u) (ε v)) ↔
      BooleanEdgeFieldFlat G c := by
  constructor
  · rintro ⟨ε, hε⟩
    exact booleanEdgeFieldFlat_of_coboundary ε c hε
  · exact exists_booleanOrientation_of_flat hG c hsymm

end GaloisForLFunctions.HTGeometry

