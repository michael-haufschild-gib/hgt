import GaloisForLFunctions.HTGeometry.CoherenceFlatness

/-!
# Realizations of the Boolean edge-symmetry interface

Constant fields, vertex coboundaries, pointwise conjunctions and disjunctions of vertex data, and
the canonical symmetric part `u v ↦ c u v ⊕ c v u` of an arbitrary field all satisfy the symmetry
interface.  Since the symmetric part is available for every field, the Boolean flatness criterion
applies on a connected graph with no symmetry premise at all.
-/

namespace GaloisForLFunctions.HTGeometry

variable {V : Type*}

/-! ## Realizations -/

theorem booleanEdgeFieldSymmetric_const (G : SimpleGraph V) (b : Bool) :
    BooleanEdgeFieldSymmetric G (fun _ _ => b) := by
  intro _ _ _
  rfl

/-- Every vertex coboundary is symmetric. -/
theorem booleanEdgeFieldSymmetric_xor (G : SimpleGraph V) (ε : V → Bool) :
    BooleanEdgeFieldSymmetric G (fun u v => Bool.xor (ε u) (ε v)) := by
  intro u v _
  exact Bool.xor_comm (ε u) (ε v)

theorem booleanEdgeFieldSymmetric_and (G : SimpleGraph V) (f : V → Bool) :
    BooleanEdgeFieldSymmetric G (fun u v => f u && f v) := by
  intro u v _
  exact Bool.and_comm (f u) (f v)

theorem booleanEdgeFieldSymmetric_or (G : SimpleGraph V) (f : V → Bool) :
    BooleanEdgeFieldSymmetric G (fun u v => f u || f v) := by
  intro u v _
  exact Bool.or_comm (f u) (f v)

/-- The symmetric part of an arbitrary Boolean edge field. -/
def booleanEdgeSymmetricPart (c : V → V → Bool) : V → V → Bool :=
  fun u v => Bool.xor (c u v) (c v u)

/-- **Every field has a symmetric part.**  The symmetrization always satisfies the interface. -/
theorem booleanEdgeFieldSymmetric_symmetricPart (G : SimpleGraph V) (c : V → V → Bool) :
    BooleanEdgeFieldSymmetric G (booleanEdgeSymmetricPart c) := by
  intro u v _
  exact Bool.xor_comm (c u v) (c v u)

/-- A field that already satisfies the interface is its own symmetric part up to the diagonal
relation `x ⊕ x = false`: symmetrization sends it to the zero field on edges. -/
theorem booleanEdgeSymmetricPart_eq_false_of_symmetric {G : SimpleGraph V}
    {c : V → V → Bool} (hc : BooleanEdgeFieldSymmetric G c)
    {u v : V} (huv : G.Adj u v) :
    booleanEdgeSymmetricPart c u v = false := by
  rw [booleanEdgeSymmetricPart, hc huv]
  exact Bool.xor_self (c v u)

/-! ## The criterion with no symmetry premise -/

/-- **Flatness criterion for coboundaries.**  On a connected graph the coboundary/flatness
equivalence holds for every vertex coboundary, with no symmetry premise. -/
theorem booleanEdgeField_coboundary_iff_flat_xor {G : SimpleGraph V}
    (hG : G.Connected) (ε : V → Bool) :
    (∃ δ : V → Bool, ∀ ⦃u v⦄, G.Adj u v →
        Bool.xor (ε u) (ε v) = Bool.xor (δ u) (δ v)) ↔
      BooleanEdgeFieldFlat G (fun u v => Bool.xor (ε u) (ε v)) :=
  booleanEdgeField_coboundary_iff_flat hG _ (booleanEdgeFieldSymmetric_xor G ε)

/-- **Flatness criterion for the symmetric part of an arbitrary field.**  On a connected graph the
coboundary/flatness equivalence holds for the symmetrization of every Boolean edge field, with no
symmetry premise. -/
theorem booleanEdgeField_coboundary_iff_flat_symmetricPart {G : SimpleGraph V}
    (hG : G.Connected) (c : V → V → Bool) :
    (∃ ε : V → Bool, ∀ ⦃u v⦄, G.Adj u v →
        booleanEdgeSymmetricPart c u v = Bool.xor (ε u) (ε v)) ↔
      BooleanEdgeFieldFlat G (booleanEdgeSymmetricPart c) :=
  booleanEdgeField_coboundary_iff_flat hG _
    (booleanEdgeFieldSymmetric_symmetricPart G c)

/-- **Flatness criterion for constant fields.** -/
theorem booleanEdgeField_coboundary_iff_flat_const {G : SimpleGraph V}
    (hG : G.Connected) (b : Bool) :
    (∃ ε : V → Bool, ∀ ⦃u v⦄, G.Adj u v → b = Bool.xor (ε u) (ε v)) ↔
      BooleanEdgeFieldFlat G (fun _ _ => b) :=
  booleanEdgeField_coboundary_iff_flat hG _ (booleanEdgeFieldSymmetric_const G b)

end GaloisForLFunctions.HTGeometry
