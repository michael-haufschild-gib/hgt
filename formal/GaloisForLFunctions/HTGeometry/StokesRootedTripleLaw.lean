import GaloisForLFunctions.HTGeometry.StokesUniversalContactLaw

/-!
# Rooted triples and the diagram form of Stokes energy

Strict antitonicity of complementary contact turns a strictly nested pair of meets into a strict
contact inequality together with an equality of the two opposite contacts.  This is the rooted
triple law: the contact matrix reads off which of three labels branches away first.  The second
half of the file writes the polarized energy of a decorated core in its integral diagram
coordinates.
-/

namespace GaloisForLFunctions
namespace IrregularStokes

namespace RootedContactTree

/-- **Rooted triple law.**  The meet of `i` and `j` lies strictly above the meet of `i` and `k`
exactly when their contacts satisfy `K i j < K i k = K j k`. -/
theorem rootedTriple_iff {n : ℕ} (t : RootedContactTree n) (i j k : Fin n) :
    t.leaf i ⊓ t.leaf k < t.leaf i ⊓ t.leaf j ↔
      t.contact i j < t.contact i k ∧ t.contact i k = t.contact j k := by
  constructor
  · intro hlt
    refine ⟨t.kappa_strictAnti hlt, ?_⟩
    have hkj : t.leaf k ⊓ t.leaf j = t.leaf i ⊓ t.leaf k := inf_eq_of_inf_lt_inf hlt
    have hval : t.contact k j = t.contact i k := congrArg t.kappa hkj
    rw [← hval, t.contact_symm j k]
  · rintro ⟨hij, -⟩
    have hle : t.leaf i ⊓ t.leaf k ≤ t.leaf j :=
      (t.contact_le_contact_iff_le_leaf i k j).mp hij.le
    refine lt_of_le_of_ne (le_inf inf_le_left hle) ?_
    intro heq
    exact hij.ne' (congrArg t.kappa heq)

/-- Nested meets are read off from the contact matrix alone. -/
theorem contact_lt_of_inf_lt_inf {n : ℕ} (t : RootedContactTree n) {i j k : Fin n}
    (h : t.leaf i ⊓ t.leaf k < t.leaf i ⊓ t.leaf j) :
    t.contact i j < t.contact i k :=
  ((t.rootedTriple_iff i j k).mp h).1

/-- A strictly nested meet forces the two opposite contacts to agree. -/
theorem contact_eq_of_inf_lt_inf {n : ℕ} (t : RootedContactTree n) {i j k : Fin n}
    (h : t.leaf i ⊓ t.leaf k < t.leaf i ⊓ t.leaf j) :
    t.contact i k = t.contact j k :=
  ((t.rootedTriple_iff i j k).mp h).2

end RootedContactTree

namespace DecoratedStokesCore

/-- Polarized energy of a decorated core in integral diagram coordinates. -/
theorem energy_eq_diagram {n : ℕ} (g : DecoratedStokesCore n) {i j : Fin n} (hij : i ≠ j) :
    g.energy i j =
      2 * (g.B i j : ℝ) / ((g.ramification i : ℝ) * (g.ramification j : ℝ)) -
        ((g.B i i : ℝ) - 1) / (g.ramification i : ℝ) ^ (2 : ℕ) -
        ((g.B j j : ℝ) - 1) / (g.ramification j : ℝ) ^ (2 : ℕ) := by
  have hri : ((g.ramification i : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (g.ramification_pos i).ne'
  have hrj : ((g.ramification j : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (g.ramification_pos j).ne'
  simp only [energy, realContactMatrix, contactMatrix_self, g.contactMatrix_of_ne hij,
    diagonalContact, pairContact]
  push_cast
  field_simp
  ring

end DecoratedStokesCore

end IrregularStokes
end GaloisForLFunctions
