import GaloisForLFunctions.HTGeometry.StokesContactTomography

/-!
# Decorated Stokes cores and contact tomography

This file defines the exact rescaling from an integral core matrix and positive ramifications to
complementary contact.  It proves the strict integral obstruction by clearing positive
denominators and proves that any two rooted realizations of one decorated core have the same
labelled threshold hierarchy.
-/

namespace GaloisForLFunctions
namespace IrregularStokes

/-- Symmetric integral Stokes core with positive ramification decoration. -/
structure DecoratedStokesCore (n : ℕ) where
  B : Fin n → Fin n → ℤ
  B_symm : ∀ i j, B i j = B j i
  ramification : Fin n → ℕ
  ramification_pos : ∀ i, 0 < ramification i

namespace DecoratedStokesCore

/-- Diagonal complementary contact `1 + (Bᵢᵢ-1)/rᵢ²`. -/
def diagonalContact {n : ℕ} (g : DecoratedStokesCore n) (i : Fin n) : ℚ :=
  1 + ((g.B i i - 1 : ℤ) : ℚ) / ((g.ramification i : ℚ) ^ (2 : ℕ))

/-- Off-diagonal complementary contact `1 + Bᵢⱼ/(rᵢrⱼ)`. -/
def pairContact {n : ℕ} (g : DecoratedStokesCore n) (i j : Fin n) : ℚ :=
  1 + (g.B i j : ℚ) / ((g.ramification i : ℚ) * (g.ramification j : ℚ))

theorem pairContact_symm {n : ℕ} (g : DecoratedStokesCore n) (i j : Fin n) :
    g.pairContact i j = g.pairContact j i := by
  simp only [pairContact, g.B_symm]
  rw [mul_comm]

/-- Unified diagonal/off-diagonal complementary-contact matrix. -/
def contactMatrix {n : ℕ} (g : DecoratedStokesCore n) (i j : Fin n) : ℚ :=
  if i = j then g.diagonalContact i else g.pairContact i j

@[simp] theorem contactMatrix_self {n : ℕ} (g : DecoratedStokesCore n) (i : Fin n) :
    g.contactMatrix i i = g.diagonalContact i := by simp [contactMatrix]

theorem contactMatrix_of_ne {n : ℕ} (g : DecoratedStokesCore n) {i j : Fin n}
    (hij : i ≠ j) : g.contactMatrix i j = g.pairContact i j := by
  simp [contactMatrix, hij]

theorem contactMatrix_symm {n : ℕ} (g : DecoratedStokesCore n) (i j : Fin n) :
    g.contactMatrix i j = g.contactMatrix j i := by
  by_cases hij : i = j
  · subst j
    rfl
  · rw [g.contactMatrix_of_ne hij, g.contactMatrix_of_ne (Ne.symm hij), g.pairContact_symm]

/-- Clearing positive ramification denominators converts strict contact separation into the exact
integral core inequality. -/
theorem strictDiagonal_iff {n : ℕ} (g : DecoratedStokesCore n) (i j : Fin n) :
    g.diagonalContact i < g.pairContact i j ↔
      (g.ramification j : ℤ) * (g.B i i - 1) <
        (g.ramification i : ℤ) * g.B i j := by
  have hriN : 0 < g.ramification i := g.ramification_pos i
  have hrjN : 0 < g.ramification j := g.ramification_pos j
  have hri : 0 < (g.ramification i : ℚ) := by exact_mod_cast hriN
  have hrj : 0 < (g.ramification j : ℚ) := by exact_mod_cast hrjN
  simp only [diagonalContact, pairContact, add_lt_add_iff_left]
  rw [div_lt_div_iff₀ (sq_pos_of_pos hri) (mul_pos hri hrj)]
  norm_num
  constructor <;> intro h
  · have h' : (g.ramification i : ℚ) *
        ((g.ramification j : ℚ) * ((g.B i i - 1 : ℤ) : ℚ)) <
        (g.ramification i : ℚ) *
          ((g.ramification i : ℚ) * (g.B i j : ℚ)) := by
      simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using h
    exact_mod_cast (lt_of_mul_lt_mul_left h' hri.le)
  · have hq : (g.ramification j : ℚ) * ((g.B i i - 1 : ℤ) : ℚ) <
        (g.ramification i : ℚ) * (g.B i j : ℚ) := by exact_mod_cast h
    have h' := mul_lt_mul_of_pos_left hq hri
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using h'

/-- Real-valued form of the core contact matrix used by rooted contact trees. -/
def realContactMatrix {n : ℕ} (g : DecoratedStokesCore n) (i j : Fin n) : ℝ :=
  g.contactMatrix i j

theorem realContactMatrix_symm {n : ℕ} (g : DecoratedStokesCore n) (i j : Fin n) :
    g.realContactMatrix i j = g.realContactMatrix j i := by
  simp only [realContactMatrix]
  exact_mod_cast g.contactMatrix_symm i j

/-- A rooted fission skeleton whose complementary-contact matrix is exactly the rescaled decorated
core matrix. -/
structure RootedRealization {n : ℕ} (g : DecoratedStokesCore n) where
  tree : RootedContactTree n
  contact_eq : ∀ i j, tree.contact i j = g.realContactMatrix i j

/-- Strict diagonal separation in a rooted realization forces the new integral core obstruction. -/
theorem RootedRealization.strictCoreObstruction {n : ℕ} {g : DecoratedStokesCore n}
    (realization : RootedRealization g) {i j : Fin n} (hij : i ≠ j) :
    (g.ramification j : ℤ) * (g.B i i - 1) <
      (g.ramification i : ℤ) * g.B i j := by
  apply (g.strictDiagonal_iff i j).mp
  have htree := realization.tree.contact_diagonal_lt hij
  rw [realization.contact_eq i i, realization.contact_eq i j] at htree
  simp only [realContactMatrix, contactMatrix_self] at htree
  rw [g.contactMatrix_of_ne hij] at htree
  exact_mod_cast htree

/-- **Decorated-core contact tomography.**  Any two rooted realizations of one decorated core have
the same canonical labelled branching hierarchy. -/
theorem RootedRealization.hierarchy_unique {n : ℕ} {g : DecoratedStokesCore n}
    (s t : RootedRealization g) : s.tree.hierarchy = t.tree.hierarchy := by
  apply RootedContactTree.hierarchy_eq_of_contact_eq
  intro i j
  rw [s.contact_eq, t.contact_eq]

/-- **The integral sharpening of the strict diagonal obstruction.**  Both sides of the strict
inequality are integers, so the left side exceeds the right by at least one. -/
theorem RootedRealization.strictCoreObstruction_add_one_le {n : ℕ} {g : DecoratedStokesCore n}
    (realization : RootedRealization g) {i j : Fin n} (hij : i ≠ j) :
    (g.ramification j : ℤ) * (g.B i i - 1) + 1 ≤ (g.ramification i : ℤ) * g.B i j :=
  Int.add_one_le_iff.mpr (realization.strictCoreObstruction hij)

/-- **`(8.2)` as the card states it: the pair of strict arithmetic obstructions.**  Lemma 8.1 gives
strict separation of the diagonal from the edge at both endpoints, so a rooted realization forces
both integral inequalities, with the same off-diagonal entry on the right by symmetry of the core. -/
theorem RootedRealization.strictCorePairObstruction {n : ℕ} {g : DecoratedStokesCore n}
    (realization : RootedRealization g) {i j : Fin n} (hij : i ≠ j) :
    (g.ramification j : ℤ) * (g.B i i - 1) < (g.ramification i : ℤ) * g.B i j ∧
      (g.ramification i : ℤ) * (g.B j j - 1) < (g.ramification j : ℤ) * g.B i j := by
  refine ⟨realization.strictCoreObstruction hij, ?_⟩
  have h := realization.strictCoreObstruction (Ne.symm hij)
  rwa [g.B_symm j i] at h

/-- **The integral sharpening of both obstructions.**  Both sides of each inequality are integers,
so each left side is at least the corresponding right side plus one. -/
theorem RootedRealization.strictCorePairObstruction_add_one_le {n : ℕ} {g : DecoratedStokesCore n}
    (realization : RootedRealization g) {i j : Fin n} (hij : i ≠ j) :
    (g.ramification j : ℤ) * (g.B i i - 1) + 1 ≤ (g.ramification i : ℤ) * g.B i j ∧
      (g.ramification i : ℤ) * (g.B j j - 1) + 1 ≤ (g.ramification j : ℤ) * g.B i j := by
  obtain ⟨h₁, h₂⟩ := realization.strictCorePairObstruction hij
  exact ⟨Int.add_one_le_iff.mpr h₁, Int.add_one_le_iff.mpr h₂⟩

end DecoratedStokesCore

end IrregularStokes
end GaloisForLFunctions
