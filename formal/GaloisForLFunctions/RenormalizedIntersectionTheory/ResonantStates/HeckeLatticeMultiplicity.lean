import GaloisForLFunctions.RepresentationLifting.Lattices.RankTwoHermite
import GaloisForLFunctions.RenormalizedIntersectionTheory.ResonantStates.EveryHeckeOperatorIsDiagonalOnEisenstein

/-!
# Hecke multiplicity counts integral sublattices

The divisor pairs and residues in the classical Hecke operator are exactly
Hermite coordinates for positive-index sublattices of `ℤ²`. This identifies
its constant-function eigenvalue with the normalized lattice count from
Theorem 6.2 of Kurnosov–Ríos Ortiz, https://arxiv.org/abs/2611.01210.
-/

noncomputable section
open scoped BigOperators
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.ResonantStates
open GaloisForLFunctions.RepresentationLifting.RankTwoHermite

/-- The exact divisor-pair and residue labels summed over by `heckeN`. -/
def HeckeLatticeLabels (m : ℕ) :=
  Σ ad : {ad : ℕ × ℕ // ad ∈ m.divisorsAntidiagonal}, Fin ad.val.2

/-- Interchanging the periods puts the Hecke residue bound into Hermite convention. -/
def heckeTriangularCoordinates (n : ℕ) (p : HeckeLatticeLabels (n + 1)) : Coordinates :=
  ⟨p.1.val.2, p.1.val.1, (pos_of_mem_divisorsAntidiagonal p.1.property).2,
    (pos_of_mem_divisorsAntidiagonal p.1.property).1, p.2⟩

def heckeHermiteEquiv (n : ℕ) : HeckeLatticeLabels (n + 1) ≃
    {c : Coordinates // c.a * c.d = n + 1} where
  toFun p := ⟨heckeTriangularCoordinates n p,
    (Nat.mul_comm p.1.val.2 p.1.val.1).trans
      (Nat.mem_divisorsAntidiagonal.mp p.1.property).1⟩
  invFun c := ⟨⟨(c.val.d, c.val.a), Nat.mem_divisorsAntidiagonal.mpr
    ⟨(Nat.mul_comm _ _).trans c.property, Nat.succ_ne_zero n⟩⟩, c.val.b⟩
  left_inv p := by rcases p with ⟨⟨⟨a, d⟩, had⟩, b⟩; rfl
  right_inv c := by apply Subtype.ext; apply Coordinates.ext <;> rfl

/-- Each triangular Hecke summand labels one sublattice, and every sublattice occurs once. -/
def heckeLatticeEquiv (n : ℕ) : HeckeLatticeLabels (n + 1) ≃
    {L : Submodule ℤ (Fin 2 → ℤ) // Nat.card ((Fin 2 → ℤ) ⧸ L) = n + 1} :=
  (heckeHermiteEquiv n).trans (latticeEquiv n)

/-- The exact multiplicity of the classical Hecke sum is the divisor sum. -/
theorem card_heckeLatticeLabels (n : ℕ) :
    Nat.card (HeckeLatticeLabels (n + 1)) = ∑ a ∈ (n + 1).divisors, a := by
  rw [Nat.card_congr (heckeLatticeEquiv n), card_sublattices]

/-- The Hecke operator on constants measures its family of integral sublattices. -/
theorem heckeN_one_eq_sublattice_count (n : ℕ) (x y : ℝ) :
    heckeN (n + 1) (fun _ _ => 1) x y =
      (((Real.sqrt (n + 1))⁻¹ : ℝ) : ℂ) *
        (Nat.card {L : Submodule ℤ (Fin 2 → ℤ) //
          Nat.card ((Fin 2 → ℤ) ⧸ L) = n + 1} : ℂ) := by
  rw [← Nat.card_congr (heckeLatticeEquiv n)]
  change heckeN (n + 1) (fun _ _ => 1) x y = _ *
    (Nat.card (Σ ad : {ad : ℕ × ℕ // ad ∈ (n + 1).divisorsAntidiagonal},
      Fin ad.val.2) : ℂ)
  rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Finset.sum_coe_sort (n + 1).divisorsAntidiagonal (fun ad : ℕ × ℕ => ad.2)]
  simp [heckeN, heckeOrbit, Nat.cast_sum]

/-- Every positive-index Hecke operator acts on constants by its normalized divisor sum. -/
theorem heckeN_one_eq_divisor_sum (n : ℕ) (x y : ℝ) :
    heckeN (n + 1) (fun _ _ => 1) x y =
      (((Real.sqrt (n + 1))⁻¹ : ℝ) : ℂ) * (∑ a ∈ (n + 1).divisors, (a : ℂ)) := by
  rw [heckeN_one_eq_sublattice_count, card_sublattices, Nat.cast_sum]

#print axioms heckeLatticeEquiv
#print axioms heckeN_one_eq_sublattice_count
#print axioms heckeN_one_eq_divisor_sum
end GaloisForLFunctions.RenormalizedIntersectionTheory.ResonantStates
