import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheGhostRingOfTheArithmeticSquare
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# Möbius coordinates of integral ghosts

The divisor transform occurring in Zehavi's character formula, Theorem 4.7
of arXiv:2611.18218, recovers the corpus's necklace coordinates exactly.
For every integral ghost the Möbius numerator is divisible by its index;
the division therefore preserves integrality without an extra premise.
-/

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open Finset ArithmeticFunction

/-- Möbius inversion makes the recursively defined necklace coordinates explicit. -/
theorem ghost_necklace_moebius (x : ghostRing) (n : ℕ+) :
    ((n : ℕ) : ℤ) * necklace (toNat x.val) n =
      ∑ d ∈ (n : ℕ).divisors, moebius ((n : ℕ) / d) * toNat x.val d := by
  have h := (sum_eq_iff_sum_mul_moebius_eq
    (f := fun d => (d : ℤ) * necklace (toNat x.val) d)
    (g := toNat x.val)).mp
      (fun m hm => (x.property.eq_sum_necklace m (Nat.ne_of_gt hm)).symm) n n.pos
  rw [Nat.sum_divisorsAntidiagonal' (fun i j => (moebius i : ℤ) * toNat x.val j)] at h
  exact h.symm

/-- Dwork congruences discharge the divisibility needed by the character-style formula. -/
theorem ghost_moebius_numerator_dvd (x : ghostRing) (n : ℕ+) :
    ((n : ℕ) : ℤ) ∣
      ∑ d ∈ (n : ℕ).divisors, moebius ((n : ℕ) / d) * toNat x.val d :=
  ⟨necklace (toNat x.val) n, (ghost_necklace_moebius x n).symm⟩

/-- The explicit divisor average is integral and equals the existing necklace coordinate. -/
theorem ghost_necklace_eq_moebius_div (x : ghostRing) (n : ℕ+) :
    necklace (toNat x.val) n =
      (∑ d ∈ (n : ℕ).divisors, moebius ((n : ℕ) / d) * toNat x.val d) / n := by
  rw [← ghost_necklace_moebius, Int.mul_ediv_cancel_left]
  exact_mod_cast n.ne_zero

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ

#print axioms GaloisForLFunctions.AbsoluteGeometryOfSpecZ.ghost_necklace_moebius
#print axioms GaloisForLFunctions.AbsoluteGeometryOfSpecZ.ghost_moebius_numerator_dvd
#print axioms GaloisForLFunctions.AbsoluteGeometryOfSpecZ.ghost_necklace_eq_moebius_div
