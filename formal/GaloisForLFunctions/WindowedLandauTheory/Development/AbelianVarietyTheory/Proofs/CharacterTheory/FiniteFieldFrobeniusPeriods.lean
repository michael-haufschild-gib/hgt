import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! The Frobenius return times of an algebraic element over a finite field. -/

open Polynomial

namespace GlobalTheory.CuspGL

/-- The Frobenius powers fixing an element are exactly the multiples of its minimal-polynomial degree. -/
theorem minpoly_natDegree_dvd_iff_pow {F : Type} [Field F] [Finite F]
    (α : AlgebraicClosure F) (m : ℕ) :
    (minpoly F α).natDegree ∣ m ↔ α ^ Nat.card F ^ m = α := by
  have hα : IsIntegral F α := Algebra.IsIntegral.isIntegral α
  constructor
  · rintro ⟨k, rfl⟩
    let L := IntermediateField.adjoin F {α}
    letI : FiniteDimensional F L := IntermediateField.adjoin.finiteDimensional hα
    letI : Finite L := Module.finite_of_finite F
    letI : Fintype L := Fintype.ofFinite L
    have hcard : Fintype.card L = Nat.card F ^ (minpoly F α).natDegree := by
      rw [Fintype.card_eq_nat_card, Module.natCard_eq_pow_finrank (K := F),
        IntermediateField.adjoin.finrank hα]
    have hfix := congrArg (fun t : L => (t : AlgebraicClosure F))
      (FiniteField.pow_card (IntermediateField.AdjoinSimple.gen F α))
    change α ^ Fintype.card L = α at hfix
    rw [hcard] at hfix
    induction k with
    | zero => simp
    | succ k ih => rw [Nat.mul_succ, pow_add (Nat.card F), pow_mul α, ih, hfix]
  · intro h
    apply (minpoly.irreducible hα).natDegree_dvd_of_dvd_X_pow_card_pow_sub_X
    apply minpoly.dvd F α
    simpa only [map_sub, map_pow, aeval_X, sub_eq_zero] using h

end GlobalTheory.CuspGL
