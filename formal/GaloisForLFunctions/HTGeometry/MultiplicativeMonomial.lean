import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Polynomial.Splits

/-!
# Multiplicative polynomials are monomials

Over an algebraically closed field, a nonzero polynomial `P` that is multiplicative,
`P(xy) = P(x) P(y)`, is a power of the indeterminate: `P = X^n`.

This is the polynomial (positive-charge) case of the classification of algebraic characters of the
multiplicative group `G_m`: the eigenvalue `χ(λ)` of a diagonalized `PGL₂`-cocharacter is `λ^k`.
It is the arithmetic heart of step §3 of the clock-character law.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open Polynomial

/-- **Multiplicative polynomials are monomials.**  Over an algebraically closed field a nonzero
polynomial with `P(xy) = P(x) P(y)` equals `X ^ (deg P)`. -/
theorem multiplicative_polynomial_eq_X_pow {C : Type*} [Field C] [IsAlgClosed C]
    {P : Polynomial C} (hP : P ≠ 0)
    (hmul : ∀ x y : C, P.eval (x * y) = P.eval x * P.eval y) :
    P = Polynomial.X ^ P.natDegree := by
  -- `P(1) = 1`
  have hev1 : P.eval 1 = 1 := by
    have h := hmul 1 1
    rw [mul_one] at h
    have hsq : P.eval 1 * (P.eval 1 - 1) = 0 := by rw [mul_sub, mul_one]; linear_combination -h
    rcases mul_eq_zero.mp hsq with h0 | h0
    · exact absurd (Polynomial.zero_of_eval_zero P (fun x => by
        have := hmul 1 x; rwa [one_mul, h0, zero_mul] at this)) hP
    · exact sub_eq_zero.mp h0
  -- every root of `P` is zero
  have hnr : ∀ r ∈ P.roots, r = 0 := by
    intro r hr'
    by_contra hr0
    have hev : P.eval r = 0 := Polynomial.isRoot_of_mem_roots hr'
    exact hP (Polynomial.zero_of_eval_zero P (fun t => by
      have hh := hmul r (r⁻¹ * t)
      rwa [mul_inv_cancel_left₀ hr0, hev, zero_mul] at hh))
  -- `P` splits and its roots are all `0`, so `P = C (lead) · X ^ n`
  have hsplit : P.Splits := IsAlgClosed.splits P
  have hprod := hsplit.eq_prod_roots
  have hmapeq : (P.roots.map (fun x => X - Polynomial.C x))
      = Multiset.replicate P.roots.card X := by
    rw [show (P.roots.map (fun x => X - Polynomial.C x))
        = P.roots.map (fun _ => (X : Polynomial C)) from
      Multiset.map_congr rfl (fun r hr' => by rw [hnr r hr']; simp)]
    exact Multiset.map_const' _ _
  rw [hmapeq, Multiset.prod_replicate] at hprod
  have hcard : P.roots.card = P.natDegree :=
    (Polynomial.splits_iff_card_roots.mp hsplit)
  rw [hcard] at hprod
  -- the leading coefficient is `1`
  have hlead : P.leadingCoeff = 1 := by
    have he : P.eval 1 = P.leadingCoeff := by rw [hprod]; simp
    rw [hev1] at he; exact he.symm
  rw [hlead, map_one, one_mul] at hprod
  exact hprod

end GaloisForLFunctions.HTGeometry
