/-
# Descent algebra: rational coefficients pinned by their values at `a = -n`

The Hurwitz quadratic descent repeatedly argues: a coefficient (a rational function of `a`, cleared to a
polynomial) that vanishes at `a = -n` for infinitely many `n` must be the zero rational function. This
is the algebraic backbone tying the local-orbit obstructions (which hold "for all sufficiently large
`n`") back to identities of the coefficients as rational functions. Pure algebra over `ℂ[X]`, built on
`Polynomial.eq_zero_of_infinite_isRoot`.
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Complex.Basic

open Polynomial

namespace HurwitzDescent

/-- **A polynomial with infinitely many roots among `{-n : n ∈ ℕ}` is zero.** The map `n ↦ -(n:ℂ)` is
injective, so an infinite set of natural numbers `n` with `p(-n) = 0` yields infinitely many roots of
`p`, forcing `p = 0`. This is the "vanishes at infinitely many `a = -n` ⟹ vanishes as a rational
function" step of the descent (after clearing denominators). -/
theorem eq_zero_of_infinitely_many_neg_nat_roots {p : ℂ[X]}
    (h : {n : ℕ | p.IsRoot (-(n : ℂ))}.Infinite) : p = 0 := by
  apply Polynomial.eq_zero_of_infinite_isRoot
  refine Set.Infinite.mono ?_ (h.image (f := fun n : ℕ => -(n : ℂ))
    (neg_injective.comp Nat.cast_injective).injOn)
  rintro x ⟨n, hn, rfl⟩
  exact hn

/-- Cofinite form: if `p` vanishes at `-n` for *all but finitely many* `n` (e.g. "all sufficiently
large `n`"), then `p = 0`. The complement of a finite set in `ℕ` is infinite. -/
theorem eq_zero_of_eventually_neg_nat_roots {p : ℂ[X]} {N : ℕ}
    (h : ∀ n, N ≤ n → p.IsRoot (-(n : ℂ))) : p = 0 := by
  apply eq_zero_of_infinitely_many_neg_nat_roots
  refine Set.Infinite.mono (s := {n : ℕ | N ≤ n}) (fun n hn => h n hn) ?_
  have hcompl : {n : ℕ | N ≤ n} = (Set.Iio N)ᶜ := by ext n; simp
  rw [hcompl]
  exact (Set.finite_Iio N).infinite_compl

end HurwitzDescent
