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
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

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

/-- **Quadratic weight-grading regroup.** A quadratic form `∑_{i,j} q_{ij}·g(i+j)` whose monomial weight
enters only through `i+j` regroups into `∑_w A_w·g(w)` with `A_w = ∑_{i+j=w} q_{ij}`. With
`g(w) = e^{-(2s+w)z}` (the singular exponent of the quadratic monomial `F_iF_j`, `F_k ~ x^{-s-k}`), this
is the bridge from the relation's quadratic part to the exponent filtration: the distinct weights `w`
give distinct exponents, so each `A_w` is a separable coefficient. -/
theorem quadratic_weight_regroup {N : ℕ} (q : Fin (N + 1) → Fin (N + 1) → ℂ) (g : ℕ → ℂ) :
    (∑ i : Fin (N + 1), ∑ j : Fin (N + 1), q i j * g ((i : ℕ) + (j : ℕ)))
      = ∑ w ∈ Finset.range (2 * N + 1),
          (∑ ij ∈ Finset.univ.filter
              (fun ij : Fin (N + 1) × Fin (N + 1) => (ij.1 : ℕ) + (ij.2 : ℕ) = w),
            q ij.1 ij.2) * g w := by
  rw [← Fintype.sum_prod_type']
  rw [← Finset.sum_fiberwise_of_maps_to (s := (Finset.univ : Finset (Fin (N + 1) × Fin (N + 1))))
      (t := Finset.range (2 * N + 1))
      (g := fun ij : Fin (N + 1) × Fin (N + 1) => (ij.1 : ℕ) + (ij.2 : ℕ))
      (f := fun ij => q ij.1 ij.2 * g ((ij.1 : ℕ) + (ij.2 : ℕ)))
      (fun ij _ => by simp only [Finset.mem_range]; have := ij.1.isLt; have := ij.2.isLt; omega)]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun ij hij => ?_)
  rw [Finset.mem_filter] at hij
  rw [hij.2]

end HurwitzDescent

namespace HurwitzDescent

/-- Shifted cofinite form: if `p` vanishes at `-n + c` for all sufficiently
large natural numbers `n`, then `p = 0`. -/
theorem eq_zero_of_eventually_shifted_neg_nat_roots {p : ℂ[X]} {N : ℕ} (c : ℂ)
    (h : ∀ n, N ≤ n → p.IsRoot (-(n : ℂ) + c)) : p = 0 := by
  apply Polynomial.eq_zero_of_infinite_isRoot
  have hinfN : {n : ℕ | N ≤ n}.Infinite := by
    have hcompl : {n : ℕ | N ≤ n} = (Set.Iio N)ᶜ := by ext n; simp
    rw [hcompl]
    exact (Set.finite_Iio N).infinite_compl
  refine Set.Infinite.mono ?_ (hinfN.image (f := fun n : ℕ => -(n : ℂ) + c) ?_)
  · rintro x ⟨n, hn, rfl⟩
    exact h n hn
  · intro a _ b _ hab
    have hneg : -(a : ℂ) = -(b : ℂ) := add_right_cancel hab
    exact Nat.cast_injective (neg_injective hneg)

end HurwitzDescent
