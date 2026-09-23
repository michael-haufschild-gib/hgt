import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Moment arrays of nonnegative weights are positive semidefinite

If `w i >= 0` and every power moment `sum_i w i * (y i)^n` converges, then the Hankel array of
those moments is positive semidefinite: testing it against a coefficient vector `a` collapses
pointwise to `w i * (sum_j a j (y i)^j)^(2 : ℕ)`.

This is the moment side of Hamburger's positivity, in the only form a countable atomic measure
needs, and it is the primitive that lets an arithmetic weight family — one with nonnegative
coefficients, such as von Mangoldt — supply *matrix* positivity rather than the positivity of a
single fixed configuration.
-/

open scoped BigOperators

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {ι : Type*}

/-- The `n`-th power moment of a weighted atomic family. -/
def weightMoment (w y : ι → ℝ) (n : ℕ) : ℝ := ∑' i, w i * y i ^ n

/-- **The moment array of a nonnegative weight family is positive semidefinite.** -/
theorem weightMoment_hankel_nonneg {w y : ι → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hsum : ∀ n : ℕ, Summable (fun i => w i * y i ^ n)) (N : ℕ) (a : ℕ → ℝ) :
    0 ≤ ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N,
      a j * a k * weightMoment w y (j + k) := by
  have hswap : ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N,
      a j * a k * weightMoment w y (j + k) =
      ∑' i, ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N,
        a j * a k * (w i * y i ^ (j + k)) := by
    rw [Summable.tsum_finsetSum (fun j _ => summable_sum fun k _ =>
      ((hsum (j + k)).mul_left (a j * a k)))]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Summable.tsum_finsetSum (fun k _ => ((hsum (j + k)).mul_left (a j * a k)))]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [weightMoment, tsum_mul_left]
  rw [hswap]
  refine tsum_nonneg fun i => ?_
  have hsq : ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N,
      a j * a k * (w i * y i ^ (j + k)) =
      w i * (∑ j ∈ Finset.range N, a j * y i ^ j) ^ (2 : ℕ) := by
    rw [pow_two, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [pow_add]
    ring
  rw [hsq]
  exact mul_nonneg (hw i) (sq_nonneg _)

end GaloisForLFunctions.HTGeometry

end
