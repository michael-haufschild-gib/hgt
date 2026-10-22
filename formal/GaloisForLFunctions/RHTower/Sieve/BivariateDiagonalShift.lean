import GaloisForLFunctions.RHTower.Sieve.BivariatePowerSeriesAlgebra

/-!
# Convolution with a diagonal monomial

For bivariate coefficient arrays `f : ℕ → ℕ → ℝ`, the additive (Cauchy) convolution corresponds to
multiplication of the generating series `∑ f(i, j) X^i Y^j`. Convolving with the diagonal monomial
`c X Y` shifts an array one step along the diagonal and scales it by `c`.

## Main results

- `additiveBivariateConvolution_diagonalMonomial_left`: `(c X Y) * f` has coefficients
  `0` if `i = 0` or `j = 0`, and `c f(i - 1, j - 1)` otherwise.
- `additiveBivariateConvolution_diagonalMonomial_right`: the same with the monomial on the right.

## Hypotheses

Both results are unconditional coefficient identities.
-/

open Finset
open scoped BigOperators

namespace RHTower.Sieve

noncomputable section

/-- Coefficient array of the diagonal monomial `c X Y`. -/
def additiveBivariateDiagonalMonomial (c : ℝ) (i j : ℕ) : ℝ :=
  if i = 1 ∧ j = 1 then c else 0

/-- Diagonal shift of an array scaled by `c`: zero on the axes, `c f(i - 1, j - 1)` elsewhere. -/
def additiveBivariateDiagonalShift (c : ℝ) (f : ℕ → ℕ → ℝ) (i j : ℕ) : ℝ :=
  if i = 0 ∨ j = 0 then 0 else c * f (i - 1) (j - 1)

/-- Convolving with the diagonal monomial `c X Y` on the left is the scaled diagonal shift. -/
theorem additiveBivariateConvolution_diagonalMonomial_left
    (c : ℝ) (f : ℕ → ℕ → ℝ) :
    additiveBivariateConvolution (additiveBivariateDiagonalMonomial c) f =
      additiveBivariateDiagonalShift c f := by
  funext i j
  rw [additiveBivariateConvolution, additiveBivariateDiagonalShift]
  by_cases hi : i = 0
  · subst i
    simp [additiveBivariateDiagonalMonomial]
  by_cases hj : j = 0
  · subst j
    simp [additiveBivariateDiagonalMonomial]
  rw [if_neg (not_or_intro hi hj), Finset.sum_eq_single 1]
  · rw [Finset.sum_eq_single 1]
    · simp [additiveBivariateDiagonalMonomial]
    · intro b hb hb1
      simp [additiveBivariateDiagonalMonomial, hb1]
    · intro hnot
      exact (hnot (Finset.mem_range.mpr (by omega))).elim
  · intro a ha ha1
    apply Finset.sum_eq_zero
    intro b hb
    simp [additiveBivariateDiagonalMonomial, ha1]
  · intro hnot
    exact (hnot (Finset.mem_range.mpr (by omega))).elim

/-- Convolving with the diagonal monomial `c X Y` on the right is the scaled diagonal shift. -/
theorem additiveBivariateConvolution_diagonalMonomial_right
    (c : ℝ) (f : ℕ → ℕ → ℝ) :
    additiveBivariateConvolution f (additiveBivariateDiagonalMonomial c) =
      additiveBivariateDiagonalShift c f := by
  rw [additiveBivariateConvolution_comm,
    additiveBivariateConvolution_diagonalMonomial_left]

end

end RHTower.Sieve
