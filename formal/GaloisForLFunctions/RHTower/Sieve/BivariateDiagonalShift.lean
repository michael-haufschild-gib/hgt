import GaloisForLFunctions.RHTower.Sieve.BivariatePowerSeriesAlgebra

open Finset
open scoped BigOperators

namespace RHTower.Sieve

noncomputable section

def additiveBivariateDiagonalMonomial (c : ℝ) (i j : ℕ) : ℝ :=
  if i = 1 ∧ j = 1 then c else 0

def additiveBivariateDiagonalShift (c : ℝ) (f : ℕ → ℕ → ℝ) (i j : ℕ) : ℝ :=
  if i = 0 ∨ j = 0 then 0 else c * f (i - 1) (j - 1)

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

theorem additiveBivariateConvolution_diagonalMonomial_right
    (c : ℝ) (f : ℕ → ℕ → ℝ) :
    additiveBivariateConvolution f (additiveBivariateDiagonalMonomial c) =
      additiveBivariateDiagonalShift c f := by
  rw [additiveBivariateConvolution_comm,
    additiveBivariateConvolution_diagonalMonomial_left]

end

end RHTower.Sieve
