import GaloisForLFunctions.RHTower.Sieve.DifferentiatedBarbanVehovIncludedOriginalForms
import GaloisForLFunctions.RHTower.Sieve.SelbergMinLogMonomial

/-!
# Ordinary/minimum-log forms for the included detector boundary

The included endpoint is expanded exactly into the ordinary complementary logarithms and their
minimum.  Generic ordinary-log monomials complement the existing minimum-log API, while symmetry
reduces the three included boundary forms to a small reusable family.
-/

open ArithmeticFunction Finset
open scoped BigOperators ArithmeticFunction.Moebius

namespace RHTower.Sieve

noncomputable section

/-- Original Möbius/gcd Selberg form with arbitrary complementary logarithmic powers. -/
def selbergOriginalLogMonomial (i j N : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N),
    let A := Real.log ((N : ℝ) / (p.1 : ℝ))
    let B := Real.log ((N : ℝ) / (p.2 : ℝ))
    selbergOriginalCoeff p.1 p.2 * (A ^ i * B ^ j)

/-- Swapping the two logarithmic powers leaves the ordinary form unchanged. -/
theorem selbergOriginalLogMonomial_comm (i j N : ℕ) :
    selbergOriginalLogMonomial i j N = selbergOriginalLogMonomial j i N := by
  rw [selbergOriginalLogMonomial, selbergOriginalLogMonomial,
    Finset.sum_product, Finset.sum_product, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  dsimp only
  rw [show selbergOriginalCoeff n m = selbergOriginalCoeff m n by
    rw [selbergOriginalCoeff, selbergOriginalCoeff, Nat.gcd_comm]
    ring]
  ring

/-- The generic `(1,1)` form is the existing logarithmic quadratic form. -/
theorem selbergOriginalLogMonomial_one_one_eq (N : ℕ) :
    selbergOriginalLogMonomial 1 1 N = selbergOriginalLogQuadratic N := by
  simp [selbergOriginalLogMonomial, selbergOriginalLogQuadratic,
    Finset.sum_product]

/-- The generic `(1,2)` form is the existing mixed logarithmic form. -/
theorem selbergOriginalLogMonomial_one_two_eq (N : ℕ) :
    selbergOriginalLogMonomial 1 2 N = selbergOriginalLogOneTwo N := by
  simp [selbergOriginalLogMonomial, selbergOriginalLogOneTwo,
    Finset.sum_product]

/-- The generic `(2,2)` form is the existing quadratic-log form. -/
theorem selbergOriginalLogMonomial_two_two_eq (N : ℕ) :
    selbergOriginalLogMonomial 2 2 N = selbergOriginalLogTwoTwo N := by
  simp [selbergOriginalLogMonomial, selbergOriginalLogTwoTwo,
    Finset.sum_product]

/-- Included base boundary as ordinary and minimum-log monomials. -/
theorem selbergOriginalIncludedBaseBoundary_eq_logMonomials
    (M : ℕ) :
    selbergOriginalIncludedBaseBoundary M =
      Real.log M * selbergOriginalLogMonomial 1 1 M -
        2 * selbergOriginalLogMonomial 1 2 M +
          selbergOriginalMinLogMonomial 1 1 1 M := by
  rw [show 2 * selbergOriginalLogMonomial 1 2 M =
      selbergOriginalLogMonomial 1 2 M +
        selbergOriginalLogMonomial 2 1 M by
    rw [selbergOriginalLogMonomial_comm 1 2 M]
    ring]
  rw [selbergOriginalIncludedBaseBoundary,
    selbergOriginalLogMonomial, selbergOriginalLogMonomial,
    selbergOriginalLogMonomial,
    selbergOriginalMinLogMonomial]
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  ring

private theorem selbergOriginalIncludedCrossBoundary_eq_logMonomials_raw
    (ell : ℝ) (M : ℕ) :
    selbergOriginalIncludedCrossBoundary ell M =
      -(ell * Real.log M - Real.log M ^ (2 : ℕ) / 2) *
          selbergOriginalLogMonomial 1 1 M +
        (ell - Real.log M) * selbergOriginalLogMonomial 2 1 M +
        (ell - Real.log M) * selbergOriginalLogMonomial 1 2 M -
        (1 / 2 : ℝ) * selbergOriginalLogMonomial 3 1 M +
        Real.log M * selbergOriginalLogMonomial 2 1 M +
        (1 / 2 : ℝ) * selbergOriginalLogMonomial 1 3 M -
        ell * selbergOriginalMinLogMonomial 1 1 1 M -
        (1 / 2 : ℝ) * selbergOriginalMinLogMonomial 1 1 2 M +
        selbergOriginalMinLogMonomial 2 1 1 M := by
  simp only [selbergOriginalIncludedCrossBoundary,
    selbergOriginalLogMonomial, selbergOriginalMinLogMonomial]
  simp_rw [Finset.mul_sum]
  repeat
    first
    | rw [← Finset.sum_add_distrib]
    | rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  ring

/-- Included base/derivative boundary as ordinary and minimum-log monomials. -/
theorem selbergOriginalIncludedCrossBoundary_eq_logMonomials
    (ell : ℝ) (M : ℕ) :
    selbergOriginalIncludedCrossBoundary ell M =
      -(ell * Real.log M - Real.log M ^ (2 : ℕ) / 2) *
          selbergOriginalLogMonomial 1 1 M +
        (2 * ell - Real.log M) * selbergOriginalLogMonomial 1 2 M -
        ell * selbergOriginalMinLogMonomial 1 1 1 M -
        (1 / 2 : ℝ) * selbergOriginalMinLogMonomial 1 1 2 M +
        selbergOriginalMinLogMonomial 2 1 1 M := by
  rw [selbergOriginalIncludedCrossBoundary_eq_logMonomials_raw,
    selbergOriginalLogMonomial_comm 2 1 M,
    selbergOriginalLogMonomial_comm 3 1 M]
  ring

private theorem selbergOriginalIncludedDerivativeBoundary_eq_logMonomials_raw
    (ell : ℝ) (M : ℕ) :
    selbergOriginalIncludedDerivativeBoundary ell M =
      (Real.log M * ell ^ (2 : ℕ) - ell * Real.log M ^ (2 : ℕ) + Real.log M ^ (3 : ℕ) / 3) *
          selbergOriginalLogMonomial 1 1 M -
        (ell ^ (2 : ℕ) - ell * Real.log M + Real.log M ^ (2 : ℕ) / 2) *
          selbergOriginalLogMonomial 2 1 M -
        (ell ^ (2 : ℕ) - ell * Real.log M + Real.log M ^ (2 : ℕ) / 2) *
          selbergOriginalLogMonomial 1 2 M +
        (1 / 6 : ℝ) * selbergOriginalLogMonomial 4 1 M +
        (1 / 6 : ℝ) * selbergOriginalLogMonomial 1 4 M -
        (1 / 2 : ℝ) * selbergOriginalLogMonomial 3 2 M -
        (1 / 2 : ℝ) * selbergOriginalLogMonomial 2 3 M +
        Real.log M * selbergOriginalLogMonomial 2 2 M +
        ell ^ (2 : ℕ) * selbergOriginalMinLogMonomial 1 1 1 M +
        ell * selbergOriginalMinLogMonomial 1 1 2 M +
        (1 / 3 : ℝ) * selbergOriginalMinLogMonomial 1 1 3 M -
        ell * selbergOriginalMinLogMonomial 2 1 1 M -
        ell * selbergOriginalMinLogMonomial 1 2 1 M -
        (1 / 2 : ℝ) * selbergOriginalMinLogMonomial 2 1 2 M -
        (1 / 2 : ℝ) * selbergOriginalMinLogMonomial 1 2 2 M +
        selbergOriginalMinLogMonomial 2 2 1 M := by
  simp only [selbergOriginalIncludedDerivativeBoundary,
    selbergOriginalLogMonomial, selbergOriginalMinLogMonomial]
  simp_rw [Finset.mul_sum]
  repeat
    first
    | rw [← Finset.sum_add_distrib]
    | rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  ring

/-- Included derivative-square boundary as ordinary and minimum-log monomials. -/
theorem selbergOriginalIncludedDerivativeBoundary_eq_logMonomials
    (ell : ℝ) (M : ℕ) :
    selbergOriginalIncludedDerivativeBoundary ell M =
      (Real.log M * ell ^ (2 : ℕ) - ell * Real.log M ^ (2 : ℕ) + Real.log M ^ (3 : ℕ) / 3) *
          selbergOriginalLogMonomial 1 1 M -
        2 * (ell ^ (2 : ℕ) - ell * Real.log M + Real.log M ^ (2 : ℕ) / 2) *
          selbergOriginalLogMonomial 1 2 M +
        (1 / 3 : ℝ) * selbergOriginalLogMonomial 1 4 M -
        selbergOriginalLogMonomial 2 3 M +
        Real.log M * selbergOriginalLogMonomial 2 2 M +
        ell ^ (2 : ℕ) * selbergOriginalMinLogMonomial 1 1 1 M +
        ell * selbergOriginalMinLogMonomial 1 1 2 M +
        (1 / 3 : ℝ) * selbergOriginalMinLogMonomial 1 1 3 M -
        2 * ell * selbergOriginalMinLogMonomial 2 1 1 M -
        selbergOriginalMinLogMonomial 2 1 2 M +
        selbergOriginalMinLogMonomial 2 2 1 M := by
  rw [selbergOriginalIncludedDerivativeBoundary_eq_logMonomials_raw,
    selbergOriginalLogMonomial_comm 2 1 M,
    selbergOriginalLogMonomial_comm 4 1 M,
    selbergOriginalLogMonomial_comm 3 2 M,
    selbergOriginalMinLogMonomial_comm 1 2 1 M,
    selbergOriginalMinLogMonomial_comm 1 2 2 M]
  ring

end

end RHTower.Sieve
