import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.Tactic

/-!
# Exact diamond-Ising renormalization algebra

This module records the unconditional rational and polynomial algebra carried by the exact
zero-field Ising decimation on the two-branch, two-bond diamond hierarchical lattice.  In the
physical transmissivity `t = tanh K`, the RG step is

`R(t) = 2 t^2 / (1 + t^4)`.

The external analytic Poincare theorem and Ritt differential-transcendence theorem are deliberately
not represented by hypotheses here.  The formal content is the exact rational map together with
the fixed-point and quotient-rule numerator factorizations used by the paper proof.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

noncomputable section

/-- The exact diamond-Ising RG self-map of the rational function field. -/
def diamondIsingRG : RatFunc ℚ :=
  2 * RatFunc.X ^ 2 / (1 + RatFunc.X ^ 4)

/-- Numerator of the physical transmissivity map before fraction reduction. -/
def diamondIsingRGNumerator : ℚ[X] :=
  2 * X ^ 2

/-- Denominator of the physical transmissivity map before fraction reduction. -/
def diamondIsingRGDenominator : ℚ[X] :=
  1 + X ^ 4

/-- Numerator of `R(X) - X` before division by `1 + X^4`. -/
def diamondIsingRGFixedPointNumerator : ℚ[X] :=
  diamondIsingRGNumerator - X * diamondIsingRGDenominator

/-- **Exact fixed-point factorization.**  Besides the phase anchors `0` and `1`, the
nontrivial thermal fixed point is selected by `X^3 + X^2 + X - 1`. -/
theorem diamondIsingRGFixedPointNumerator_factorization :
    diamondIsingRGFixedPointNumerator =
      -X * (X - 1) * (X ^ 3 + X ^ 2 + X - 1) := by
  simp [diamondIsingRGFixedPointNumerator, diamondIsingRGNumerator,
    diamondIsingRGDenominator]
  ring

/-- Quotient-rule numerator `N' D - N D'` for the exact RG map. -/
def diamondIsingRGDerivativeNumerator : ℚ[X] :=
  derivative diamondIsingRGNumerator * diamondIsingRGDenominator -
    diamondIsingRGNumerator * derivative diamondIsingRGDenominator

/-- **Exact derivative numerator.**  Formally, this is the numerator of
`R'(X) = 4X(1-X^4)/(1+X^4)^2`. -/
theorem diamondIsingRGDerivativeNumerator_eq :
    diamondIsingRGDerivativeNumerator = 4 * X * (1 - X ^ 4) := by
  simp [diamondIsingRGDerivativeNumerator, diamondIsingRGNumerator,
    diamondIsingRGDenominator]
  rw [show (C (3 : ℚ) + 1 : ℚ[X]) = 4 by
    change C (3 : ℚ) + C 1 = C 4
    rw [← map_add]
    norm_num]
  ring

/-- Complete rational critical-numerator factorization over `ℚ`. -/
theorem diamondIsingRGDerivativeNumerator_factorization :
    diamondIsingRGDerivativeNumerator =
      -4 * X * (X - 1) * (X + 1) * (X ^ 2 + 1) := by
  rw [diamondIsingRGDerivativeNumerator_eq]
  ring

end

end GaloisForLFunctions.HTGeometry
