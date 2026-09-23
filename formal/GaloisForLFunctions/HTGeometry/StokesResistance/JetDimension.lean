import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Order
import Mathlib.Tactic.Ring

/-!
# Stokes-jet and reciprocal-response dimensions

This module formalizes the dimension identities in Moreau,
*The Stokes resistance of an arbitrary particle: a classification of hydrodynamic symmetries*,
arXiv:2608.23907v1, Appendix A.

The order is shifted from the paper's `k ≥ 3` to `k = n + 3`. This makes every theorem
unconditional. The first two harmonic jet sectors have dimensions `3` and `8`; every later sector
has dimension `6q + 3`. Their partial sum is quadratic. Reciprocity identifies response operators
with symmetric bilinear forms, giving `choose (D + 1) 2` raw parameters and hence quartic growth.
Removing hydrodynamic-centre and adapted-frame coordinates subtracts exactly six parameters.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry.StokesResistance

/-- Dimension of the `q`-th incompressible harmonic Stokes-jet sector. -/
def harmonicJetSectorDimension : ℕ → ℕ
  | 0 => 3
  | 1 => 8
  | q + 2 => 6 * q + 15

@[simp] theorem harmonicJetSectorDimension_zero : harmonicJetSectorDimension 0 = 3 := rfl

@[simp] theorem harmonicJetSectorDimension_one : harmonicJetSectorDimension 1 = 8 := rfl

/-- Moreau's `dim H_q = 6q + 3`, shifted to the unconditional index `q + 2`. -/
@[simp] theorem harmonicJetSectorDimension_add_two (q : ℕ) :
    harmonicJetSectorDimension (q + 2) = 6 * q + 15 := by
  rw [harmonicJetSectorDimension]

/-- Retained jet dimension at paper order `k = n + 3`. -/
def jetDimension (n : ℕ) : ℕ :=
  ∑ q ∈ Finset.range (n + 2), harmonicJetSectorDimension q

/-- Moreau Appendix A: `D_k = 3k² - 6k + 2`, with `k = n + 3`. -/
theorem jetDimension_eq (n : ℕ) :
    jetDimension n = 3 * n ^ (2 : ℕ) + 12 * n + 11 := by
  induction n with
  | zero => norm_num [jetDimension, harmonicJetSectorDimension, Finset.sum_range_succ]
  | succ n ih =>
      rw [jetDimension, show n + 1 + 2 = (n + 2) + 1 by omega,
        Finset.sum_range_succ, ← jetDimension, ih]
      rw [harmonicJetSectorDimension_add_two]
      ring

/-- Raw reciprocal-response parameter count: symmetric bilinear forms on the retained jet. -/
def rawResistanceParameterCount (n : ℕ) : ℕ :=
  Nat.choose (jetDimension n + 1) 2

/-- Moreau's quartic raw-dimension formula, shifted to `k = n + 3`. -/
theorem rawResistanceParameterCount_eq (n : ℕ) :
    rawResistanceParameterCount n =
      (9 * n ^ (4 : ℕ) + 72 * n ^ (3 : ℕ) + 213 * n ^ (2 : ℕ) + 276 * n + 132) / 2 := by
  rw [rawResistanceParameterCount, Nat.choose_two_right, jetDimension_eq]
  rw [show 3 * n ^ (2 : ℕ) + 12 * n + 11 + 1 - 1 = 3 * n ^ (2 : ℕ) + 12 * n + 11 by omega]
  congr 1
  ring

/-- Reduced response count after three origin and three adapted-frame coordinates are removed. -/
def reducedResistanceParameterCount (n : ℕ) : ℕ :=
  rawResistanceParameterCount n - 6

/-- Every retained jet has enough raw coordinates for the six-coordinate reduction. -/
theorem six_le_rawResistanceParameterCount (n : ℕ) :
    6 ≤ rawResistanceParameterCount n := by
  rw [rawResistanceParameterCount_eq]
  apply le_trans (show 6 ≤ 132 / 2 by norm_num)
  apply Nat.div_le_div_right
  omega

/-- Moreau's reduction removes exactly six parameters, without truncated subtraction. -/
theorem reducedResistanceParameterCount_add_six (n : ℕ) :
    reducedResistanceParameterCount n + 6 = rawResistanceParameterCount n := by
  have h := six_le_rawResistanceParameterCount n
  rw [reducedResistanceParameterCount]
  omega

end GaloisForLFunctions.HTGeometry.StokesResistance
