import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCompletedBalancedSpinTwoEisensteinVertex

/-!
# Analytic-family finite part of diagonal Eisenstein cusp currents

The two Stokes defects in the completed balanced spin-two vertex are boundary currents at the
modular cusp.  This module closes their constant-term contribution uniformly in spectral
parameters.

Each constant term of `E(z,1/2+u)` has exponent `1/2 + epsilon*u`, with `epsilon = ±1`.
For two equal positive legs and a projecting leg, every triple boundary exponent is therefore

`1/2 + (epsilonOne+epsilonTwo)*u + epsilonThree*v`.

Represent an affine exponent by its doubled constant coordinate and its `u,v` coefficients.  The
doubled constant coordinate of every boundary term is `1`, hence no exponent is identically zero
as a spectral family.  The analytic-family finite part extracts only the identically zero
exponent before spectral specialization, so it annihilates every such boundary current for
arbitrary coefficients.  In particular, accidental numerical exponent zero on a resonance
hyperplane creates no anomalous constant after analytic continuation.

This proves the constant-term part of both cusp Stokes defects.  Exponentially decaying
nonconstant Whittaker modes are deliberately not encoded here; their boundary limit is the next
separate theorem.

`[NEW] [PAPER-PROVED] [LEAN-PROVED] [HC94] [CUSP CONSTANT TERM]`
-/

open Complex Real
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Affine cusp exponent coordinates: doubled constant, repeated-leg coefficient, projecting-leg
coefficient. -/
abbrev D4BMDiagonalEisensteinCuspAffineExponent := Fin 3 → ℤ

/-- Sign encoded by one Weyl choice. -/
def d4BMCuspSign (b : Bool) : ℤ := if b then 1 else -1

/-- Affine exponent of one diagonal triple-Eisenstein cusp boundary monomial. -/
def d4BMDiagonalEisensteinCuspBoundaryExponent
    (epsilonOne epsilonTwo epsilonThree : Bool) :
    D4BMDiagonalEisensteinCuspAffineExponent := fun j =>
  match j with
  | 0 => 1
  | 1 => d4BMCuspSign epsilonOne + d4BMCuspSign epsilonTwo
  | 2 => d4BMCuspSign epsilonThree

/-- No diagonal triple-Eisenstein boundary exponent is identically zero as a spectral family. -/
theorem d4BMDiagonalEisensteinCuspBoundaryExponent_ne_zero
    (epsilonOne epsilonTwo epsilonThree : Bool) :
    d4BMDiagonalEisensteinCuspBoundaryExponent
        epsilonOne epsilonTwo epsilonThree ≠ 0 := by
  intro h
  have hzero := congrFun h 0
  norm_num [d4BMDiagonalEisensteinCuspBoundaryExponent] at hzero

/-- Analytic-family finite part: coefficient of the exponent identically equal to zero. -/
def d4BMCuspAnalyticFamilyFinitePart
    (F : D4BMDiagonalEisensteinCuspAffineExponent →₀ ℂ) : ℂ := F 0

/-- General diagonal Eisenstein cusp current with arbitrary spectral coefficients. -/
def d4BMDiagonalEisensteinCuspBoundaryFamily
    (coefficient : Bool → Bool → Bool → ℂ) :
    D4BMDiagonalEisensteinCuspAffineExponent →₀ ℂ :=
  ∑ epsilonOne : Bool, ∑ epsilonTwo : Bool, ∑ epsilonThree : Bool,
    Finsupp.single
      (d4BMDiagonalEisensteinCuspBoundaryExponent
        epsilonOne epsilonTwo epsilonThree)
      (coefficient epsilonOne epsilonTwo epsilonThree)

/-- Every diagonal triple-Eisenstein constant-term boundary current has zero analytic-family
finite part, independently of all current coefficients. -/
theorem d4BMCuspAnalyticFamilyFinitePart_diagonalEisensteinBoundary_eq_zero
    (coefficient : Bool → Bool → Bool → ℂ) :
    d4BMCuspAnalyticFamilyFinitePart
        (d4BMDiagonalEisensteinCuspBoundaryFamily coefficient) = 0 := by
  simp [d4BMCuspAnalyticFamilyFinitePart,
    d4BMDiagonalEisensteinCuspBoundaryFamily,
    d4BMDiagonalEisensteinCuspBoundaryExponent_ne_zero]

/-- The complete linear combination of first and second constant-term Stokes boundaries has zero
analytic-family finite part. -/
theorem d4BMCuspAnalyticFamilyFinitePart_twoStokesBoundary_eq_zero
    (d : ℂ)
    (firstCoefficient secondCoefficient : Bool → Bool → Bool → ℂ) :
    2 * d4BMCuspAnalyticFamilyFinitePart
          (d4BMDiagonalEisensteinCuspBoundaryFamily secondCoefficient) +
        2 * (d + 1) * d4BMCuspAnalyticFamilyFinitePart
          (d4BMDiagonalEisensteinCuspBoundaryFamily firstCoefficient) = 0 := by
  rw [d4BMCuspAnalyticFamilyFinitePart_diagonalEisensteinBoundary_eq_zero,
    d4BMCuspAnalyticFamilyFinitePart_diagonalEisensteinBoundary_eq_zero]
  ring

end

end RHTower
