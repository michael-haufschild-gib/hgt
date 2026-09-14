import Mathlib.Tactic.Ring

/-!
# Exact mean-residual update

Lemma 8.8 of the supplied Navier--Stokes paper recomputes the radial mean
residual after adding a mean-velocity correction.  Once the intended linear
term `(2V/R)Δv` is removed, the result is an explicit quadratic remainder.

This file proves equation (8.26) over an arbitrary commutative ring.  Derivative
operators are additive homomorphisms, which is precisely the structure used in
the expansion; no analytic or asymptotic assumptions enter the identity.
-/

namespace GaloisForLFunctions.HTGeometry.NavierStokesMeanResidualUpdate

variable {R : Type*} [CommRing R]

/-- Cylindrical radial divergence `D + e/r`, represented algebraically. -/
def weightedRadialDivergence (D : R →+ R) (weight rInv x : R) : R :=
  D x + weight * rInv * x

/-- Radial quadratic flux in equation (8.3). -/
def radialMeanFlux (b beta Wrr : R) : R :=
  2 * b * beta + beta ^ 2 + Wrr

/-- Axial quadratic flux entering the radial source in equation (8.3). -/
def axialMeanFlux (b G beta gamma Wzr : R) : R :=
  b * gamma + G * beta + beta * gamma + Wzr

/-- Swirl contribution to the radial source in equation (8.3). -/
def swirlMeanFlux (V v WthetaTheta : R) : R :=
  2 * V * v + v ^ 2 + WthetaTheta

/-- Radial-vector-Laplacian contribution in equation (8.3). -/
def radialViscousTerm (lap : R →+ R) (rInv beta : R) : R :=
  lap beta - rInv ^ 2 * beta

/-- Algebraic model of the mean radial source `g_r` in equation (8.3). -/
def meanRadialSource (timeD radialD axialD lap : R →+ R)
    (rInv epsilon b V G beta v gamma Wrr Wzr WthetaTheta : R) : R :=
  -timeD beta -
    weightedRadialDivergence radialD 1 rInv (radialMeanFlux b beta Wrr) -
    axialD (axialMeanFlux b G beta gamma Wzr) +
    rInv * swirlMeanFlux V v WthetaTheta +
    epsilon * radialViscousTerm lap rInv beta

/-- Explicit nonlinear remainder in Lemma 8.8, equation (8.26). -/
def meanRadialUpdateRemainder (timeD radialD axialD lap : R →+ R)
    (rInv epsilon b G beta v gamma deltaBeta deltaV deltaGamma : R) : R :=
  -timeD deltaBeta -
    weightedRadialDivergence radialD 1 rInv
      (2 * b * deltaBeta + 2 * beta * deltaBeta + deltaBeta ^ 2) -
    axialD (b * deltaGamma + G * deltaBeta + beta * deltaGamma +
      gamma * deltaBeta + deltaBeta * deltaGamma) +
    rInv * (2 * v * deltaV + deltaV ^ 2) +
    epsilon * radialViscousTerm lap rInv deltaBeta

theorem radialMeanFlux_add (b beta deltaBeta Wrr : R) :
    radialMeanFlux b (beta + deltaBeta) Wrr =
      radialMeanFlux b beta Wrr +
        (2 * b * deltaBeta + 2 * beta * deltaBeta + deltaBeta ^ 2) := by
  simp [radialMeanFlux]
  ring

theorem axialMeanFlux_add (b G beta gamma deltaBeta deltaGamma Wzr : R) :
    axialMeanFlux b G (beta + deltaBeta) (gamma + deltaGamma) Wzr =
      axialMeanFlux b G beta gamma Wzr +
        (b * deltaGamma + G * deltaBeta + beta * deltaGamma +
          gamma * deltaBeta + deltaBeta * deltaGamma) := by
  simp [axialMeanFlux]
  ring

theorem swirlMeanFlux_add (V v deltaV WthetaTheta : R) :
    swirlMeanFlux V (v + deltaV) WthetaTheta =
      swirlMeanFlux V v WthetaTheta + 2 * V * deltaV +
        (2 * v * deltaV + deltaV ^ 2) := by
  simp [swirlMeanFlux]
  ring

theorem radialViscousTerm_add (lap : R →+ R) (rInv beta deltaBeta : R) :
    radialViscousTerm lap rInv (beta + deltaBeta) =
      radialViscousTerm lap rInv beta + radialViscousTerm lap rInv deltaBeta := by
  simp [radialViscousTerm]
  ring

theorem weightedRadialDivergence_add (D : R →+ R) (weight rInv x y : R) :
    weightedRadialDivergence D weight rInv (x + y) =
      weightedRadialDivergence D weight rInv x +
        weightedRadialDivergence D weight rInv y := by
  simp [weightedRadialDivergence]
  ring

/-- Exact residual recomputation identity (8.26) from Lemma 8.8. -/
theorem meanRadialSource_update
    (timeD radialD axialD lap : R →+ R)
    (rInv epsilon b V G beta v gamma deltaBeta deltaV deltaGamma Wrr Wzr
      WthetaTheta : R) :
    meanRadialSource timeD radialD axialD lap rInv epsilon b V G
        (beta + deltaBeta) (v + deltaV) (gamma + deltaGamma) Wrr Wzr WthetaTheta -
      meanRadialSource timeD radialD axialD lap rInv epsilon b V G
        beta v gamma Wrr Wzr WthetaTheta -
      2 * V * rInv * deltaV =
    meanRadialUpdateRemainder timeD radialD axialD lap rInv epsilon b G
      beta v gamma deltaBeta deltaV deltaGamma := by
  simp only [meanRadialSource, radialMeanFlux_add, axialMeanFlux_add,
    swirlMeanFlux_add, radialViscousTerm_add, weightedRadialDivergence_add,
    map_add, meanRadialUpdateRemainder]
  ring

end GaloisForLFunctions.HTGeometry.NavierStokesMeanResidualUpdate
