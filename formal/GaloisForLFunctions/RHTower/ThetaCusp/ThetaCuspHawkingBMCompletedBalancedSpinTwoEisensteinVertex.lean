import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMPlebanskiMaassSecondJetBridge
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingEKGCompletedEisensteinOpticalIncidence

/-!
# Stokes-completed balanced spin-two Eisenstein vertex

The BM-pulled Plebanski source selects the diagonal Maass word
`(R_2 R_0 f) (L_(-2) L_0 f)`.  Its modular-weight `(4,-4,0)` projection can be reduced to the
scalar triple vertex by two weighted Bochner/Stokes steps.  This module determines the exact
spectral polynomial and, crucially, records every possible failure of that reduction.

For geometric Laplacian eigenvalues `lambda` on the repeated positive leg and `mu` on the
projecting leg, set

`d = mu/2 - lambda`.

If `V`, `G`, and `H` denote scalar, gradient, and full-Hessian moments, the balanced traceless
spin moment is `2 H - lambda^(2 : ℕ) V`.  Lean proves the unconditional defect decomposition

```text
(2 H - lambda^(2 : ℕ) V) - (2 d (d+1) - lambda^(2 : ℕ)) V
  = 2 (H-(d+1)G) + 2(d+1)(G-dV).
```

Thus the two explicit Stokes defects are exhaustive: there is no third hidden tensor datum in
the diagonal spin channel.  Applying the canonical zero-defect completion to the existing
completed scalar triple-Eisenstein vertex gives the coefficient

`2 d(d+1) - lambda^(2 : ℕ)`,

with `lambda = u^(2 : ℕ)-1/4` and `mu = v^(2 : ℕ)-1/4`.  The completed polarized vertex retains both
Eisenstein Weyl reflections.  Proving that the analytic cusp regularization realizes this
zero-defect completion remains a separate boundary theorem; it is not assumed here.

`[NEW] [PAPER-PROVED] [LEAN-PROVED] [HC94] [EXACT STOKES DEFECT]`
-/

open Complex Real

namespace RHTower

noncomputable section

/-- Geometric-sign hyperbolic Laplacian eigenvalue of `E(z,1/2+u)`. -/
def thetaCuspHawkingEisensteinGeometricEigenvalue (u : ℂ) : ℂ :=
  u ^ (2 : ℕ) - 1 / 4

/-- First weighted integration-by-parts coefficient. -/
def d4BMHyperbolicDiagonalGradientShift (lambda mu : ℂ) : ℂ :=
  mu / 2 - lambda

/-- Exact balanced traceless-Hessian coefficient after two zero-defect Stokes steps. -/
def d4BMHyperbolicBalancedSpinTwoBochnerCoefficient (lambda mu : ℂ) : ℂ :=
  let d := d4BMHyperbolicDiagonalGradientShift lambda mu
  2 * d * (d + 1) - lambda ^ (2 : ℕ)

/-- Defect in the first weighted Stokes reduction `G = d V`. -/
def d4BMHyperbolicFirstStokesDefect
    (lambda mu scalarMoment gradientMoment : ℂ) : ℂ :=
  gradientMoment -
    d4BMHyperbolicDiagonalGradientShift lambda mu * scalarMoment

/-- Defect in the second weighted Stokes reduction `H = (d+1) G`. -/
def d4BMHyperbolicSecondStokesDefect
    (lambda mu gradientMoment hessianMoment : ℂ) : ℂ :=
  hessianMoment -
    (d4BMHyperbolicDiagonalGradientShift lambda mu + 1) * gradientMoment

/-- Balanced spin-two moment in terms of scalar and full-Hessian moments. -/
def d4BMHyperbolicBalancedSpinTwoMoment
    (lambda scalarMoment hessianMoment : ℂ) : ℂ :=
  2 * hessianMoment - lambda ^ (2 : ℕ) * scalarMoment

/-- Exact exhaustive decomposition of failure of scalar-vertex reduction into two Stokes defects.
No vanishing or boundary assumption occurs in this identity. -/
theorem d4BMHyperbolicBalancedSpinTwoMoment_defect_decomposition
    (lambda mu scalarMoment gradientMoment hessianMoment : ℂ) :
    d4BMHyperbolicBalancedSpinTwoMoment lambda scalarMoment hessianMoment -
        d4BMHyperbolicBalancedSpinTwoBochnerCoefficient lambda mu * scalarMoment =
      2 * d4BMHyperbolicSecondStokesDefect lambda mu gradientMoment hessianMoment +
        2 * (d4BMHyperbolicDiagonalGradientShift lambda mu + 1) *
          d4BMHyperbolicFirstStokesDefect lambda mu scalarMoment gradientMoment := by
  simp [d4BMHyperbolicBalancedSpinTwoMoment,
    d4BMHyperbolicBalancedSpinTwoBochnerCoefficient,
    d4BMHyperbolicFirstStokesDefect, d4BMHyperbolicSecondStokesDefect,
    d4BMHyperbolicDiagonalGradientShift]
  ring

/-- Existing completed scalar triple vertex on two equal positive legs. -/
def thetaCuspHawkingDiagonalCompletedEisensteinCubicVertex (u v : ℂ) : ℂ :=
  thetaCuspHawkingCompletedEisensteinCubicVertex u u v

/-- First Stokes shift in Eisenstein spectral coordinates. -/
def thetaCuspHawkingDiagonalEisensteinGradientShift (u v : ℂ) : ℂ :=
  d4BMHyperbolicDiagonalGradientShift
    (thetaCuspHawkingEisensteinGeometricEigenvalue u)
    (thetaCuspHawkingEisensteinGeometricEigenvalue v)

/-- Balanced spin-two coefficient in Eisenstein spectral coordinates. -/
def thetaCuspHawkingBalancedSpinTwoBochnerCoefficient (u v : ℂ) : ℂ :=
  d4BMHyperbolicBalancedSpinTwoBochnerCoefficient
    (thetaCuspHawkingEisensteinGeometricEigenvalue u)
    (thetaCuspHawkingEisensteinGeometricEigenvalue v)

/-- Canonical first zero-defect Stokes completion of the diagonal gradient vertex. -/
def thetaCuspHawkingStokesCompletedDiagonalGradientVertex (u v : ℂ) : ℂ :=
  thetaCuspHawkingDiagonalEisensteinGradientShift u v *
    thetaCuspHawkingDiagonalCompletedEisensteinCubicVertex u v

/-- Canonical second zero-defect Stokes completion of the diagonal full-Hessian vertex. -/
def thetaCuspHawkingStokesCompletedDiagonalHessianVertex (u v : ℂ) : ℂ :=
  (thetaCuspHawkingDiagonalEisensteinGradientShift u v + 1) *
    thetaCuspHawkingStokesCompletedDiagonalGradientVertex u v

/-- Canonical Stokes-completed balanced spin-two Eisenstein vertex. -/
def thetaCuspHawkingCompletedBalancedSpinTwoEisensteinVertex (u v : ℂ) : ℂ :=
  2 * thetaCuspHawkingStokesCompletedDiagonalHessianVertex u v -
    thetaCuspHawkingEisensteinGeometricEigenvalue u ^ (2 : ℕ) *
      thetaCuspHawkingDiagonalCompletedEisensteinCubicVertex u v

/-- Exact completed coefficient: the balanced spin-two vertex is a fixed spectral polynomial
times the existing completed scalar vertex. -/
theorem thetaCuspHawkingCompletedBalancedSpinTwoEisensteinVertex_eq
    (u v : ℂ) :
    thetaCuspHawkingCompletedBalancedSpinTwoEisensteinVertex u v =
      thetaCuspHawkingBalancedSpinTwoBochnerCoefficient u v *
        thetaCuspHawkingDiagonalCompletedEisensteinCubicVertex u v := by
  simp [thetaCuspHawkingCompletedBalancedSpinTwoEisensteinVertex,
    thetaCuspHawkingStokesCompletedDiagonalHessianVertex,
    thetaCuspHawkingStokesCompletedDiagonalGradientVertex,
    thetaCuspHawkingBalancedSpinTwoBochnerCoefficient,
    thetaCuspHawkingDiagonalEisensteinGradientShift,
    d4BMHyperbolicBalancedSpinTwoBochnerCoefficient,
    d4BMHyperbolicDiagonalGradientShift]
  ring

/-- Coefficient is even in the repeated positive-leg parameter. -/
theorem thetaCuspHawkingBalancedSpinTwoBochnerCoefficient_neg_left
    (u v : ℂ) :
    thetaCuspHawkingBalancedSpinTwoBochnerCoefficient (-u) v =
      thetaCuspHawkingBalancedSpinTwoBochnerCoefficient u v := by
  simp [thetaCuspHawkingBalancedSpinTwoBochnerCoefficient,
    thetaCuspHawkingEisensteinGeometricEigenvalue,
    d4BMHyperbolicBalancedSpinTwoBochnerCoefficient,
    d4BMHyperbolicDiagonalGradientShift]

/-- Coefficient is even in the projecting-leg parameter. -/
theorem thetaCuspHawkingBalancedSpinTwoBochnerCoefficient_neg_right
    (u v : ℂ) :
    thetaCuspHawkingBalancedSpinTwoBochnerCoefficient u (-v) =
      thetaCuspHawkingBalancedSpinTwoBochnerCoefficient u v := by
  simp [thetaCuspHawkingBalancedSpinTwoBochnerCoefficient,
    thetaCuspHawkingEisensteinGeometricEigenvalue,
    d4BMHyperbolicBalancedSpinTwoBochnerCoefficient,
    d4BMHyperbolicDiagonalGradientShift]

/-- The diagonal completed scalar vertex is even in its repeated parameter. -/
theorem thetaCuspHawkingDiagonalCompletedEisensteinCubicVertex_neg_left
    (u v : ℂ) :
    thetaCuspHawkingDiagonalCompletedEisensteinCubicVertex (-u) v =
      thetaCuspHawkingDiagonalCompletedEisensteinCubicVertex u v := by
  simp only [thetaCuspHawkingDiagonalCompletedEisensteinCubicVertex]
  rw [thetaCuspHawkingCompletedEisensteinCubicVertex_neg_one,
    thetaCuspHawkingCompletedEisensteinCubicVertex_neg_two]

/-- The completed polarized vertex preserves repeated-leg Weyl reflection. -/
theorem thetaCuspHawkingCompletedBalancedSpinTwoEisensteinVertex_neg_left
    (u v : ℂ) :
    thetaCuspHawkingCompletedBalancedSpinTwoEisensteinVertex (-u) v =
      thetaCuspHawkingCompletedBalancedSpinTwoEisensteinVertex u v := by
  rw [thetaCuspHawkingCompletedBalancedSpinTwoEisensteinVertex_eq,
    thetaCuspHawkingCompletedBalancedSpinTwoEisensteinVertex_eq,
    thetaCuspHawkingBalancedSpinTwoBochnerCoefficient_neg_left,
    thetaCuspHawkingDiagonalCompletedEisensteinCubicVertex_neg_left]

/-- The completed polarized vertex preserves projecting-leg Weyl reflection. -/
theorem thetaCuspHawkingCompletedBalancedSpinTwoEisensteinVertex_neg_right
    (u v : ℂ) :
    thetaCuspHawkingCompletedBalancedSpinTwoEisensteinVertex u (-v) =
      thetaCuspHawkingCompletedBalancedSpinTwoEisensteinVertex u v := by
  rw [thetaCuspHawkingCompletedBalancedSpinTwoEisensteinVertex_eq,
    thetaCuspHawkingCompletedBalancedSpinTwoEisensteinVertex_eq,
    thetaCuspHawkingBalancedSpinTwoBochnerCoefficient_neg_right]
  simp [thetaCuspHawkingDiagonalCompletedEisensteinCubicVertex,
    thetaCuspHawkingCompletedEisensteinCubicVertex_neg_three]

/-- Four-factor Xi factorization specialized to two equal positive legs. -/
theorem thetaCuspHawkingDiagonalCompletedEisensteinCubicVertex_factorization
    (u v : ℂ) :
    thetaCuspHawkingDiagonalCompletedEisensteinCubicVertex u v =
      thetaCuspHawkingCompletedEisensteinXiFactor (2 * u + v) *
        thetaCuspHawkingCompletedEisensteinXiFactor v ^ (2 : ℕ) *
        thetaCuspHawkingCompletedEisensteinXiFactor (2 * u - v) := by
  simp [thetaCuspHawkingDiagonalCompletedEisensteinCubicVertex,
    thetaCuspHawkingCompletedEisensteinCubicVertex]
  rw [thetaCuspHawkingCompletedEisensteinXiFactor_neg]
  ring

end

end RHTower
