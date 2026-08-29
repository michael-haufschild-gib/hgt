import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinActualFirstStokesFubini

/-!
# Actual covariant-Hessian seam and exhaustive second Stokes defect

Corpus conjecture C-A.9t4a closes the tensor-normalization seam between the literal actual Maass
legs and the abstract balanced spin-two coefficient.  For the repeated actual completed Poincare
leg `F`, the three orthonormal hyperbolic Hessian components are

```text
A = y^2 F_xx - y F_y,
B = y^2 F_xy + y F_x,
C = y^2 F_yy + y F_y.
```

The literal product `(R_2 R_0 F)(L_(-2) L_0 F)` is `(C-A)^2 + 4 B^2`.  The actual eigen equation
identifies `A+C` with `lambda F`, hence the product is exactly
`2 (A^2 + 2 B^2 + C^2) - lambda^2 F^2`.  Multiplication by the projecting actual Poincare leg
therefore realizes the abstract balanced full-Hessian moment pointwise.  Instantiating the corpus
exhaustive defect identity leaves precisely the actual first and second Stokes defects; C-A.9t3d
has already closed the former after truncation and finite part.

RH chain:

`actual Maass/full-Hessian seam -> sole second Stokes defect -> actual balanced BM ++- coefficient
-> negative BM leg -> conserved left-QNM projection -> HC94 -> RH`.
-/

open Complex Real

namespace RHTower
noncomputable section

/-- Orthonormal horizontal-horizontal covariant Hessian component of the actual Poincare leg. -/
def d4BMActualHyperbolicHessianXX
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) : ℂ :=
  (z.y : ℂ) ^ 2 * d4BMCompletedPoincareHorizontalSecondJet z P -
    (z.y : ℂ) * d4BMCompletedPoincareVerticalFirstJet z P

/-- Orthonormal mixed covariant Hessian component of the actual Poincare leg. -/
def d4BMActualHyperbolicHessianXY
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) : ℂ :=
  (z.y : ℂ) ^ 2 * d4BMCompletedPoincareMixedSecondJet z P +
    (z.y : ℂ) * d4BMCompletedPoincareHorizontalFirstJet z P

/-- Orthonormal vertical-vertical covariant Hessian component of the actual Poincare leg. -/
def d4BMActualHyperbolicHessianYY
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) : ℂ :=
  (z.y : ℂ) ^ 2 * d4BMCompletedPoincareVerticalSecondJet z P +
    (z.y : ℂ) * d4BMCompletedPoincareVerticalFirstJet z P

/-- Actual projecting-leg-weighted full covariant-Hessian density.  The bilinear square, rather
than a Hermitian norm, is the analytic Eisenstein triple-product convention. -/
def d4BMActualSecondStokesHessianDensity
    (z : D4BMUpperHalfPlaneCoordinate)
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) : ℂ :=
  d4BMCompletedEisensteinPoincareSeries z Q *
    (d4BMActualHyperbolicHessianXX z P ^ 2 +
      2 * d4BMActualHyperbolicHessianXY z P ^ 2 +
      d4BMActualHyperbolicHessianYY z P ^ 2)

/-- Literal actual balanced `++-` spin-two source density. -/
def d4BMActualBalancedSpinTwoDensity
    (z : D4BMUpperHalfPlaneCoordinate)
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) : ℂ :=
  d4BMActualCompletedPoincareRaiseLeg z P *
    d4BMActualCompletedPoincareLowerLeg z P *
    d4BMCompletedEisensteinPoincareSeries z Q

/-- Literal actual defect in the second weighted Stokes reduction `H = (d+1) G`. -/
def d4BMActualSecondStokesDefectDensity
    (z : D4BMUpperHalfPlaneCoordinate)
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) : ℂ :=
  d4BMHyperbolicSecondStokesDefect
    (P.s * (P.s - 1)) (Q.s * (Q.s - 1))
    (d4BMActualFirstStokesGradientDensity z P Q)
    (d4BMActualSecondStokesHessianDensity z P Q)

private theorem d4BM_balancedMaass_product_eq_covariantHessian
    (y f fx fy fxx fxy fyy g lambda : ℂ)
    (htrace : y ^ 2 * (fxx + fyy) = lambda * f) :
    (y ^ 2 * (fyy - fxx + 2 * Complex.I * fxy) +
        2 * y * (fy + Complex.I * fx)) *
      (y ^ 2 * (fyy - fxx - 2 * Complex.I * fxy) +
        2 * y * (fy - Complex.I * fx)) * g =
      2 * g *
          ((y ^ 2 * fxx - y * fy) ^ 2 +
            2 * (y ^ 2 * fxy + y * fx) ^ 2 +
            (y ^ 2 * fyy + y * fy) ^ 2) -
        lambda ^ 2 * (f ^ 2 * g) := by
  calc
    _ = ((y ^ 2 * (fyy - fxx) + 2 * y * fy) ^ 2 +
          4 * (y ^ 2 * fxy + y * fx) ^ 2) * g := by
      ring_nf
      simp
      ring
    _ = (2 *
          ((y ^ 2 * fxx - y * fy) ^ 2 +
            2 * (y ^ 2 * fxy + y * fx) ^ 2 +
            (y ^ 2 * fyy + y * fy) ^ 2) -
          (y ^ 2 * (fxx + fyy)) ^ 2) * g := by ring
    _ = 2 * g *
          ((y ^ 2 * fxx - y * fy) ^ 2 +
            2 * (y ^ 2 * fxy + y * fx) ^ 2 +
            (y ^ 2 * fyy + y * fy) ^ 2) -
        lambda ^ 2 * (f ^ 2 * g) := by
      rw [htrace]
      ring

/-- **C-A.9t4a actual Maass/full-Hessian seam.**  The literal actual raised/lowered product is
exactly the abstract balanced full-Hessian density, with the trace term forced by the genuine
Poincare eigen equation. -/
theorem d4BM_actualBalancedSpinTwoDensity_eq_hyperbolicBalancedMoment
    (z : D4BMUpperHalfPlaneCoordinate)
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) :
    d4BMActualBalancedSpinTwoDensity z P Q =
      d4BMHyperbolicBalancedSpinTwoMoment
        (P.s * (P.s - 1))
        (d4BMActualFirstStokesScalarDensity z P Q)
        (d4BMActualSecondStokesHessianDensity z P Q) := by
  have htrace :=
    d4BM_completedEisensteinPoincareSeries_hyperbolicLaplacian_eq_eigenvalue z P
  unfold d4BMActualBalancedSpinTwoDensity
  rw [d4BM_actualCompletedPoincareRaiseLeg_eq,
    d4BM_actualCompletedPoincareLowerLeg_eq]
  unfold d4BMHyperbolicBalancedSpinTwoMoment
    d4BMActualFirstStokesScalarDensity
    d4BMActualSecondStokesHessianDensity
    d4BMActualHyperbolicHessianXX
    d4BMActualHyperbolicHessianXY
    d4BMActualHyperbolicHessianYY
  simpa only [mul_assoc] using
    d4BM_balancedMaass_product_eq_covariantHessian
      (z.y : ℂ)
      (d4BMCompletedEisensteinPoincareSeries z P)
      (d4BMCompletedPoincareHorizontalFirstJet z P)
      (d4BMCompletedPoincareVerticalFirstJet z P)
      (d4BMCompletedPoincareHorizontalSecondJet z P)
      (d4BMCompletedPoincareMixedSecondJet z P)
      (d4BMCompletedPoincareVerticalSecondJet z P)
      (d4BMCompletedEisensteinPoincareSeries z Q)
      (P.s * (P.s - 1)) htrace

/-- **C-A.9t4a exhaustive actual defect decomposition.**  There is no hidden tensor datum or
normalization defect between the actual balanced source and the corpus coefficient.  Its complete
failure is exactly the literal second defect plus the literal first defect already treated by
C-A.9t3. -/
theorem d4BM_actualBalancedSpinTwoDensity_exhaustiveDefectDecomposition
    (z : D4BMUpperHalfPlaneCoordinate)
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) :
    d4BMActualBalancedSpinTwoDensity z P Q -
        d4BMHyperbolicBalancedSpinTwoBochnerCoefficient
          (P.s * (P.s - 1)) (Q.s * (Q.s - 1)) *
          d4BMActualFirstStokesScalarDensity z P Q =
      2 * d4BMActualSecondStokesDefectDensity z P Q +
        2 * (d4BMHyperbolicDiagonalGradientShift
          (P.s * (P.s - 1)) (Q.s * (Q.s - 1)) + 1) *
          d4BMActualFirstStokesDefectDensity z P Q := by
  rw [d4BM_actualBalancedSpinTwoDensity_eq_hyperbolicBalancedMoment]
  simpa only [d4BMActualSecondStokesDefectDensity,
    d4BMActualFirstStokesDefectDensity] using
    d4BMHyperbolicBalancedSpinTwoMoment_defect_decomposition
      (P.s * (P.s - 1)) (Q.s * (Q.s - 1))
      (d4BMActualFirstStokesScalarDensity z P Q)
      (d4BMActualFirstStokesGradientDensity z P Q)
      (d4BMActualSecondStokesHessianDensity z P Q)

end
end RHTower
