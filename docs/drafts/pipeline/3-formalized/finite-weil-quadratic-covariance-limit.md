# Finite Weil quadratic covariance limit

Status: formalized; seven new theorems across four leaves, native and axiom audits passed (2026-10-12).

## Objective and corpus evidence

Compute the limiting covariance of arbitrary quadratic observables under actual
finite subcritical Weil tilts, and classify the directions whose variance tends
to zero. This complements the exact finite common-kernel result; it does not
identify the finite kernel with the limiting kernel.

Only local Lean sources are used. The scoped quadratic/variance/limit search
returned five existing coordinate-variance bounds, not this observable covariance
formula. Two polynomial/moment convergence hits concern compact one-dimensional
carriers. Existing WeilLogShiftQuadraticTiltMoments gives every mixed monomial
limit. TiltedHeatSaddleGaussian.gaussMoment_four_eq supplies the exact unnormalized
fourth Gaussian moment. The broad Gaussian/fourth query was exploratory, not an
exhaustive novelty audit.

The final declaration-uniqueness audit found the exact quadratic mean theorem
already in WeilLogShiftQuadraticTiltEntropyLimit. Its proof is reused directly;
the duplicate mean declaration was removed from this increment.

## Dependency-closed paper proof

Write s=a+2*b+d<2, v=1/(4-2*s), and H=h+2*j+l for Q(h,j,l).

1. At frequency zero, gaussMoment is the complex embedding of the real Gaussian
   monomial integral. Taking real parts of gaussMoment_four_eq gives its fourth
   moment ratio. Multiply by the Gaussian density's normalization, whose integral
   is one, at precision 1/(2*v). Thus the centered Gaussian fourth moment is 3*v^2.
   At variance zero the measure is Dirac at zero, giving the same formula.
2. Finite sums of existing mixed-monomial limits give every binary homogeneous
   polynomial moment: for degree n and coefficients c_i, the limit is
   (sum c_i)*E[X^n]. Every finite integrability requirement is discharged by the
   actual finite-law theorem.
3. The existing quadratic mean theorem gives E[Q(h,j,l)] tending to H*v.
   The product with Q(H0,J0,L0) is homogeneous of degree four with
   coefficient sum H*(H0+2*J0+L0), hence has mean limit 3*v^2 times that sum.
4. Covariance is the product moment minus the product of means, so its limit is
   2*H*(H0+2*J0+L0)/(4-2*s)^2. The variance limit is 2*H^2/(4-2*s)^2.
5. Since the denominator is positive in the existing subcritical parameter
   domain, variance tends to zero iff H=0. This is an exact limiting kernel
   classification for all quadratic observable coefficients.

## Plan

1. Native API audit and probability-normalized Gaussian fourth moment.
2. Actual homogeneous moment transfer, quadratic product moments, and reuse of
   the existing quadratic mean theorem.
3. Actual covariance, variance, and zero-limit equivalence.
4. Sequential leaf builds, umbrella wiring, full owned axiom/dependency/index
   audits, whitespace, and one repository lint snapshot.

## Working verification log

- Fifteen local Mathlib API references passed natively. The current finite-sum
  convergence API is tendsto_finsetSum; the old snake-case alias is deprecated.
- GaussianProbabilityFourthMoment passed with an empty native log after removing
  one unnecessary tactic sequencing warning.
- WeilLogShiftHomogeneousTiltMoments passed with an empty native log.
- Quadratic product moments, covariance, variance, and the exact zero-limit
  criterion passed with empty native logs, including the final rebuilds after
  deduplicating the mean theorem.
- The finite-index specializations require explicit Nat casts in exponents
  such as 4-(i:Nat); otherwise numeral subtraction is inferred in Fin. This
  elaboration issue was corrected before rebuilding the observable-moment leaf.
- Final audit imported WeilLogShiftQuadraticCovarianceLimit using
  `lake --old env lean /tmp/hgt-weil-quadratic-covariance-final-audit.lean`.
  All seven new declarations use only propext, Classical.choice, and Quot.sound;
  fifteen API checks passed without residual diagnostics.
- Metadata audit verified four fresh native objects, empty leaf logs, eight
  direct import edges, seven incoming imports, unique declaration names, and one
  umbrella import per new leaf. No umbrella or full build was run.
- Scoped local index audit recovered all seven declarations with full coverage,
  no partial results, no markers, and empty stderr. New Lean files and umbrella
  changes passed whitespace checks.
- Final repository lint snapshot: six errors outside this increment and 367
  size warnings. The errors were unreachable modules CCMPolarOddPrimeJumps,
  PaperWoldHardyDefect, PaperWoldHardyMaskedTransport, PaperWoldHardyQuotient,
  HurwitzZetaEulerMaclaurinBridge, and QKrawtchoukCompanionTriangular. No owned
  declaration or import error was reported. Global lint is not claimed clean.

## Formalized declarations

- GaussianProbabilityFourthMoment: gaussMoment_zero_eq_ofReal_integral and
  gaussianZero_integral_fourth.
- WeilLogShiftHomogeneousTiltMoments:
  tendsto_finiteWeilCanonicalJointQuadraticTilt_homogeneous_moment.
- WeilLogShiftQuadraticObservableMoments:
  tendsto_finiteWeilCanonicalJointQuadraticTilt_quadratic_product_moment.
- WeilLogShiftQuadraticCovarianceLimit:
  tendsto_finiteWeilCanonicalJointQuadraticTilt_quadratic_covariance,
  tendsto_finiteWeilCanonicalJointQuadraticTilt_quadratic_variance, and
  tendsto_finiteWeilCanonicalJointQuadraticTilt_quadratic_variance_zero_iff.

## Boundary

No rate of convergence or prescribed replication schedule is asserted. The
limiting quadratic covariance has rank-one form in coefficient directions;
the exact finite kernel can still be smaller. Canonical depths and subcritical
base tilt domains are retained from the proved mixed-moment theorem.
All finite integrability and L2 assumptions are discharged on the actual laws.
The subsequent finite-weil-polynomial-variance-kernel increment extends moment,
covariance, and variance convergence to every fixed bivariate polynomial. Its
exact zero-variance-limit criterion is P(x,x)=P(0,0) for every real x, independent
of subcritical tilt parameters and canonical schedules.
The corpus-wide research goal remains active.
