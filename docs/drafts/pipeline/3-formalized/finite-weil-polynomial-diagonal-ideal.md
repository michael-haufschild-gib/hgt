# Finite Weil polynomial diagonal ideal

Status: formalized; eight new theorems across three leaves, native and axiom audits passed (2026-10-12).

## Objective and corpus evidence

Replace the infinite pointwise criterion for vanishing limiting variance by an
exact divisibility test and unique quotient. All mathematical evidence comes
from local Lean sources.

WeilLogShiftPolynomialVarianceKernel proves that actual variance tends to zero
iff P(x,x)=P(0,0) for every real x. Installed Mathlib supplies multivariate
polynomial induction, renaming, evaluation under renaming, and extensionality
over infinite integral domains. The direct polynomial/diagonal/divisibility
query returned no entries. The broadened diagonal/polynomial query was
exploratory (161 eligible entries, first 20 returned), not a novelty audit.
Exact source searches and final declaration-uniqueness checks cover new symbols.

## Dependency-closed paper proof

Let D=X0-X1 and let R(P) rename both variables to X1.

1. D divides P-R(P) for every P. Polynomial induction proves this for constants
   and sums. For multiplication by Xi, use
   P*Xi-R(P)*X1 = (P-R(P))*Xi + R(P)*(Xi-X1).
   The last difference is D or zero because i is in Fin 2.
2. P vanishes on the real diagonal iff R(P)=0: evaluation under renaming gives
   the forward implication by multivariate extensionality, and the reverse
   follows by evaluation. Step 1 then implies D divides P. Conversely a multiple
   of D evaluates to zero on the diagonal.
3. Apply step 2 to P-C(P(0,0)). Constancy of the diagonal restriction is exactly
   divisibility of this centered polynomial by D.
4. Step 1 gives P=R(P)+D*Q. D is nonzero since X0 and X1 are distinct, and the
   polynomial ring is an integral domain, so cancellation proves Q unique.
   If the diagonal restriction is constant, extensionality gives R(P)=C(P(0,0)).
   Hence centered divisibility has a unique quotient as well.
5. Compose step 3 and the unique-quotient result with the actual variance-kernel
   theorem. This yields exact algebraic criteria for the finite-law variance
   limit, with all analytic assumptions already discharged. In particular every
   diagonal defect P-R(P) has variance tending to zero.

## Plan and working log

1. Audit installed algebra APIs; prove diagonal divisibility in one helper leaf.
2. Prove the unique diagonal remainder/quotient normal form in a second leaf.
3. Transfer divisibility and unique-factor criteria to actual Weil variance.
4. Sequential native leaf builds, umbrella wiring, complete new declaration
   axiom/import/index audits, whitespace, and one final lint snapshot.

- Nineteen installed Mathlib API references and the concrete `Infinite ℝ`
  instance passed natively with an empty log.
- The first divisibility build exposed one missing dependency: Real.Basic does
  not itself provide the `Infinite ℝ` instance. Importing
  Mathlib.Algebra.CharZero.Infinite supplies it. The corrected leaf passed with
  an empty native log.
- The unique diagonal normal form and constant-diagonal unique-factor criterion
  passed natively with an empty log.
- All three leaves are written. No mathematical conjecture was weakened.
- The actual divisibility criterion, unique-factor criterion, and diagonal-defect
  variance limit passed natively with an empty log.
- Final audit imported WeilLogShiftPolynomialVarianceIdeal using
  `lake --old env lean /tmp/hgt-weil-polynomial-diagonal-ideal-final-audit.lean`.
  All eight axiom reports use only propext, Classical.choice, and Quot.sound;
  nineteen API references and the concrete infinite-real instance passed, with
  no residual diagnostics.
- Metadata audit verified three fresh native objects and empty logs, three direct
  project import edges (eight imports including Mathlib), five incoming imports,
  fresh direct project dependencies, unique names, and exactly one umbrella
  import per leaf. New Lean files and both umbrella changes passed whitespace
  checks. No umbrella or full build was run.
- Scoped local index audit recovered all eight declarations with full coverage,
  no partial results or markers, and empty stderr.
- Final repository lint snapshot: five errors outside this increment and 367
  large-file warnings. Unreachable modules: PaperWoldCompositeApproach,
  PaperWoldCompositeDamping, PaperWoldCompositeParameter,
  WeilConeXiDivisibleBlindTest, and XiSliceKKLScaleOffLineDetection. No error
  concerns this increment. Global lint is not claimed clean.
- Audit artifacts use the prefix `/tmp/hgt-weil-polynomial-diagonal-ideal`.

## Formalized declarations

- HTGeometry/BinaryPolynomialDiagonalDivision:
  binaryPolynomial_sub_rename_diagonal_dvd,
  binaryPolynomial_diagonal_zero_iff_dvd,
  binaryPolynomial_diagonal_constant_iff_dvd.
- HTGeometry/BinaryPolynomialDiagonalNormalForm:
  binaryPolynomial_existsUnique_diagonal_quotient,
  binaryPolynomial_diagonal_constant_iff_existsUnique.
- RHTower/WeilLogShiftPolynomialVarianceIdeal:
  tendsto_finiteWeilCanonicalJointQuadraticTilt_polynomial_variance_zero_iff_dvd,
  tendsto_finiteWeilCanonicalJointQuadraticTilt_polynomial_variance_zero_iff_unique_factor,
  tendsto_finiteWeilCanonicalJointQuadraticTilt_polynomial_diagonal_defect_variance_zero.

## Boundary

This identifies constants plus the principal ideal generated by X0-X1 as the
limiting variance kernel. It does not identify a finite-depth kernel, supply a
convergence rate, or prove a dimension formula for bounded-degree quotients.
The subsequent finite-weil-polynomial-covariance-rank increment proves positive
Gaussian covariance matrices for every fixed list of first n positive powers,
and eventual positivity of their actual Weil covariance determinants.
Actual-law statements retain canonical depths 2*(r+1)^2+t(r) and the subcritical
base domain a+2*b+d<2. Algebraic normal forms hold for every real bivariate
polynomial independently of those parameters.
The corpus-wide research goal remains active.
