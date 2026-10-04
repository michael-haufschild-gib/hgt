# TG C9.19a: universal arithmetic selector contraction

- **Stage:** 5-failed
- **Type:** FALSIFIED candidate, with formalized positive classification
- **Candidate:** realize the prime or prime-power indicator as a bounded
  linear selector on the unchanged TG chronological ground grid, then
  import the jet's exact LCM idempotence as a physical contraction.

## Exact obstruction

For B_n=soninGroundEntry a(log(n+2)), a>0, the physical covariance is
2a/max(i+2,j+2). Adjacent differences have squared norm
2a/((n+2)(n+3)). A binary selector switching at n sends that difference
to B_n or -B_(n+1), forcing n+2 <= norm(T)^2. Both genuine prime and
prime-power masks change arbitrarily late. No bounded selector exists.

## Strongest positive survivor

Bounded selectors exist exactly for eventually constant masks; contractive
selectors exist exactly for constant masks. Explicit continuous duals
recover each original coefficient, and finite-rank perturbations of zero
or identity realize every eventually constant mask. These are statements
on the original physical carrier, not altered diagonal norms.

## New insight and status

Algebraic idempotence of the divisor-transform prime-power mask cannot be
promoted to physical boundedness without an additional mechanism. A proof
for the particular polar-centered arithmetic source must exploit its
signed correlations; the obstruction does not falsify its summability.

Dependency-closed paper proof and Lean formalization COMPLETE in
SoninGroundGridArithmeticSelection. Main statements:
soninGroundGridSelector_bounded_iff,
soninGroundGridSelector_contractive_iff,
soninGroundGrid_primeSelector_unbounded,
soninGroundGrid_primePowerSelector_unbounded.
Final leaf/foundation audits pass; umbrella wired and indexed. Global
lint reports fourteen unrelated unreachable leaves, none in this module.
Positive-survivor card: ../3-formalized/tg-critical-prime-selection.md.
No RH proof, RH falsification or retirement of route TG is claimed.
