# Exact finite Weil power-covariance threshold

Status: formalized and audited (2026-10-12); repository lint has one unrelated error.

## Formal result and verification

For every finite size `r`, depth `k`, real tilt coefficients `a b d`, and power
count `n`, the actual first-coordinate power covariance matrix is positive
definite iff `n ≤ r`. Its determinant is positive iff `n ≤ r`, and zero iff
`r < n`. Consequently, for fixed `n`, determinants are eventually positive for
arbitrary depth sequences and arbitrary real coefficient sequences. There are
no canonical-depth or subcriticality assumptions in these finite results.

Eleven theorems are formalized across four leaves:

- `HTGeometry/FinitePowerSumNodes.lean`: two finite-node statements.
- `HTGeometry/PowerCovarianceKernel.lean`: covariance null-vector and determinant lemmas.
- `RHTower/WeilLogShiftFinitePowerCovariance.lean`: three actual finite-law results.
- `RHTower/WeilLogShiftFinitePowerThreshold.lean`: three exact classifications and the arbitrary-sequence consequence.

All four native leaf builds have empty diagnostic logs and fresh objects. Final
scratch audit imports the actual root and verifies all 11 axiom reports plus
20 checked APIs; only `propext`, `Classical.choice`, and `Quot.sound` occur.
Every declaration is indexed with full scoped coverage: 2 + 2 + 3 + 4. Umbrella
wiring, declaration uniqueness, all 6 direct project dependency edges, 12 total
imports, 7 incoming imports, and whitespace were checked. Audit artifacts use
the prefix `/tmp/hgt-weil-finite-power-rank-`.

The final `scripts/formal_tools.py lint` snapshot reports 367 warnings and one
unrelated error: `RHTower.JointAncestryRealAmplitudeDetection` is unreachable
from its theorem-area umbrella. No new leaf has a lint error.

Evidence was confined to the local Lean corpus. No web searches, external
papers, or numerical experiments were used.

## Objective and local evidence

For every finite r,k and every real quadratic tilt, classify the covariance
matrix of first-coordinate powers z0,...,z0^n: positive definite and positive
determinant exactly when n<=r; determinant zero exactly when r<n. Remove the
canonical-depth and subcriticality restrictions from the positivity result.

Only local Lean sources are used. WeilLogShiftJointProbabilityLaw defines the
support using Fin(r+1). WeilLogShiftJointTransportGeometry proves that the first
coordinate is injective on this carrier. WeilLogShiftTiltVarianceKernel gives
L2 for every real observable and zero variance iff all support values agree,
for every finite depth and all real tilt coefficients. PowerCovarianceMatrix
supplies its quadratic-form identity. A scoped power/covariance search recovered
only the three previous Gaussian-limit roots; the broader finite/support/rank
search had two unrelated results. All returned statements were inspected.

## Dependency-closed paper proof

1. On r+1 distinct real nodes, a power sum of degree at most n<=r which is
   constant on the nodes is a constant polynomial. Polynomial interpolation
   from more nodes than its degree proves this. Its positive-degree coefficients
   must all vanish.
2. If r<n, the linear map from n coefficients to the r differences between node
   values and the value at node zero has a nontrivial kernel, by finite dimension.
   Thus a nonzero coefficient vector gives a power sum constant on all r+1 nodes.
   This direction does not require node injectivity.
3. For a probability law and square-integrable powers, an almost-everywhere
   constant power sum gives a null vector of the power covariance matrix:
   each matrix-vector coordinate is covariance with that sum, hence zero.
   A nonzero null vector forces determinant zero.
4. Apply step 1 to the actual injective first-coordinate nodes. Exact finite
   variance rigidity and the quadratic-form identity give positive definiteness
   for n<=r. Apply step 2, actual support equivalence, and step 3 for r<n.
5. The two cases yield exact iff statements for positive definiteness, positive
   determinant, and zero determinant. They also give eventual determinant
   positivity with explicit threshold r>=n for arbitrary depth schedules and
   arbitrary real tilt coefficient sequences.

## Plan and working log

1. Audit APIs; prove the two finite-node power-sum statements.
2. Prove the covariance null-vector and determinant-zero transfer.
3. Prove actual finite positive and singular cases, then the exact threshold and
   unrestricted eventual corollary.
4. Sequential native builds, umbrella wiring, complete declaration/axiom/index
   audits, whitespace checks, and one final lint snapshot.

## Boundary

The claim is an exact determinant/positive-definiteness threshold, not yet a
formal rank=min(n,r) theorem or an explicit determinant formula. The previous
Gaussian determinant limit retains its own subcritical canonical-depth domain.
The corpus-wide research goal remains active.
