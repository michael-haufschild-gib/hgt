# Finite Weil observables as a polynomial quotient

Status: formalized and audited (2026-10-12); repository lint has three unrelated errors.

## Objective and local evidence

Classify actual finite polynomial observables by the support's nodal polynomial,
then prove that every real observable has a unique representative of degree at
most `r` in the first coordinate. All finite `r k`, all real tilt coefficients,
and all observables are in scope. Mathematical evidence is local Lean only.

The existing exact power-covariance kernel identifies constant power sums on
the `r+1` support nodes. `WeilLogShiftJointTransportGeometry` proves first-node
coordinate injectivity; `WeilLogShiftTiltVarianceKernel` characterizes arbitrary
almost-everywhere predicates and zero variance by their support values.

Scoped indexed polynomial/variance search returned six complete hits, all
previous asymptotic binary-polynomial variance results. Source search found
existing interpolation pairings in `WeilLogShiftMomentBarycentric` and
`WeilLogShiftCanonicalCluster`; both statements concern top coefficients and
moment-dual pairings, not almost-everywhere representatives of arbitrary actual
law observables. No finite quotient classification was found in these sources.

The expanded indexed query `interpolation interpolant --any`, scoped to
`WeilLogShift`, returned 23 declarations across two pages; all 23 statement
headers were inspected. The additional results concern arbitrary first-probe
histories, coefficient perturbations, and paired-kernel finite reconstruction.
They do not supply the actual finite-law polynomial quotient or representative.

Reuse `Lagrange.nodal`, not a new equivalent nodal definition. The local
`LinearPartialFractions.prod_X_sub_C_dvd_of_isRoot` supplies divisibility from
distinct roots. Installed Lean interpolation provides existence and uniqueness
below the support cardinality.

## Dependency-closed paper proof

Write `x_i` for the first coordinates of the actual support and
`N(X) = ∏ i, (X - x_i)`. The nodes are distinct, and `N` is monic, nonzero,
and degree `r+1`. A polynomial vanishes at every node iff `N` divides it:
each distinct linear factor divides it, the factors are pairwise coprime,
and divisibility implies vanishing by evaluation.

Therefore `p(x_i)=q(x_i)` for every node iff `N | p-q`, equivalently their
remainders modulo `N` agree. The finite law assigns positive mass to every
node for every real tilt, so these are also exactly the almost-everywhere
equalities of the corresponding observables. A polynomial has zero variance
iff it is constant on the support, equivalently
`p = C(p(x_0)) + N*q` for one unique polynomial `q`; uniqueness follows by
cancellation of nonzero `N`. Applied to a power-sum polynomial, this classifies
every covariance null vector algebraically.

For any observable `f`, interpolate the `r+1` values `f(point_i)` on the
distinct nodes `x_i`. Lagrange interpolation gives degree below `r+1` and
agreement on the full support. Almost-everywhere agreement follows from the
existing exact support theorem. Any other polynomial of that degree with the
same almost-everywhere values agrees at all nodes and equals the interpolant.
The explicit representative depends on support values, not tilt coefficients.

## Plan and working log

1. Verify nodal, remainder, cancellation, and interpolation APIs natively.
2. Prove finite-node vanishing/divisibility, remainder, and unique-factor lemmas.
3. Prove actual finite-law quotient, variance, and covariance-kernel roots.
4. Prove explicit interpolation characterization and unique representation for
   every real observable.
5. Sequential native builds, complete axiom/declaration/index audits, umbrella
   wiring, whitespace checks, and one repository lint snapshot.

## Native verification

Thirteen theorems are implemented in `HTGeometry/FiniteNodePolynomialIdeal`
(five), `RHTower/WeilLogShiftFinitePolynomialQuotient` (five), and
`RHTower/WeilLogShiftFinitePolynomialInterpolation` (three). Every leaf built
natively with an empty diagnostic log. Nineteen APIs and two concrete API
examples passed. Full index coverage is 13/13. Metadata verified all three
fresh objects, 5 project edges, 7 total imports, 5 incoming imports, unique
declarations, umbrella wiring, and clean whitespace. The final native scratch
audit imports the actual interpolation root and passed with all 13 axiom
reports restricted to `propext`, `Classical.choice`, and `Quot.sound`, all 19
API checks, both concrete API examples, and no residual diagnostics. All owned
native processes are terminal. Artifacts use prefix
`/tmp/hgt-weil-finite-polynomial-ideal-`.

The one repository lint snapshot reports 367 warnings and three unrelated
unreachable modules: `RHTower.JointAncestryRealAmplitudeCapstone`,
`RHTower.JointAncestryRealAmplitudeDetection`, and
`RHTower.Zeta23TheoremASpectralSlack`. No new leaf has a lint error.

No web searches, external papers, or numerical experiments were used.

## Boundary

These are finite-law equalities, not pointwise identities on the ambient plane.
The degree bound grows with `r`; no uniform-degree asymptotic representation or
new Gaussian-limit interchange follows. This does not identify kernels across
different depths or provide determinant/eigenvalue estimates.
