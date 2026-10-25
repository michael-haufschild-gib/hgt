# Fixed-determinant cubic amplification and its arithmetic cost

- **ID:** biarithmetic-fixed-determinant-cube-amplification
- **Stage:** 1-in-progress
- **Type:** CANDIDATE (Lean formalization incomplete)
- **Proof status:** Only statements with completed Lean checks and axiom audits are proved. Paper arguments below are proof plans; every significant claim remains a formalization obligation.
- **Parent:** [Biarithmetic Geometry](../1-in-progress/biarithmetic-geometry-foundations.md)
- **Statement:** Audit the natural operation `alpha -> alpha^3/p` on reciprocal genus-one roots of product `p`. It preserves rank and determinant while cubing the normalized roots. Determine exactly when integrality and nonnegative low-degree point counts survive, and test the actual golden roots.

## Source and scope

This addresses the amplification question with an explicit operation and a
precise fixed invariant. Fixed determinant and fixed root count are not a
definition of the analytic conductor of arbitrary rational zeta data. A
result about this operation must not be advertised as the requested general
bounded-conductor no-go.

The corpus query returned ACS's `adamsOp` on scaling cycles and `spanAdams`,
as well as `goldenDatum_pointCount_nonneg`. The scaling-cycle operation is
not the root transformation proposed here; its source definition was read.
The actual golden positivity theorem was also inspected. No matching
fixed-determinant root-cube classification appeared in that query.

## Exact arithmetic classification

Let roots have sum `T` and product a prime `p`. The transformed roots
`alpha^3/p`, `beta^3/p` have product `p` and trace

`U=(T^3-3pT)/p`.

For integral `T,U`, the equation `pU=T^3-3pT` forces `p|T`. Nonnegativity
of the degree-two point counts before and after transformation is exactly
`T^2<=(p+1)^2` and `U^2<=(p+1)^2`. These bounds and `p|T` force
`T in {-p,0,p}`. For `T=+/-p`, the transformed trace is
`U=+/-p(p-3)`, which violates the second bound when `p>=5`. Thus for
prime `p>=5` both integrality and these positivity tests survive exactly at
`T=U=0`. At `p=2,3`, the three traces `-p,0,p` survive; all lie in the
pure range `T^2<=4p`.

For the actual golden datum, `p=5`, `T=5`, so `U=10`. Its transformed
first point count is `6-10=-4`, despite the original datum having all
point counts nonnegative. The normalized cube therefore cannot preserve
the golden positive-count class. The positive survivor is the exact finite
integral/positive trace classification, rather than the bare failure.

## Verification gates

- [x] Corpus-first reuse audit and exact candidate operation specified.
- [x] Dependency-closed proof plan, including small primes and exact source-root identity.
- [x] Lean trace classification and actual golden counterexample.
- [ ] Direct source checks, transitive audits, and umbrella import.

No retirement or formal theorem is claimed yet. In particular, most genuine
curve traces also lose integrality under this normalization: the operation
is not assumed to preserve the finite-field calibration.

## Dependency-closed proof details

Newton's identity is the polynomial equality
`alpha^3+beta^3=(alpha+beta)^3-3alpha*beta*(alpha+beta)`.
Since `alpha*beta=p!=0`, the transformed determinant is
`(alpha*beta)^3/p^2=p` and the trace is the displayed `U`. Dividing
each transformed root by `sqrt(p)` cubes the original normalized root.
For any reciprocal root pair with trace `T`, its degree-two point count is
`p^2+1-(T^2-2p)=(p+1)^2-T^2`, proving the precise positivity dictionary.

The trace equation gives `T^3=p(U+3T)`. Prime divisibility of a power gives
`p|T`, so write `T=pk` with integral `k`. The first positivity test gives
`|pk|<=p+1<2p`, hence `k=-1,0,1`. If `k=0`, cancellation of nonzero `p`
gives `U=0`. If `k=+/-1`, the trace equation gives
`U=+/-p(p-3)`. For `p>=5`, its absolute value is at least `2p>p+1`,
contradicting the second positivity test. The only smaller primes are two
and three. Their nonzero cases are exactly `(T,U)=(2,-2),(-2,2)` and
`(3,0),(-3,0)`, respectively; direct substitution verifies every condition.
This proves both directions of the complete classification and uniqueness
of the transformed integral trace. In every surviving case `T^2<=4p`.

The actual golden roots have sum five and product five, so Newton's identity
gives their cubed sum `125-75=50`. Dividing by five gives trace ten and
the exact first transformed point count minus four. No spectral estimate or
new positivity premise enters this calculation.

The arithmetic classification is implemented in
`BiarithmeticGeometry/NormalizedCubicTrace.lean`. Its scratch check and all
five audits and its direct repository check passed; the umbrella is wired.
The [stage-3 card](../3-formalized/biarithmetic-normalized-cubic-trace.md) records
the exact scope. The inspected
Mathlib interface `Int.Prime.dvd_pow'` supplies the integer divisibility
step. Newton identities and these elementary integral bounds are classical;
no external originality claim is made.

The actual golden source comparison is formalized in
`BiarithmeticGeometry/GoldenNormalizedCube.lean`, with a direct repository
check and four clean transitive audits. Its
[formalized card](../3-formalized/biarithmetic-golden-normalized-cube.md)
records the preserved determinant, trace ten, transformed counts minus four
and minus sixty-four, and comparison with every original point count.
The general integral trace classification also passed its direct repository check.
The complex-root bridge and purity theorem remain pending.

The root-to-trace bridge is drafted in
`/tmp/BiarithmeticNormalizedCubicRootLaw.lean`. Its field identities retain
the determinant, give Newton's exact transformed trace, and show that
dividing by a square-root scale turns the operation into cubing normalized
roots. The real-root specialization identifies the two second point-count
tests with the integer inequalities in `NormalizedCubicTraceCondition`.
The complex-root specialization also records that each second point count
is the corresponding real integer. Thus the classification covers arbitrary
complex reciprocal roots, including the pure nonreal cases, by taking real
parts of the exact integer identity. The root-purity extension below is also
included. Scratch check and all eight transitive audits passed. Production
source is wired; its direct check remains pending.

## Root purity exposed by the trace classification

The square-root trace bound also forces both actual complex roots to have
norm `sqrt(p)`. This is the classical quadratic discriminant criterion,
not an additional purity premise. Write `a=x+iy` and `b=z-iy`, since their
trace is real. Their real product gives `xz+y^2=p`, while its imaginary
part gives `y(z-x)=0`. If `y!=0`, then `z=x`. If `y=0`, the trace bound
gives `(x-z)^2=(x+z)^2-4xz<=0`, again forcing `z=x`. Consequently both
norm squares equal `p`. Applied to the checked integral classification,
every root pair surviving normalized cubing's two positive-count tests is
pure. Corpus searches returned general curve purity machinery but no
matching elementary reciprocal-pair criterion. This strengthened survivor
remains a Lean obligation and must be checked before closing the route.
