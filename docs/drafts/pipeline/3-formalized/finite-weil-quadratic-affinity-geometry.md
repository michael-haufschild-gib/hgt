# Finite Weil quadratic affinity geometry

Status: formalized and natively audited (2026-10-12).

## Scope and local evidence

Use only local Lean mathematical sources. No web, external papers, or numerical experiments.
The existing likelihood moment theorem at order -1/2 gives the actual square-root
Radon–Nikodym overlap. `HTGeometry.HellingerAffinityFactorization` supplies the
arbitrary-measure Bhattacharyya affinity and its finite-product factorization.
The quadratic tilt entropy increment gives the limiting symmetric KL divergence.
Local lexical overlap search: 6 hits in 4 WeilLogShift modules, including the two
actual overlap declarations; no partial-result markers. Gaussian/affinity/variance
conjunctive query returned no declarations. Existing affinity factorization is reused.

## Conjecture and dependency-closed paper proof

For subcritical diagonal coefficients s=a+2b+d and S=A+2B+D, put x=2-s>0,
y=2-S>0. The square-root overlap limit is
H = sqrt(2 sqrt(x*y)/(x+y)).

1. Raise the existing order -1/2 likelihood limit to the fourth power. The
   exponential factor contributes y/x, the squared response contributes
   4*x^2/(x+y)^2. Thus H^4=4*x*y/(x+y)^2; positivity identifies the fourth root.
2. (x-y)^2 >= 0 proves 0<H<=1; equality holds exactly when x=y, equivalently s=S.
3. Use P+Q as common dominating measure. The corpus RN quotient identity
   gives dQ/dP=(dQ/d(P+Q))/(dP/d(P+Q)), P-almost everywhere. On points where
   p=dP/d(P+Q) is positive, sqrt(p*q)=sqrt(q/p)*p; at p=0 both weighted
   expressions vanish. Change of measure identifies the actual real overlap
   without assuming Q is absolutely continuous with respect to P.
   Finite measures already ensure square-root RN integrability:
   sqrt(u) <= 1+u, and the corpus proves real RN derivatives integrable. Thus
   the generic bridge needs neither a separate integrability premise nor an
   absolute-continuity premise.
4. Fixed n independent copies have affinity H^n in the limit, by existing
   product factorization and continuity. If s differs from S, H<1. Choose a
   constant between H and 1; eventually the actual affinity is bounded by that
   constant. Geometric squeeze proves affinity of r copies tends to zero.
5. The existing symmetric KL limit J=(s-S)^2/(2*x*y) obeys H^4*(1+J/2)=1,
   by clearing positive denominators. Continuity transfers this relation to
   actual finite-law affinities and symmetric KL values.

This increment alone does not classify growing products when s=S. The later
[adaptive replication increment](finite-weil-quadratic-adaptive-replication.md)
proves existence of a monotone diverging stable schedule; prescribed growth
rates remain a distinct research question.

## Formalized modules

- `HTGeometry/PositivePrecisionOverlap.lean`: one definition and six theorems;
  positive precision kernel, fourth-power formula, sharp bounds and equality
  classification, exact symmetric-divergence relation.
- `HTGeometry/BhattacharyyaRealOverlap.lean`: three theorems; square-root RN
  integrability and exact real-overlap bridge for arbitrary finite measures
  (including singular pairs), plus varying geometric decay.
- `RHTower/WeilLogShiftQuadraticAffinityGeometry.lean`: one definition and five
  theorems; subcritical diagonal parameters, bounds and exact classification.
- `RHTower/WeilLogShiftQuadraticAffinityLimit.lean`: six theorems; old likelihood
  finite-branch identity, actual finite-law affinity identities, both real and
  extended-real limits, and affinity tending to one iff diagonal parameters agree.
- `RHTower/WeilLogShiftQuadraticAffinityProducts.lean`: three theorems; fixed
  products, r-copy separation for distinct diagonals, and the actual finite-law
  affinity/symmetric-KL limit relation.

Actual roots take arbitrary depth remainder t and subcritical coefficient-domain
elements; every analytic assumption in generic limit helpers is discharged.
No new axioms, admitted proofs, or heartbeat increases.

## Verification log

- All five final leaves: foreground `lake --old env lean ... -o ...`, native
  exit 0, empty logs, fresh emitted objects. One owned Lean process at a time.
- Native `/tmp/hgt-weil-affinity-final-audit.lean`: exit 0; 40 API checks and
  all 25 declaration axiom reports. Only `propext`, `Classical.choice`, and
  `Quot.sound`; no residual diagnostic output.
- Metadata audit: 25 unique declarations (23 theorems, 2 definitions), all 10
  direct import edges, all 9 incoming imports, fresh direct dependencies and
  owned objects, exactly one umbrella import per new module.
- Refreshed scoped lexical publication audit: 25/25 declarations (15 actual-law
  and geometry, 7 precision-kernel, 3 generic bridge), no partial results,
  markers, pagination gaps, or stderr. Scoped whitespace checks clean.
- Global lint snapshot: exit 1, 8 unrelated errors, 367 warnings. Unreachable
  RHTower modules: `CCMPolarOddPrimeJumps`, `LindelofQuasiRHCosineThreshold`,
  `PaperThetaClosedConvolution`, `WeilBoundedDenominatorLockConvolution`,
  `WeilBoundedDenominatorLockPeriodicity`; unreachable HTGeometry module:
  `QKrawtchoukCompanionTriangular`. Existing `sorry`s:
  `CCMPolarOddPrimeJumps.lean:104` and `WeilBoundedDenominatorLockPeriodicity.lean:397`.
  No error references a module in this increment. Unrelated files untouched.
- Transient missing objects in a shared transitive dependency rebuild resolved
  before actual-law checks. No duplicate or full build was launched. The broad
  import-closure snapshot also observed source-newer indirect objects (129 in
  the final readiness snapshot); no full-corpus freshness claim is made.
- Local premise audit: sqrt/rnDeriv lexical query returned this bridge alone;
  direct installed Lean sources supplied RN integrability and the common-measure
  quotient theorem. Both initially retained bridge premises were removed,
  reproved on paper, and natively verified before final publication.

Audit artifacts: `/tmp/hgt-weil-affinity-{metadata,audit-summary,index-summary}.json`,
`/tmp/hgt-weil-affinity-final-audit.{lean,log}`, `/tmp/hgt-weil-affinity-lint.log`;
native leaf logs use `/tmp/hgt-<Leaf>.log`.

## Remaining research boundary

The [adaptive replication increment](finite-weil-quadratic-adaptive-replication.md)
now proves that equal diagonals admit monotone m(r)<=r tending to infinity with
affinity tending to one. Universal separation over all diverging schedules is
equivalent to unequal diagonals. Prescribed same-diagonal schedules, including
r copies, remain unresolved here. The corpus-wide research goal remains active.
