# Finite Weil cost after removing logarithmic backgrounds

Stage: formalized; dependency-closed paper proof and native Lean audits complete.
Classification: corpus-internal bridge; no external novelty or priority claim.
Sources: local Lean corpus and installed Lean/mathlib only.

## Source finding

`WeilLogShiftAllOrderCancellation.exists_normalized_real_moment_annihilator`
constructs a sup-norm unit vector annihilating every moment through order r.
The actual nodes are log(n+i)-log(n). The paired-kernel and exponential
envelopes currently forget these equations. Rank-nullity alone supplies no
sharper coefficient absolute-sum profile, so a square-root weight bound remains
unproved and is not assumed here.

Local audit: documented lexical research `moment background`, restricted to
WeilLogShift, returned no declarations. Exhaustive background/polynomial-
annihilation text search over WeilLogShift leaves also returned no matches.

## Exact target

There exist B>0 and K>=2 such that for each N>=2K, writing q=N/K and
h(j)=log(j+2)-log(N-q+2), there exist i in range N and d with norm d=1,
|d(i)|=1, off-coordinate absolute sum <=q-1, and

    sum_j d(j) h(j)^p = 0    for every p<=q-2.

For every actual test w and every coefficient vector b indexed by p<q-1,
put y=V_N(w), P(j)=sum_p b(p) h(j)^p, z=y-P, E=2^q, C=cost_1(w).
Then

    E |z(i)| <= B C + E sum_{j!=i} |d(j)| |z(j)|
             <= B C + E(q-1) ||z-single_i(z(i))||.

The constants precede the cutoff; the dual witness precedes both w and b.
Thus smooth logarithmic backgrounds may be removed without changing the
cost-sensitive dual response. Constant backgrounds are included.

## Dependency-closed paper proof

1. Retain the moment equations from the existing normalized annihilator in
   the paired-kernel envelope. Its analytic estimate is unchanged.
2. Retain the same equations through the existing geometric-envelope proof.
3. For q=N/K, r=q-2, k=N-q, use the existing width budget and zero-extend the
   cluster coefficients along j -> k+j. Finite sum transport preserves every
   moment with centered node h. Maximal coefficient selection gives |d(i)|=1;
   norm and absolute-sum transport give the existing q-1 off-weight bound.
4. The existing sensitivity estimate gives E|sum_j y(j)d(j)|<=BC.
5. Interchange the two finite sums in sum_j P(j)d(j). Each inner moment is
   zero; hence the background pairing vanishes exactly. Therefore the same
   sensitivity estimate holds with z=y-P.
6. Apply the already verified finite coordinate-pairing and off-weight norm
   inequalities to z. No remaining analytic premise is required.

## Implementation and checks

Preserve existing public APIs as corollaries of stronger producers. Factor
finite extension algebra to avoid copying the cluster witness proof. Add a
new moment/background receiver leaf and wire it once into the umbrella.

Current downstream closure of AllOrderCancellation contains eight leaves:
AllOrderCancellation, AllOrderClusterCost, SuperpolynomialGramCost,
ExponentialClusterCost, GramCoordinateObstruction, GramUnitResponse,
GramIsolationSeparation, GramCostLeakage (all prefixed WeilLogShift).
Rebuild this dependency closure plus changed/new algebra and receiver leaves,
one owned Lean process at a time. Audit every affected public declaration,
refresh the index, run formal lint, and verify artifact freshness.

## Nonvacuous exact-target consequence

For the same selected coordinate, every target P + a single_i is realized by
an actual finite Gram test, using the existing unconditional
`surjective_finiteWeilGramCoefficientVector` receiver. Its residual is exactly
single_i(a), so the off-coordinate norm vanishes. The new leakage inequality
therefore gives cost >= B^(-1) 2^q |a|, uniformly over all background coefficients
and amplitudes. Adding an allowed background cannot evade the spike cost.


## Verified formalization — 2026-10-10

New leaf: `formal/GaloisForLFunctions/RHTower/WeilLogShiftGramBackgroundLeakage.lean`.
The root `exists_finiteWeilGram_log_background_cost_leakage` retains all moments
and gives both weighted and sup-norm bounds for every background coefficient
vector. `exists_finiteWeilGram_log_background_isolation_cost` includes actual
realizability of every background-plus-spike target and its universal
exponential cost lower bound. `finiteWeilLogBackground` names the background.

The existing analytic envelope, geometric envelope, and cutoff dual producers
now expose moment-preserving strengthenings. Their old APIs remain corollaries.
The chosen-coefficient cluster helper avoids duplicating the witness proof;
extension pairing, subtraction of backgrounds, and leakage algebra are shared.

All ten leaves in the complete affected dependency closure pass native
`lake --old env lean` checks. Source and direct-dependency artifacts are fresh,
and every leaf has exactly one umbrella import. The final scratch audit
`/tmp/hgt-moment-final-audit.lean` covers all 39 public declarations; its output
contains only `propext`, `Classical.choice`, and `Quot.sound`. Three newly used
mathlib API terms also passed a dedicated scratch check. Build logs are
`/tmp/hgt-moment-<leaf>.log`; no heartbeat settings were changed.

The sharper absolute-sum profile remains open. Current construction retains
moments but does not prove square-root concentration of coefficients. A next
local question is whether distinct logarithmic nodes force a unique annihilator
line (normalized coefficients up to sign), permitting a canonical divided-difference
interpretation.


Final integration: corpus index refreshed; the new isolation receiver is found
by the documented local research command, and both background roots are in
LEAN_API. Formal lint exits 1 for four unrelated missing umbrella imports:
`RHTower.JointAncestryLagAggregatePositivityAbscissa`,
`RHTower.PaperCriticalFeatureEntropy`,
`RHTower.PhotonicLosslessProductPortDensityLaw`, and
`HTGeometry.QKrawtchoukCompanionTriangular`.
The affected ten-leaf closure has no freshness or import failures. All owned
build, audit, index, lint, metadata, and search jobs have terminated.


## Canonical-dual follow-up — 2026-10-10

[Canonical moment dual](finite-weil-canonical-moment-dual.md) closes the
annihilator-line question. The vector is the normalized reciprocal product of
logarithmic node differences, unique up to sign, with no zero entries. Its
pairing equals the normalized top interpolation coefficient. The geometric
kernel envelope and actual Gram sensitivity now hold for these explicit weights.
