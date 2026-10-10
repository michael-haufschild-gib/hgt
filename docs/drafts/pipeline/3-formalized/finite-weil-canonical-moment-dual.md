# Canonical moment dual for logarithmic Weil clusters

Stage: formalized; dependency-closed paper proof and native Lean audits complete.
Classification: corpus-internal interpolation bridge, not an external novelty claim.
Research sources: local Lean corpus and installed Lean/mathlib only.

## Source audit

The existing Weil annihilator is normalized by rank-nullity. Its newly retained
moments invite a structural classification. Mathlib's `Lagrange.coeff_eq_sum`
and `Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero` provide the interpolation
and uniqueness ingredients. The corpus already uses divided differences in
`HTGeometry/HilbertIrreducibility/DividedDifference.lean` and
`HTGeometry/ConstitutivePrimitiveFormationProperness.lean`; interpolation itself
is not new. The intended bridge identifies the actual real sup-norm Weil
cluster witness and transfers its geometric envelope to explicit coefficients.

Documented local searches: `moment annihilator uniqueness` returned no hits;
`vandermonde moments` and `barycentric moment` exposed existing interpolation
and moment-determination lemmas. All six source files using the exact Lagrange
weight/coefficient APIs were located and their relevant uses inspected.

## Exact algebraic target and proof

At n+1 distinct real nodes x_i, set

    b_i = product_{j != i} (x_i-x_j)^(-1),   beta=b/||b||_infinity.

Lagrange coefficient extraction applied to X^p, p<=n, gives

    sum_i b_i x_i^p = 0 (p<n), and =1 (p=n).

If c annihilates moments p<n, set lambda=sum_i c_i x_i^n. The vector c-lambda b
annihilates all n+1 initial moments, so the invertible Vandermonde matrix gives
c=lambda b. Each b_i is nonzero. Therefore a nonzero annihilator has full
support; a sup-norm unit annihilator is exactly beta or -beta. The norm identity
1=|lambda| ||b|| makes the sign ambiguity precise.

## Weil target and proof

For each r,k use the r+2 nodes
x_i=log(k+i+2)-log(k+2). These are distinct for every natural k because logarithm
is injective on positive numbers. Define the canonical cluster to be beta above.
It has norm one, every coefficient nonzero, and all moments through r vanish;
every other normalized vector with those moments is beta or -beta.

The existing geometric envelope supplies some normalized c with exactly these
moments whenever 4L(r+1)<=k+2. Classification makes c=+/-beta, so its absolute
paired-kernel envelope transfers unchanged to the explicit beta. All constants
come from the existing unconditional geometric-envelope producer.

Finally, zero-extend this canonical vector into any finite support containing
the arithmetic cluster. The existing chosen-coefficient Gram sensitivity helper
gives the same cost inequality for every actual finite Gram test, with this
explicit dual and all cluster entries nonzero. Normalize the native cost using
the existing cost-scaling theorem. No additional analytic premise is introduced.

## Scope and verification

Add a pure real moment/interpolation leaf and a canonical Weil-cluster leaf.
Reuse existing producers without changing their sources. Wire both new leaves
into the umbrella; native-check each and audit every public declaration.
Verify referenced mathlib APIs in a scratch Lean file. Refresh index, run lint,
and check source/dependency freshness. No numerical computation or heartbeat
changes. This result does not assert a sharper absolute-sum bound.

## Exact interpolation interpretation

For arbitrary nodal data y, apply the same Lagrange coefficient identity to its
interpolating polynomial P. It gives sum_i b_i y_i = coeff_n(P), hence the unit
dual pairing equals coeff_n(P)/||b||. This identifies the canonical Weil response
with a normalized top divided difference, not merely an unspecified null vector.


## Verified formalization — 2026-10-10

`WeilLogShiftMomentBarycentric.lean` proves the nodal moment identity, exact
scalar classification by the last moment, full support of every nonzero
annihilator, unit normalization, the two possible orientations, and the exact
normalized interpolation-coefficient pairing.

`WeilLogShiftCanonicalCluster.lean` specializes this to the actual centered
logarithmic cluster. `finiteWeilCanonicalCluster_spec` is unconditional for all
natural r,k. `exists_pairedLogKernel_canonical_cluster_envelope` transfers the
existing geometric estimate to the explicit canonical coefficients, and
`exists_finiteWeilGram_canonical_cluster_sensitivity` supplies the actual-test
cost bound for their zero extension, nonzero at every cluster label.

Both native leaves compile with empty logs. All 20 public declarations and 24
mathlib API terms pass `/tmp/hgt-canonical-final-audit.lean`; only `propext`,
`Classical.choice`, and `Quot.sound` occur. Source/direct-dependency artifacts
are fresh and both modules have exactly one umbrella import. Incoming-import
search confirms the affected dependency closure consists only of these two
leaves. Existing source modules were not changed. No heartbeat changes or
numerical experiments were used.

Remaining question: use the explicit logarithmic node-difference products to
study sign alternation and coefficient-ratio bounds. The earlier q-1 off-weight
bound is not improved or claimed sharp here.


Final integration: corpus index refreshed; the explicit actual-test receiver is
found by the documented local research command at CanonicalCluster line 83.
The classification, pairing, and sensitivity roots are in LEAN_API. Formal lint
exits 1 solely for two unrelated missing umbrella imports:
`RHTower.SuzukiScrewBeurlingDenyAperture` and
`HTGeometry.QKrawtchoukCompanionTriangular`.
All owned compiler, audit, index, lint, and search jobs have terminated.

Successor formalized 2026-10-10: [alternating probability profiles](finite-weil-alternating-probability-profiles.md). Exact ratios and alternating signs now yield explicit disjoint probability profiles with matching moments, realizable separation, and a universal native-cost sensitivity bound. All 24 new public declarations passed the axiom audit.
