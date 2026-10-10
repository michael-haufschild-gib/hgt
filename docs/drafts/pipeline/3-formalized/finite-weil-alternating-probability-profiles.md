# Alternating positive probability profiles hidden from cheap Weil tests

Stage: dependency-closed paper proof; Lean work pending.
Classification: corpus-internal positive-probability bridge, no external novelty claim.
Sources: local Lean corpus and installed Lean/mathlib only.

## Exact target

For every logarithmic cluster r,k, its explicit canonical unit dual beta has
strictly alternating signs and positive last entry. Every coefficient ratio is
an explicit product of logarithmic node-difference ratios. Split beta into

    S=sum_i |beta_i|,
    p_i=(|beta_i|+beta_i)/S,   q_i=(|beta_i|-beta_i)/S.

These are nonnegative probability profiles with disjoint supports, covering
every cluster label. Their difference alternates, their absolute difference
sums to 2, and their centered logarithmic moments through r agree exactly.

There exist fixed B>0,L>=1 such that, under the existing width budget
4L(r+1)<=k+2, every actual Gram test w on any finite support containing the
cluster satisfies

    |sum_i p_i V(w)_(k+i) - sum_i q_i V(w)_(k+i)| * (k+2)^2 * 2^r
      <= B * cost_1(w).

The same two explicit positive profiles are thus maximally separated in total
variation while giving exponentially close readings to bounded-cost actual
tests. This is stronger structural information than existence of a signed
moment-null vector. No sharper absolute-sum asymptotic is claimed.

## Dependency-closed proof

1. For distinct ordered nodes x_i and nodal weights b_i, erase i,j from the
   products to obtain the exact ratio
   b_j/b_i = - product_{l!=i,j}(x_i-x_l)/(x_j-x_l).
   Sup-norm normalization cancels in this ratio.
2. For adjacent i,j, each remaining node is below both or above both. Every
   factor is strictly positive, so the ratio and adjacent coefficient product
   are negative. At the last node all factors defining its weight are positive.
   The existing logarithmic nodes are strictly increasing.
3. The canonical vector has sum zero and sup norm one. Choose |beta_i|=1.
   The existing finite coordinate/pairing inequality, applied to the constant
   vector one, gives sum_{j!=i}|beta_j|>=1. Hence S>=2.
4. The displayed p,q formulas give nonnegativity, unit sums, disjoint support,
   positive combined weight at each node, and p-q=(2/S)beta. Since 0<2/S<=1,
   sum_i|p_i-q_i|=2, all moments through r match, and strict alternation survives.
5. For arbitrary readings y, the difference of the two expectations equals
   (2/S)sum_i beta_i y_i. Its absolute value is no larger than the canonical
   pairing. Transport the pairing through the cluster embedding and invoke
   `exists_finiteWeilGram_canonical_cluster_sensitivity`. Its constants remain
   unchanged, and all analytic inputs are already unconditional producers.

## Local audit and implementation scope

Documented `nodalWeight sign` search returned no hits; source search found no
nodal-weight sign/ratio theorem. Search the positive moment-profile formulation
before implementation. Existing canonical and interpolation leaves provide the
exact weights and full support; do not reprove them.

Add finite weight-ratio/sign algebra, normalized positive-profile algebra, and
the logarithmic-cluster/actual-test receiver. Preserve existing source modules.
Native-check each new leaf, audit every public declaration and new mathlib API,
wire imports once, refresh index, run lint, and verify freshness. One owned Lean
process at a time; no numerical computations or heartbeat changes.

## Actual separation is realizable

The sign indicator 1_{beta_i>0} has expectation one under p and zero under q.
Zero-extend these desired readings to the full coefficient support and apply
`surjective_finiteWeilGramCoefficientVector`. This constructs an actual finite
Gram test giving readings 1 and 0. The final sensitivity receiver includes this
witness, so the exponential restriction describes the cost of a realizable
separating measurement. The distance statement is explicitly the finite l1
norm 2 (equivalently, usual probability total-variation distance 1).

The positive-profile source audit returned no declarations for the documented
`alternating moment probability` query and no matching WeilLogShift source text.

Formalization completed 2026-10-10. Current stage: `3-formalized`.

Exact Lean receivers:
- `WeilLogShiftMomentRatios.lean`: exact weight ratios, adjacent sign alternation, positive last weight.
- `WeilLogShiftMomentProbabilities.lean`: absolute mass at least two; positive and negative normalized profiles, disjoint support, unit masses, absolute difference sum two, pairing bound.
- `WeilLogShiftCanonicalQuadrature.lean`: explicit log-cluster probability profiles, matching moments through order `r`, strict alternation, actual separating Gram test, and unconditional `exists_finiteWeilGram_probability_profile_sensitivity` at line 128. Separating expectations are exactly one and zero; every actual test obeys the native-cost sensitivity bound.

Verification: all three leaves compiled using native `lake --old env lean`, with empty warning/error logs. Scratch audit `/tmp/hgt-quadrature-final-audit.lean` checked all 24 authored public declarations and 34 imported API names; axioms only `propext`, `Classical.choice`, `Quot.sound`. Source/direct-dependency outputs fresh, all three umbrella imports occur once. No whole-project build, numerics, web search, or external paper reading.

Global formal lint exited 1 on six unrelated missing umbrella imports: `RHTower.PaperPrimeFredholmReconstruction`, `RHTower.PaperZetaCyclePhysicalReconstruction`, `RHTower.PaperZetaCycleVaryingPeriods`, `RHTower.XiCosineShiftAlmostEveryHeight`, `HTGeometry.PaperCirclePhysicalHeight`, and `HTGeometry.QKrawtchoukCompanionTriangular`. No errors named these three new leaves. Shared-worktree files left untouched.

Classification: local-corpus structural bridge, not an external novelty claim. Next candidate, unproved here: the full probability simplex fiber with these moments is precisely the segment joining the two profiles. Exact ratios do not establish sharper magnitude bounds.

Successor formalized 2026-10-10: [complete probability moment fiber](finite-weil-probability-moment-fiber.md). The formerly unproved segment conjecture is now exact: every member is a unique mixture, with l1 distance `2|a-b|`; an actual Gram test reads the mixture coordinate, and the native-cost sensitivity law holds for every pair in the fiber. Twelve public declarations passed native compilation and axiom audit.
