# Signed logarithmic traces characterize correlation compactness

## Domain and exact claim [PAPER PROOF]

Let S be any family of actual compact C² real sources f with R_f=h_f(0)>0
and normalized Levy energy E(f)<=K, for one real K. Put H_f=h_f/R_f.
No node value is assumed zero, nonnegative or otherwise constrained. The following
three conditions are equivalent:

1. For every epsilon>0, some integer N>=2 satisfies |H_f(log n)|<epsilon
   for all f in S and all n>=N.
2. For every epsilon>0, some A>0 satisfies |H_f(x)|<epsilon for all f in S
   and all real x with A<=|x|.
3. The normalized correlations have compact closure in the global supremum norm.

The complexification H_f: R->C is an isometry and lets us reuse the existing
bounded-continuous-function compactness theorem. The claim concerns actual
correlation kernels; it does not assert source realization for arbitrary limits.

## Signed sampling estimate [PAPER PROOF]

Write c=exp(-1/2)>0 and m(T)=ceil(exp T). The certified grid-free sampling theorem,
divided by R_f², gives for T>=0

    c T |H_f(T)-H_f(log m(T))|² <= 8E(f) <= 8K.

This retains the actual signed value H_f(log m(T)). Set K₊=max(K,0).
For epsilon>0 let A=1+8K₊/(c epsilon²)>0. If T>=A and the sampling error were
at least epsilon, the preceding inequality would imply

    c T epsilon² <= 8K₊ < c A epsilon²,

a contradiction. Thus the sampling error is uniformly less than epsilon beyond A.
Using K₊ avoids any nonnegativity premise on K and handles an empty source class.

## Equivalence of the two tail conditions [PAPER PROOF]

Assume (1). Apply it with epsilon/2 to obtain N>=2. Obtain the sampling radius A
for epsilon/2 and set R=max(A,N)>0. If |x|>=R, put T=|x|. Since exp T>=T+1,
m(T)>=N. Therefore

    |H_f(x)| = |H_f(T)|
      <= |H_f(T)-H_f(log m(T))| + |H_f(log m(T))| < epsilon.

Evenness gives the first equality. Hence (2).

Conversely, assume (2), choose its radius A, and put N=max(2,ceil(exp A)).
For n>=N, exp A<=n and monotonicity of log gives A<=log n<=|log n|.
Applying (2) at log n proves (1).

## Continuum tails imply compactness [PAPER PROOF]

Every H_f is continuous and |H_f|<=1. The existing grid-free logarithmic
continuity modulus with ceiling K₊ gives equicontinuity uniformly over the family.
Condition (2) is the uniform two-sided tail hypothesis of
`HTGeometry.isCompact_closure_bcf_of_uniform_tails`. Its other hypotheses are
exactly the envelope and equicontinuity just derived. The theorem gives (3).

## Compactness forces uniform tails [PAPER PROOF]

Each actual compact source has a compactly supported correlation. Fix epsilon>0.
Compact closure supplies a finite epsilon/2-net whose centers belong to the original
family of normalized correlations. This precise center property is provided by
`exists_finite_cover_balls_of_isCompact_closure`; no vanishing property is assumed
for an arbitrary limit kernel.

Each center vanishes outside some finite symmetric interval. Take one positive
radius larger than all these finitely many radii. At any x beyond that radius,
every center is zero. Any family member lies within epsilon/2 in global norm
of a center, hence its value at x has absolute value less than epsilon/2<epsilon.
This proves (2). For the empty net/family choose radius one. No common source
support, common source profile, derivative bound or polar moment is required.

## Consequence, scope and novelty boundary [PAPER PROOF]

Every sequence drawn from a family satisfying (1) has a strictly increasing
subsequence of normalized correlations converging uniformly on the entire line
to a continuous real kernel, by compactness and isometric complexification.
This upgrades the previous all-grid compactness theorem to an exact criterion
for unrestricted signed logarithmic traces.

This does not assert hyperbolically weighted polar-tail control, preservation of
polar balance, or continuity of singular Levy energy. Package 10 already shows
that even zero traces and strong source convergence cannot guarantee the latter.
Arzela–Ascoli, finite uniform nets and the earlier sampling estimate are reused;
the connected contribution is the exact signed-grid criterion in the actual
bounded-energy source domain. No exhaustive external priority claim is made.

## Search and formal status

Deep corpus search `signed logarithmic grid trace uniform tail compact closure`
completed with an older-generation coverage snapshot and unmeasured semantic
coverage. Suggestions outside the relevant source domain are not used. Lexical
fallback and direct source reads identify the actual sampling theorem, the
bounded-function compactness theorem, and the finite-net lemma with original-set
centers. Logs: `/tmp/signed-grid-trace-{research,lexical}.txt`.

Certified package 11. Direct `lake --old env lean` checks pass without diagnostics
for `SignedGridEnergySources.lean` (9 public theorems, 2 definitions, 1 structure),
`SignedGridTailEquivalence.lean` (3 theorems, 2 definitions), and
`SignedGridTraceCompactness.lean` (5 public theorems, 1 private finite-family helper).
All 22 public declarations were audited through `/tmp/signed_grid_trace_axioms.lean`;
the private helper is covered transitively. Only `propext`, `Classical.choice` and
`Quot.sound` occur. All three umbrella imports and every exact declaration/module
API entry were verified; index refresh passed. No umbrella build ran.

Formal lint reports seven concurrent foreign modules missing umbrella reachability:
`CoprimeAlternatingProjectionRate`, `CoprimeProjectionAngleNorm`,
`CoprimeProjectionAnglePolynomial`, `CoprimeProjectionNeighbors`, `SignedGramCapacity`,
`SignedGramCutoffComparison`, and `SignedGramCutoffHierarchy`. No owned leaf has a
lint error; repository-wide green is not claimed.

Logs: `/tmp/signed-grid-sources-leaf.log`,
`/tmp/signed-grid-tail-equivalence-leaf.log`, `/tmp/signed-grid-compactness-leaf.log`,
and `/tmp/signed-grid-trace-{axioms,index,lint}.log`.
The read-only field README remains unchanged at SHA256
`80c91d482d9dfcfeb86508edcf5551d34d34a5ef333d3fab64be78e75dd67507`.
