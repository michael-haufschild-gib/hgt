# Uniform factorial regularity across every real shift

Status: FORMALIZED. Dependency-closed paper proof and all ten Lean theorems verified.

## Corpus question

The existing `weilLogShiftHasFactorialMajorant_some_shift_iff_origin` only transfers regularity inward. Does origin regularity control all shifts, even with one common normalization over an entire finite-dimensional affine history family?

Sources are exclusively the local Lean corpus. The lexical corpus query `pairedLogKernel exponential bound factorial shift regularity` returned the existing lower-envelope and origin-transfer results; exhaustive targeted `rg` searches found the global autocorrelation bound. No web, external papers, or numerical experiments.

## Exact conjecture and paper proof

Write K_y(n)=pairedLogKernel y n, positive for every real y and natural n. The corpus theorem `WeilExcess.riemannAutocorr_le_zero` gives K_y(n) <= U := 2 riemannAutocorr(0), with U>0, uniformly in y,n.

Fix a source shift c. Put b=logKernelCriticalRate(c)+1>0. The corpus lower-envelope theorem supplies d>0 and N such that d exp(-bn)<=K_c(n) for n>=N. Put

V = 1/d + sum_(j<N) exp(-bj)/K_c(j).

Every term is nonnegative, V>0, and exp(-bn)/K_c(n)<=V for every n: use the sum term for n<N and the lower envelope otherwise. Multiplication by exp(bn)K_c(n)>0 gives 1<=V exp(bn)K_c(n). Thus

K_y(n)<=U V exp(bn)K_c(n)

simultaneously for all real y and all n, including the finite head. The comparison constants depend only on source shift c.

For any signed sequence v and fixed factorial order m, a bound |v(n)K_c(n)|<=D exp(An)(n!)^m on a tail implies the simultaneous bound

|v(n)K_y(n)| <= U V |D| exp((A+b)n)(n!)^m

on the same tail for every y. Consequently membership in each fixed factorial-order class, and in the union of all finite orders, is independent of shift. In particular one regular shift implies a common majorant across all shifts. This concerns factorial regularity; it does not assert shift invariance of unnormalized summability.

For finite-dimensional affine history families, homogenize the origin moment map F(a) to H(a,t)=F.linear(a)+t F(0). The established uniform linear envelope gives one m,A,D and the bound D(1+norm a)exp(An)(n!)^m for every regular amplitude at origin. Apply the global comparison with source shift 0: one m,A+b,C bounds every amplitude and every shift. One extra unit of damping gives the pointwise majorant C(1+norm a)exp(-n), hence absolute summability and a common sum bound across the entire real shift line. Conversely normalized summability at any shift implies a factorial majorant there, hence origin regularity. No new analytic premise or continuity into sequence space is used.

## Intended Lean artifacts

- `WeilLogShiftUniformKernelComparison.lean`: global comparison, same-order transfer, and shift-independent factorial regularity for arbitrary signed kernel potentials and native recovery moments.
- `WeilLogShiftAllShiftFactorialNormalization.lean`: one common normalized envelope and absolute-sum bound for all real shifts in any finite-dimensional affine bounded-history family.

## Verification log

Pending direct `lake --old env lean` leaf checks, axiom audit, umbrella wiring, index refresh, and formal lint.

Kernel-comparison leaf: direct compile/export clean. Seven public theorems cover a uniform global comparison, same-order transfer, and shift invariance for arbitrary signed sequences and recovery histories (boundedness unnecessary). All-shift affine-family leaf written; direct compile pending.

Final verification supersedes pending notes above:

- Both leaves compiled/exported cleanly with `lake --old env lean`; fresh oleans verified.
- `WeilLogShiftUniformKernelComparison.lean`: seven public theorems.
- `WeilLogShiftAllShiftFactorialNormalization.lean`: three public theorems.
- All ten axiom audits contain exactly `propext`, `Classical.choice`, `Quot.sound`.
- Two unique RHTower umbrella imports; index refresh exited 0; all ten declarations indexed exactly once.
- Formal lint exited 1 with six unrelated unreachable HTGeometry modules: `PaperGenericMinorWeights`, `PaperNormalCrossingNormalLine`, `PaperRectangularRankNormalLine`, `PaperSquareRankNormalLine`, `PaperVeroneseNormalLine`, and `QKrawtchoukCompanionTriangular`. No errors in either new leaf.
- No full builds, external sources, numerical experiments, added axioms, or heartbeat changes.

New insight: every fixed factorial-order class is shift invariant; one common factorial/exponential normalization works simultaneously across the entire real shift line and every regular amplitude of a finite-dimensional affine bounded-history family. The constants depend on the family, not on its amplitude or target shift.

Next corpus questions, not yet audited or formalized: identify each fixed factorial-order class directly with the unweighted recovered-deviation sequence; determine whether the normalized moment sum forms a continuous function vanishing at infinity, with an operator bound on the actual finite-dimensional regular locus.


Subsequent result: [intrinsic coefficient criterion and vanishing normalization](weil-logshift-coefficient-criterion-vanishing-normalization.md) formalizes the unweighted coefficient equivalence at each fixed factorial order and an individual `C₀` normalization for arbitrary histories. A common bounded `C₀` operator for finite-dimensional regular families remains a next conjecture.
