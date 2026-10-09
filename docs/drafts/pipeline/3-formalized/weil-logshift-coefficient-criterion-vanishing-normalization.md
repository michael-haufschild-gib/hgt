# Intrinsic coefficient criterion and vanishing normalized potentials

Status: FORMALIZED. Dependency-closed paper proof, twelve theorems, and one `C₀` constructor verified.

## Corpus question and sources

Does factorial regularity depend only on the unweighted recovered-deviation sequence? Can a suitable normalization produce a continuous function vanishing at infinity, beyond pointwise summability at every shift?

Only local Lean sources were consulted. Lexical research queries covered factorial coefficient regularity and summable continuous vanishing kernel potentials. Relevant dependencies: uniform kernel comparison, fixed-order transfer, factorial normalization, `riemannAutocorr_le_zero`, `exists_riemannAutocorr_le`, and `continuous_riemannAutocorr`. Existing continuity statements concern more specialized coefficient hypotheses; this increment obtains a normalization criterion for arbitrary signed coefficient sequences and arbitrary recovery histories.

## Dependency-closed proof

Let R be the native positive autocorrelation and K_y(n)=R(y+log n)+R(y-log n). Uniformly, K_y(n)<=U=2R(0). At the moving shift y=log n, K_y(n)>=R(0)>0, including n=0 under Lean's logarithm convention.

If v(n)K_c(n) has a factorial bound of fixed order m, the preceding uniform comparison theorem supplies a bound of that same order simultaneously at all shifts. Evaluate it at y=log n and divide by R(0). This bounds v itself at order m. Conversely multiply a factorial bound for v by U. Thus each fixed factorial-order class is identical before and after multiplication by any fixed shifted kernel. Taking the union over m gives the intrinsic criterion for recovered deviations, without boundedness assumptions on histories.

The factorial-normalization theorem then gives m and B>0 such that w(n)=exp(-Bn)v(n)/(n!)^m is summable whenever one kernel potential has a factorial majorant. Each function y -> w(n)K_y(n) is continuous and bounded in absolute value by U|w(n)|. The latter is summable, so the potential series converges absolutely at every shift and uniformly on the whole line, and its sum is continuous.

For fixed n, both |y+log n| and |y-log n| tend to infinity as |y| tends to infinity. The corpus envelope R(z)<=C exp(-2|z|) and nonnegativity imply K_y(n) tends to zero along the cocompact filter. Dominated convergence with U|w(n)| therefore proves that the potential sum vanishes at infinity. Package this sum as a native `C₀(ℝ, ℝ)` value.

Conversely, existence of a factorial/exponential normalization whose series is summable at each shift (and has this vanishing continuous sum) implies a factorial majorant at the chosen source shift by the established summability-to-majorant theorem. The final equivalence has no extra analytic premise.

## Intended artifacts

- `WeilLogShiftFactorialCoefficientCriterion.lean`: moving-shift lower bound, fixed-order coefficient equivalence, factorial-majorant equivalence, native recovery criterion, normalized coefficient criterion.
- `WeilLogShiftVanishingNormalization.lean`: kernel continuity and decay, summable-coefficient potentials as `C₀` functions, exact normalization criterion and native recovery specialization.

## Verification

Pending direct leaf checks, axiom audit, umbrella imports, index refresh, and formal lint. No external sources, numerical experiments, or unproved analytic assumptions.

Both owned leaves compiled/exported cleanly using `lake --old env lean`. Coefficient criterion contributes five public theorems; vanishing normalization contributes seven public theorems and the `pairedLogPotentialC0` definition. Axiom audit pending.

Implementation note: simplifying the bare norm function with `Real.norm_eq_abs` did not change the cocompact limit statement. An explicit function equality `funext Real.norm_eq_abs`, followed by rewriting, passed the local API check and final leaf compile.

## Final checkpoint

- Both direct `lake --old env lean` leaf compile/export checks exited 0 with clean logs; fresh oleans verified.
- All thirteen public declarations audited: exactly `propext`, `Classical.choice`, `Quot.sound`.
- Both umbrella imports unique. Index refresh exited 0; all thirteen declarations found at their unique expected indexed locations. A narrow definition lookup recovered `pairedLogPotentialC0`, which the broad query's result cap omitted.
- Fresh formal lint exited 1 with five unrelated unreachable modules: `RHTower.ZetaSmoothedPartialSumsDisc`, `HTGeometry.PaperCofaceExponentEmbedding`, `HTGeometry.QKrawtchoukCompanionTriangular`, `HTGeometry.TriangularPolynomialAutomorphism`, and `HilbertMetric.HorizontalLamzouriMixedRangeSharp`. No owned-leaf lint errors.
- No full builds, extra axioms, numerical experiments, external sources, or heartbeat changes.

Exact new insight: multiplying by the native shifted kernel preserves every fixed factorial-order class. For arbitrary signed coefficient sequences and arbitrary recovery histories, factorial regularity is equivalent to existence of a single factorial/exponential normalization summable at every shift whose actual sum is a continuous function vanishing at infinity.

Next conjecture: combine the common finite-family envelope with the `C₀` construction to obtain a single normalization and a bounded `C₀`-valued linear operator on the actual regular subspace (and an affine receiver on its affine fibres). This common-operator statement has not yet been formalized. Its paper mechanism is the uniform geometric term bound from the established all-shift envelope, followed by continuity and dominated convergence; the operator bound should follow from the existing absolute-sum estimate.


Subsequent formalized result: [common C0 operator and stable recovery receiver](weil-logshift-common-c0-operator.md). A single normalization now defines a bounded linear operator on the actual regular subspace, and an affine-family receiver with explicit `HasSum` contracts and uniform supremum-norm difference bounds.
