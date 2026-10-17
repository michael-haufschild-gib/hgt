# Smooth infinite-grid polar recovery family

- **ID:** infinite-grid-polar-recovery-family-2026-10-17
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** `infinite-grid-tail-rigidity-2026-10-17.md`
- **Objective:** Construct actual smooth compact polar two-copy sources satisfying all logarithmic
  zeros, with normalized Levy energy bounded by `A+B T` as separation `T` tends to infinity.

## Plan

1. Reuse source rescaling, smooth seed, polar-copy identity, and exact Levy tail integral.
2. Prove logarithmic compression cost and grid avoidance on paper.
3. Formalize the actual family and energy bound; source existence and all-grid admissibility
   must be conclusions, not hypotheses of the endpoint.
4. Audit leaves, axioms, umbrella wiring, and indexes. Count one package only after the
   construction and energy estimate are connected.

## Conjecture and scope

The previous lower barrier has the correct order: at logarithmic cell midpoints, sufficiently
compressed smooth seeds produce polar infinite-grid sources of energy `O(T)`. The general
distance-to-grid law remains part of the broader frontier; this family tests attainability
without claiming an optimal coefficient.

## Prior audit

Corpus search found dilation identities and arbitrarily small broad-source energy in
`BroadSpectralCostRealization.lean`, but no logarithmic compression upper bound or infinite-grid
polar recovery family. Existing polar-error estimates concern separated copies and will be reused.
Logarithmic dilation costs themselves are classical; Laptev–Weth, *Spectral properties of the
logarithmic Laplacian*, Lemma 2.5, gives the corresponding eigenvalue scaling law. The contribution
must be the actual infinite-grid polar construction with verified quantitative cost.

## Proof and implementation state

Dependency-closed paper proof: `docs/reports/BiScaleUncertainty/InfiniteGridPolarRecovery.md`.
Both leaves pass without diagnostics with the support-aware upper bound `C+T`.
Outside the compressed correlation support, the normalized tail integrand is exactly the Levy
weight. The endpoint derives smoothness, compactness, positive mass, exact polar balance,
every infinite-grid zero, and lower bound `exp(-1/2)T/4`. A separate theorem proves arbitrarily
large midpoint separation. All 17 new theorems passed the scratch axiom audit with only
`propext`, `Classical.choice`, and `Quot.sound`. Both modules are wired and all theorem names
appear in the generated API. Certified package 2 of the parent goal; helpers are not counted separately.
Global lint remains non-green because six concurrent foreign modules lack umbrella reachability;
see the paper for the exact list. Neither owned module has a lint error.

Owned logs: `/tmp/infinite-grid-compression-build.log`, `/tmp/infinite-grid-recovery-build.log`,
`/tmp/infinite-grid-recovery-axioms.log`, `/tmp/infinite-grid-recovery-index.log`,
`/tmp/infinite-grid-recovery-lint.log`.
No numerical computations, full builds, or new analytic assumptions were used.
