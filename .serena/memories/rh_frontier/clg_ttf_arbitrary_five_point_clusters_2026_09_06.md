# CLG/TTF arbitrary five-point clusters: closed

Extends `mem:rh_frontier/clg_ttf_five_point_cusp_closure_2026_09_06` and `mem:rh_frontier/clg_ttf_global_d1_rank_three_mixture_2026_09_06`. Prior goal turn was progress: authoritative Lean state advanced from equispaced cusp to all distinct five-point cluster shapes.

## Exact physical capstone

`RHTower.exists_thetaCuspCenterMixedGramFive_posDef_cluster`, `formal/GaloisForLFunctions/RHTower/ThetaCuspCenterMixedFivePointCluster.lean:99`:
For every 0<a<1/2, exists δ>0, for every injective t : Fin 5 -> Real with |t i-t j|<δ for all i,j, the literal theta center-mixed Gram matrix is Matrix.PosDef. No ordering, minimum-gap, or spacing-ratio restriction. Radius may depend on aperture. Sorted diameter and node-norm versions are also proved.

## New generic infrastructure

1. `HTGeometry/MixedTranslationDividedDifference.lean`: mixed translation-kernel divided difference at p+1 and q+1 increasing nodes equals (-1)^q f^(p+q)(u-v)/(p!q!), with u,v in their closed node hulls. Includes p or q zero. Proof uses existing `HTGeometry/HilbertIrreducibility/DividedDifference.exists_dividedDiff_eq` twice. First differentiate the finite right-stencil function, apply left MVT, then right MVT to the literal derivative; do not differentiate chosen mean-value points.
2. `HTGeometry/PrefixDividedDifferenceGram.lean`: exact square prefix transform, lower-triangular invertibility, exact congruence, uniform entrywise derivative-matrix limit over arbitrary ordered cluster shapes. Generic `exists_translationSampleGram_posDef_radius` proves: even C^(2N-2) kernel with strict factorial-normalized signed derivative Gram matrix has one radius covering every ordered rank-N cluster. No lower gap bound or inverse-Vandermonde estimate needed.
3. Physical source wrapper factorial-rescales already proved fivePointJetMatrix, uses existing C8 regularity, translation invariance, and sorting/permutation congruence. All source premises discharged.

## Verification and discipline

Scratch and production direct `lake env lean` passed for all three modules; production warning-free. Only necessary new oleans generated. New physical capstone #print axioms gives [propext, Classical.choice, Quot.sound]; old theorem audits not repeated. Formal lint and git diff --check passed. Corpus indexes refreshed. All three modules wired to HTGeometry/RHTower umbrellas without umbrella or full/cascading builds. All 26 new public declaration names searched across the corpus: zero outside matches. No numeric certificate/oracle or added axiom.

Stage3 proof card: `docs/drafts/pipeline/3-formalized/clg-ttf-arbitrary-five-point-clusters.md`; owned Stage1 card moved there. Frontier map, TCD hard-core status, original five-point notebook, and earlier Stage3 D1/mixture/equispaced cards updated. Universal STATUS unchanged because no new route-independent RH constraint was needed. Other tasks concurrently update the shared tree; preserve their changes and do not commit/push without user authorization.

## Remaining goal

RH still unproved; goal remains active. Full endpoint: completed theta source -> Xi Bezoutian -> EVERY finite two-channel Weil packet PSD -> RH. Global D1, actual rank-three mixture, equispaced cusp, and arbitrary local rank-five cluster shapes are closed. Do not continue listing unequal gaps at rank five as an open local obstruction. Higher ranks, global packet geometry, actual theta-to-divisor incidence, and cofinal no-escape remain; separate C5 fronts remain open. Generic complete reflected-Hankel real-rootedness no-gos still apply within their exact scopes. Local positivity radii depending on rank/aperture do not establish all-packet positivity.

User efficiency constraints persist: one foreground Lean process per agent, direct scratch checks, only necessary oleans, no umbrella/full builds, audit only new capstones, remove scratch and stale owned processes.