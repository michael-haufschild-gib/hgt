# Split-formation parallax — Lean certification

- **ID:** ULF-CPM-1
- **Lean modules:** `HTGeometry.ConstitutiveSplitFormationParallax`,
  `HTGeometry.SplitFormationParallaxDistanceBound` (new)
- **Status:** `[LEAN-CERTIFIED] [UMBRELLA-WIRED] [NO SORRY] [NO AXIOMS] [TARGETED BUILD]`

The pre-existing leaf already carried `(CPM.8)`, `(CPM.9)`, `(CPM.11)`, `(CPM.12)`, the
neutral-kernel equivalence, `(CPM.14)`, `(CPM.15)`, `(CPM.16)` and `(CPM.20)`.  Its recorded gap
was the quantitative estimate

`∑_k ‖Ω_{kji} x‖² ≥ A α² dist(x, N_{ji})²`  `(CPM.18)`.

The new leaf closes it:

* `neutralOverlap Fi Fj = ker (hiddenResidual Fi Fj)` — `(CPM.17)`;
* `norm_hiddenResidual_ge_dist` — a lower bound on the orthogonal complement transfers to
  `α · dist(x, N) ≤ ‖R x‖`, using `Submodule.starProjection` and `starProjection_minimal`
  (the distance is the honest `⨅ n : N, ‖x − n‖`);
* `parallaxEnergy_ge_dist_sq` — **(CPM.18)**, by composing that with the fusion-frame lower bound
  `parallaxEnergy_fusionFrame_bounds`.

## Verification (2026-08-20)

Both modules elaborate from the tree with 0 errors and all 41 public declarations across them use
only `propext`, `Classical.choice`, `Quot.sound`.  Both are imported by
`GaloisForLFunctions.HTGeometry.UniversalLawField`.
