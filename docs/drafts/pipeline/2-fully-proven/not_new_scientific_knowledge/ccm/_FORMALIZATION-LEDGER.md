# CCM (not-new-scientific-knowledge) Stage-2 → Stage-3 formalization ledger

Goal: every card in this folder gets an unconditional Lean 4 theorem (no hypotheses, no axioms,
`#print axioms` = `[propext, Classical.choice, Quot.sound]`), a `-formalized.md` certificate, and a
move to `docs/drafts/pipeline/3-formalized/not_new_scientific_knowledge/ccm/`.

Status legend: `TODO` · `AUDIT` (module found, clause audit running) · `BUILD` (writing Lean) ·
`DONE` (promoted).

| # | card | candidate module(s) | status |
|---|---|---|---|
| 1 | `ccm-aperture-morse-hardymodel-index-exhaustion-law` | | TODO |
| 2 | `ccm-aperture-morse-index-conservation-law` | | TODO |
| 3 | `ccm-boundary-strip-weak-compactness-transfer-law` | | TODO |
| 4 | `ccm-bv-muntz-graph-domain-extension` | | TODO |
| 5 | `ccm-causal-pick-affine-conjugacy-law` | | TODO |
| 6 | `ccm-characteristic-crossing-interior-mode-reduction-law` | | TODO |
| 7 | `ccm-characteristic-evans-boundary-infinite-rank-law` | | TODO |
| 8 | `ccm-cofinal-prime-sawtooth-incidence-law` | | TODO |
| 9 | `ccm-cofinal-weil-spectral-floor-criterion` | | TODO |
| 10 | `ccm-coherent-euler-logarithm-square-exclusion-law` | | TODO |
| 11 | `ccm-completed-quotient-weighted-schur-seam-law` | | TODO |
| 12 | `ccm-compressed-prime-shift-arithmetic-complement-law` | | TODO |
| 13 | `ccm-constrained-endpoint-euler-response-constant` | | TODO |
| 14 | `ccm-countable-log-chirp-renormalization-law` | | TODO |
| 15 | `ccm-critical-mellin-defect-abscissa-rh-law` | | TODO |
| 16 | `ccm-diagonal-fock-polar-prime-mellin-incidence-law` | | TODO |
| 17 | `ccm-endpoint-oscillation-poisson-tail-bound` | | TODO |
| 18 | `ccm-euler-gamma-radon-nikodym-frame-law` | | TODO |
| 19 | `ccm-euler-observability-relative-index-allocation-law` | | TODO |
| 20 | `ccm-euler-pick-logderivative-transfer-boundary-law` | | TODO |
| 21 | `ccm-evans-gram-requires-determinant-line-lift` | | TODO |
| 22 | `ccm-exact-finite-aperture-first-row-vanishing` | | TODO |
| 23 | `ccm-exact-high-radial-first-row-bv-bound` | | TODO |
| 24 | `ccm-exact-radial-nonstationary-sector-bound` | | TODO |
| 25 | `ccm-exterior-inverse-symbol-graph-norm-law` | | TODO |
| 26 | `ccm-exterior-range-observability-law` | | TODO |
| 27 | `ccm-finite-prime-parity-hankel-carrier` | | TODO |
| 28 | `ccm-fredholm-schur-resolvent-carrier-law` | | TODO |
| 29 | `ccm-galerkin-cofinal-diagonal-transfer` | | TODO |
| 30 | `ccm-gamma-damped-cauchy-frame-trace-law` | | TODO |
| 31 | `ccm-gauss-paired-quantized-differential-incidence-law` | | TODO |
| 32 | `ccm-generic-ground-separating-incidence-law` | | TODO |
| 33 | `ccm-growing-aperture-mellin-determinant-transfer` | | TODO |
| 34 | `ccm-hankel-boundary-relative-trace-four-unit-law` | | TODO |
| 35 | `ccm-hankel-gap-trace-slope-rh-criterion` | | TODO |
| 36 | `ccm-higher-subset-covariance-fock-lift` | | TODO |
| 37 | `ccm-infinitesimal-half-unit-cauchy-seam-law` | | TODO |
| 38 | `ccm-infinitesimal-real-euler-ray-logderivative-index-law` | | TODO |
| 39 | `ccm-leading-endpoint-archimedean-log-law` | | TODO |
| 40 | `ccm-limiting-radial-first-row-weber-bound` | | TODO |
| 41 | `ccm-log-symbol-dirichlet-exterior-reconstruction-law` | | TODO |
| 42 | `ccm-logderivative-closed-two-channel-graph-law` | | TODO |
| 43 | `ccm-parity-split-evans-gram-law` | | TODO |
| 44 | `ccm-poisson-jensen-outer-defect-rh-law` | | TODO |
| 45 | `ccm-polar-euler-frame-minus-level-law` | | TODO |
| 46 | `ccm-prime-free-aperture-characteristic-pair-law` | | TODO |
| 47 | `ccm-prime-log-crowding-separating-margin-law` | | TODO |
| 48 | `ccm-prime-source-ground-incidence-response` | | TODO |
| 49 | `ccm-prolate-endpoint-jet-resummation-law` | | TODO |
| 50 | `ccm-quartet-resolvent-bilateral-polarization-law` | | TODO |
| 51 | `ccm-radial-dilation-divisibility-carrier` | | TODO |
| 52 | `ccm-radial-prime-first-row-reduction` | | TODO |
| 53 | `ccm-radial-prolate-global-defect-measure` | | TODO |
| 54 | `ccm-radial-prolate-two-scale-boundary-carrier` | | TODO |
| 55 | `ccm-rational-residual-finite-evans-matrix-law` | | TODO |
| 56 | `ccm-rayleigh-excess-determinant-transfer` | | TODO |
| 57 | `ccm-rayleigh-transfer-collapses-to-spectral-floor` | | TODO |
| 58 | `ccm-real-euler-ray-loewner-index-law` | | TODO |
| 59 | `ccm-real-spectral-loggraph-transverse-vanishing-law` | | TODO |
| 60 | `ccm-rectangular-critical-mellin-tent-floor-law` | | TODO |
| 61 | `ccm-rectangular-subpower-lower-floor-rh-law` | | TODO |
| 62 | `ccm-relative-logderivative-coordinate-negative-index-law` | | TODO |
| 63 | `ccm-restricted-weil-square-evans-determinant-law` | | TODO |
| 64 | `ccm-safe-kernel-diagonal-fock-lift-rh-law` | | TODO |
| 65 | `ccm-screw-null-global-log-regularity-law` | | TODO |
| 66 | `ccm-shift-covariant-pole-divisor-capacity-law` | | TODO |
| 67 | `ccm-sonin-log-position-edge-trace-correction-law` | | TODO |
| 68 | `ccm-sonin-three-grade-relative-carrier-law` | | TODO |
| 69 | `ccm-source-normalized-nonschatten-birman-schwinger-line-law` | | TODO |
| 70 | `ccm-spectral-parameter-evans-completion-carrier-law` | | TODO |
| 71 | `ccm-suzuki-deficiency-line-zero-shift-floor-equivalence` | | TODO |
| 72 | `ccm-transverse-index-trace-slope-coercivity-law` | | TODO |
| 73 | `ccm-unit-riesz-markov-virial-landau-law` | | TODO |
| 74 | `ccm-unit-riesz-mobius-wavelet-reduction` | | TODO |
| 75 | `ccm-universal-boundary-laplace-frame-saturation-law` | | TODO |
| 76 | `ccm-weierstrass-stabilized-square-evans-line-law` | | TODO |
| 77 | `ccm-weil-exterior-tail-quotient-gate` | | TODO |
