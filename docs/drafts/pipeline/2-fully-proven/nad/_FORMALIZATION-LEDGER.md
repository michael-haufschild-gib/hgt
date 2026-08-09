# `nad` folder — unconditional Lean formalization ledger

Working ledger for promoting every card in `2-fully-proven/nad` to `3-formalized/nad`.
A card is promoted only when its numbered statements are unconditional Lean theorems, the
modules are wired into an area umbrella, the axiom audit reports only `propext`,
`Classical.choice`, `Quot.sound`, and a `<id>-formalized.md` companion is issued.

| # | Card | Status | Notes |
|---|---|---|---|
| 1 | `hypertranscendental-phase-infinite-topological-charge-rank` | **PROMOTED** | 6 new modules: `RealExponentialPolynomial`, `RealConstantCoefficientAnnihilator`, `AnseloneKorevaarTranslationRank`, `EntireExponentialCompositionDA`, `ActiveChargeRankHypertranscendence`, `ChargeRankDressingExamples` |
| 2 | `affine-jet-packet-collision-completeness` | TODO | |
| 3 | `asymmetric-binary-tree-channel-rg-clock-hypertranscendence` | TODO | |
| 4 | `bethe-padic-holographic-rg-clock-hypertranscendence` | TODO | |
| 5 | `cofinal-cholesky-carrier-selection-threshold-law` | TODO | |
| 6 | `compact-local-form-factor-hypertranscendence-forcing` | TODO | |
| 7 | `constrained-prolate-continuous-polar-charge-law` | TODO | |
| 8 | `diamond-ising-da-scheme-rg-generation-hypertranscendence` | TODO | |
| 9 | `diamond-ising-family-rg-generation-hypertranscendence` | TODO | |
| 10 | `explicit-digamma-herglotz-universal-palette` | TODO | |
| 11 | `finite-jet-aperture-complete-germ-closure-law` | TODO | |
| 12 | `gauss-paired-quasi-inner-channel-schatten-depth-law` | TODO | |
| 13 | `hausdorff-positive-higher-spin-cdd-cone` | TODO | |
| 14 | `hypertranscendental-collision-phase-complexity-production` | TODO | |
| 15 | `identity-zero-componentwise-pauli-modular-nuclearity` | TODO | |
| 16 | `incommensurable-gamma-orbit-free-quasianalyticity` | TODO | |
| 17 | `indeterminate-moment-fiber-maximal-translation-ht` | TODO | |
| 18 | `kolchin-exchange-cocycle-obstruction` | TODO | |
| 19 | `moment-polynomial-blind-resolvent-complete-boundary-splitting` | TODO | |
| 20 | `neutral-gamma-ratio-full-differential-boundary-depth-law` | TODO | |
| 21 | `nevanlinna-boundary-bauer-retract-maximal-ht` | TODO | |
| 22 | `nonautonomous-kolchin-frequency-budget-law` | TODO | |
| 23 | `one-species-hypertranscendental-elastic-saturation` | TODO | |
| 24 | `open-family-hypertranscendental-cdd-qft` | TODO | |
| 25 | `pick-defect-finite-selector-maximal-ht-phase-law` | TODO | |
| 26 | `postselected-qubit-clock-integrability-fracture` | TODO | |
| 27 | `prime-log-jump-sonin-mellin-grade-frame` | TODO | |
| 28 | `projective-constraint-topological-capacity-phase-law` | TODO | |
| 29 | `projective-hurwitz-one-over-forty-two-phase-transition` | TODO | |
| 30 | `q-ladder-reflectionless-reciprocal-jost-qft` | TODO | |
| 31 | `sectoral-kolchin-signature-quantum-fields` | TODO | |
| 32 | `signed-archimedean-gamma-orbit-charge-phase-law` | TODO | |
| 33 | `singular-autonomous-ade-kolchin-frequency-law` | TODO | |
| 34 | `singular-maximal-ht-schur-defect-collapse-law` | TODO | |
| 35 | `singular-maximal-ht-toeplitz-weld-graph-saturation` | TODO | |
| 36 | `spectral-type-stratified-moment-fiber-maximal-ht` | TODO | |
| 37 | `two-state-fermionic-zero-intrinsic-mixing-rigidity` | TODO | |
| 38 | `wedge-pfg-four-point-exchange-carrier` | TODO | |
| 39 | `xi-euler-ray-two-node-response-barrier` | TODO | |
| 40 | `xi-physical-prime-log-aperture-fusion-cross-kernel` | TODO | |
| 41 | `xi-schur-inverse-limit-atomic-condensation-law` | TODO | |
| 42 | `identity-zero-componentwise-pauli-modular-nuclearity` (dup guard) | — | |

## Reusable infrastructure created here

- `HTGeometry/RealExponentialPolynomial.lean` — `expPolySpace`, `expPolySpaceC`, `polyExp`,
  `polyExpC`, first-order inhomogeneous solve, homogeneous law.
- `HTGeometry/RealConstantCoefficientAnnihilator.lean` — `smoothSubmodule`, `smoothDerivLM`,
  `realConstCoeffOp`, `Polynomial.aeval` operator calculus, both directions of the
  constant-coefficient solution space.
- `HTGeometry/AnseloneKorevaarTranslationRank.lean` — `realTranslate`, `translationSpan`,
  `exists_eval_separating`, Anselone–Korevaar.
- `HTGeometry/EntireExponentialCompositionDA.lean` — `differentiallyAlgebraic_cexp_comp`.
- `HTGeometry/ActiveChargeRankHypertranscendence.lean` — `eq_of_eqOn_real` (real-axis identity
  theorem), `differentiallyAlgebraic_of_mem_expPolySpaceC`.
