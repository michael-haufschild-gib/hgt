# Top-level `2-fully-proven` → stage 3 — formalization ledger

Scope: the **top-level** `.md` cards of `docs/drafts/pipeline/2-fully-proven` only
(subfolders `computations/`, `constraint-relativity/`, `new_scientific_knowledge/`,
`nomological-geometry-and-dynamics/`, `not_new_scientific_knowledge/`, `universal-law-field/`
are out of scope — other agents own them).

Rules in force: unconditional Lean only (no `sorry`, no added axiom, no hypothesis standing for an
analytic input); never full builds nor umbrella builds — `lake env lean <file>` to check, `lake build
<module>` only for oleans a scratch needs; wire new modules into the area umbrella import list
without building it; search the corpus (`scripts/formal_tools.py research`) before writing anything.

## Start state (2026-08-21): 22 cards

## Promoted

| date | card | evidence |
|---|---|---|
| 2026-08-21 | `suzuki-v2-spherical-atlas-convergence` | `RHTower/SuzukiV2SphericalConvergence.lean` — 3 theorems, axiom-clean, wired |
| 2026-08-21 | `suzuki-v2-actual-projective-characteristic` | `RHTower/SuzukiTaV2ProjectiveCharacteristic.lean` — Theorems A/B/C, axiom-clean, wired |

## In progress

**`fixed-shell-angular-dephasing-static-local-plateau-law`** — root of the static-local cluster
(blocks `stabilizer-seeded`, `cubic-phase-seeded`, `all-replica-static-centralizer`, and weak-cut
Theorem C).  2026-08-21: closed the first of its two remaining Theorem-C inputs — the easy-circuit
tube is now proved closed in the angular-phase bundle, via three new modules
`HTGeometry/LagrangeSpectralProjector.lean`, `HTGeometry/SpectralBundleCaptureTube.lean`,
`HTGeometry/EvolvedStateBundlePairing.lean` (all axiom-clean, umbrella-wired, olean-built).

Remaining gap, located exactly: `(23)`/`(24)` live on the **Pauli** coefficient shell
(`pauliEnsemble w`) while `(16)`/`(17)` live on the **leaf-extended endpoint-complete architecture**
(`physicalEndpointCompleteQubitPath`, whose `PhysicalState` is only pinned up to cardinality because
it is produced by `Classical.choose`).  The assembly needs both on one ensemble.  The cheapest route
found so far: realize the *concrete* `n`-qubit Pauli path as a
`PhysicallyRealizedEndpointCompleteSystem` (concrete `PhysicalState = Fin n → Bool`, path tree,
one-site endpoint probe), so that `exists_leafLocal_simple_energy_witness` lands on the concrete
local-Hamiltonian submodule; then the `hwit`/`hsimple` inputs of
`tendsto_integral_exp_sortedSpectralAction_zero_of_simple_of_energy_witness` transfer to any
trace-orthonormal basis of the same real span, in particular to the Pauli basis (both hypotheses
depend only on the span, since `∑_a θ_a² = Tr(H²)/c`).

**`capacitary-observer-sector-excision-law`** — 2026-08-21: Theorems G, H, I, `(11aa)`, `(11ab)`
closed with four new modules (`CapacitySoftMinLaw`, `CompletedPhaseAccessibilityPlateau`,
`PartitionDivergenceBounds`, `CapacityEntropyBudget`).  Corollaries I.2 and J.1 closed the same day
with `GeometricCircuitCollision`.  Remaining: Corollary I.1's physical-time transfer (unique
ergodicity + the phase-coherence target bound), Corollary A.3, `(8c)`, `(11be)`, and — gated on the
fixed-shell card — Corollary I.3 and Theorem K.

**`computable-static-local-exponential-state-complexity-law`** — 2026-08-21: `(5)`, `(12)`, `(13)`,
`(14)`, the completed-time circuit bound behind `(6)` and the eigenbasis coordinate change are
closed with `CompletedTimeCircuitDensity`, `GaussianGoodCoefficientSet`, `CircuitDictionaryCounting`
(plus a strengthening of `GaussianBoxMass`).  Remaining: the instantiation wiring of Theorem A
(centred-time transport + dictionary in eigencoordinates) and all of Theorem B.  **Not gated on the
fixed-shell card** — it lives on the Gaussian Pauli ensemble, where `(23)`/`(26)` are available.

## Open (20)

algebraic-two-local-instant-exact-complexity, all-replica-static-centralizer-planar-separation-law,
arithmetic-static-local-hardness-recurrence-window-law, capacitary-observer-sector-excision-law,
capacity-compatible-fast-forwardable-incubation-law,
circuit-complexity-selection-synthesis-divergence-law,
codimension-forced-complexity-onset-moment-divergence-law,
computable-static-local-exponential-state-complexity-law,
cubic-phase-seeded-static-local-full-scale-plateau-law, cusp-spectrum-radius-law,
determinant-defect-completion-law, fixed-shell-angular-dephasing-static-local-plateau-law,
local-chain-metric-recurrence-exponents, onset-recurrence-dimension-independence-law,
route-e-cofactor-amplified-e3-token-supply, route-e-forbidden-support-e3-stability,
schanuel-defects-algebraic-coefficient-independent, schanuel-stage-two-defect-slope-normal-form,
stabilizer-seeded-static-local-double-exponential-plateau-law,
weak-cut-complexity-onset-capacity-separation-law
