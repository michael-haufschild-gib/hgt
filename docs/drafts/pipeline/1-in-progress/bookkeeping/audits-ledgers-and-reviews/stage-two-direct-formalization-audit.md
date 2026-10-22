# Direct Stage 2 unconditional Lean formalization audit

- **ID:** `stage-two-direct-formalization-audit`
- **Stage:** 1-in-progress
- **Type:** FORMALIZATION AUDIT
- **Scope:** Every Markdown card directly inside `docs/drafts/pipeline/2-fully-proven`; subfolders excluded.
- **Completion criterion:** Every exact dependency-closed paper theorem has an unconditional Lean theorem, required infrastructure, umbrella reachability, direct elaboration, final module build, clean formal lint, and audited axioms; completed cards move to Stage 3.

## Card ledger

- [x] `analytic-operational-horizon-dichotomy.md`
- [ ] `arbitrary-graph-quantum-temporal-curvature-law.md`
- [x] `ccm-first-clock-asymptotic-bohr-law.md`
- [x] `ccm-first-clock-asymptotic-bohr-torelli-law.md`
- [ ] `ccm-rational-analytic-real-descent.md`
- [x] `ccm-single-clock-complete-source-divisor-tomography.md`
- [x] `ccm-unitary-polar-source-atlas.md`
- [ ] `complete-graph-local-projective-spectral-maximality.md`
- [ ] `component-recurrence-torus-and-replica-factorization-law.md`
- [x] `countable-euler-family-sonin-gamma-xi-rees-chart.md`
- [ ] `cusp-spectrum-radius-law.md`
- [ ] `dense-arithmetic-instability-of-quantum-eternity.md`
- [ ] `disconnected-local-spectral-factorization-genericity.md`
- [x] `dissipative-quantum-return-information-transition.md`
- [ ] `field-one-spherical-weyl-multiplier-bridge.md`
- [x] `finite-contraction-temporal-boundary-law.md`
- [ ] `finite-horizon-observer-temporal-profile-stability.md`
- [x] `finite-multiset-transformation-moment-universality-law.md`
- [x] `finite-observer-generated-time-law.md` — fully formalized; moved to `3-formalized`
- [x] `finite-satake-reality-torelli-universality-law.md`
- [ ] `finite-window-replica-collision-resolution-law.md`
- [ ] `generic-two-local-spectral-monodromy.md`
- [x] `function-field-spectral-closure-universality-law.md`
- [x] `gram-weld-trilemma.md`
- [ ] `hypergraph-local-projective-spectral-factorization.md`
- [ ] `local-chain-metric-recurrence-exponents.md`
- [ ] `local-interaction-replica-collision-extremality.md`
- [ ] `mobius-fixed-current-von-mangoldt-critical-transport-weld.md`
- [x] `mobius-pluecker-normal-cone-diagonal-lift.md`
- [x] `multiple-elliptic-gamma-face-depth-rigidity.md`
- [ ] `nearest-neighbor-chain-projective-spectral-maximality.md`
- [x] `nearest-neighbor-qudit-projective-spectral-maximality.md`
- [ ] `positive-shell-koszul-cartier-obstruction-reciprocity.md`
- [x] `prime-arch-black-hole-reciprocal-spectral-cone-universality.md`
- [x] `prime-arch-cofinal-orientation-charge-universality.md`
- [ ] `prime-sieve-wold-gamma-bv-relative-character.md`
- [ ] `prime-valuation-conditioning-normalization-amplification-no-go.md`
- [ ] `prime-valuation-kakutani-polar-third-completion.md`
- [ ] `prime-winning-cech-divisor-resolution.md`
- [x] `pure-pair-normal-actuality-fracture.md`
- [x] `replica-collision-hamming-tomography-law.md`
- [x] `squarefree-euler-modular-corona-curvature-colligation.md` — promoted to `3-formalized`
- [x] `summable-nome-infinite-order-multiple-elliptic-gamma.md` — promoted to `3-formalized`
- [ ] `universal-static-choi-complexity-plateau.md`
- [ ] `weak-interaction-singular-quantum-time-expansion.md`
- [ ] `wold-shell-euler-activation-square.md`
- [x] `xi-aperture-counterterm-phase-universality-law.md`

## Active checkpoint

- 2026-08-01 — inventory opened: 45 direct Stage 2 cards. Existing Lean corpus, Stage 3 cards, and generated API are being checked before any theorem code is written. Unrelated worktree edits and active Lean jobs belong to other sessions and remain untouched.
- 2026-08-01 — exact existing theorem surface confirmed and umbrella-wired for: analytic operational horizon, countable Euler-family Sonin chart, finite contraction boundary, finite multiset transformation moments, finite Satake Torelli, function-field closure, Gram weld trilemma, replica-collision Hamming tomography, and Xi aperture counterterm phase. One batched scratch audit elaborated 14 capstones; every axiom set is `[propext, Classical.choice, Quot.sound]`. Final direct-file checks and module builds remain.
- 2026-08-01 — additional exact corpus matches found after stale card status: `CCMFirstClockAsymptoticBohrTorelli.lean`, `CCMUnitaryPolarSourceAtlas.lean` (also supplies one-clock crease--pole--frequency capstone), `MultipleEllipticGammaFacePacketDisjointness.lean`, `PrimeArchBlackHoleReciprocalSpectralConeUniversalityLaw.lean`, and `PrimeArchCofinalOrientationChargeUniversalityLaw.lean`. Axiom/direct/final audits remain.
- 2026-08-01 — material formal gaps confirmed: arbitrary-graph temporal-curvature graph induction and capstones; CCM rational analytic/cyclic descent infrastructure; dissipative bistochastic-channel bridge. These are not eligible for Stage 3 yet.
- 2026-08-01 — closed the remaining `ccm-first-clock-asymptotic-bohr-law.md` Lean gap without weakening: exact literal-source `liminf = 0`, `limsup = ccmFirstClockAsymptoticHullMax`, and intersection-of-closed-tail-images equality. Direct elaboration and final module build pass; all three new capstones audit to `[propext, Classical.choice, Quot.sound]`. An unrelated transient umbrella-lint failure was cleared before promotion.
- 2026-08-01 — repository-wide lint cleared after the concurrent umbrella update. Sequential direct elaboration passed for 18 audited modules; final `lake build <module>` passed for all 16 exact-complete capstone/dependency modules. Batched capstone audits report only `[propext, Classical.choice, Quot.sound]`. Promoted 14 exact-complete direct cards to Stage 3; 31 direct Stage 2 cards remain.
- 2026-08-01 — closed bistochastic-channel TODO without weakening: added all-level finite matrix complete positivity, positivity and adjoint preservation, two-by-two Kadison--Schwarz, trace/Frobenius identity, Hilbert--Schmidt contraction, bounded channel operator, and exact channel ceiling/dichotomy/deadline capstones. Direct elaboration, final module build, umbrella reachability, formal lint, and axiom audits pass. Promoted `dissipative-quantum-return-information-transition.md`; 30 direct Stage 2 cards remain.
- 2026-08-01 — completed UPSA-1 canonical-product seam: source-atlas copies are exactly equivalent to the complete Xi multiplicity-copy divisor, and the atlas product is the normalized centered Xi canonical product. Existing polar/critical atlas capstone plus new divisor/product capstones pass direct elaboration, final module build, umbrella reachability, lint, and axiom audit. Promoted `ccm-unitary-polar-source-atlas.md`; 29 direct Stage 2 cards remain.
- 2026-08-01 — a concurrently added direct card, `generic-two-local-spectral-monodromy.md`, entered scope; direct Stage 2 inventory returned to 30. Closed exact OC-1 Lean seam with a literal forward crease--pole--frequency proposition, complete divisor bijection/canonical product, arbitrary Stone recurrence chambers, and a stronger inverse obstruction: distinct same-divisor source coordinates admit no set-theoretic reconstruction map. Direct elaboration, module build, umbrella wiring, and axiom audit pass. Promotion waits only for repository lint to clear a concurrent unrelated unreachable-module error.
- 2026-08-01 — repository lint cleared. Promoted OC-1 after all gates passed. Closed the pure-pair
  geometric TODO without weakening: exact tangent compatibility quotient, projective normal-fiber
  quotient, determinant-one unitary `SU(3)` action, fixed subspace exactly the weak doublet,
  complex/real ranks `2/4`, and quaternionic `1+3` capstone. Direct elaboration, module build,
  umbrella reachability, lint, and axiom audit pass. A concurrently added direct card,
  `universal-static-choi-complexity-plateau.md`, entered scope; 29 direct Stage 2 cards remain.
- 2026-08-01 — closed the Möbius--Pluecker normal-cone diagonal lift without weakening: finite
  source/product transfer, fixed-aperture no-go, locally uniform Euler product, nested cofinal
  diagonal for every positive critical sequence, Gamma completion, and projectivized negative
  reciprocal square. Direct elaboration, target module build, umbrella reachability, lint, and
  axiom audit pass. Promoted `mobius-pluecker-normal-cone-diagonal-lift.md`; 28 direct Stage 2 cards
  remain before re-inventory.
