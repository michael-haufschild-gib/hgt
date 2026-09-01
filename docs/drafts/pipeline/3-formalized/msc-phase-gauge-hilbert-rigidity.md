# MSC phase-gauge Hilbert rigidity

- **ID:** MSC-PGHR
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md` · MSC singular order transport
- **Statement:** Any coefficient-faithful positive Hilbert realization of the physical MSC source and literal overlap vector with independent unitary mode sign gauges forces `1 < Re rho`.

## Proof chain

Independent sign gauges force pairwise mode orthogonality. Normalization plus Bessel for source and overlap yields reciprocal diagonal weight `w n = ‖mode n‖²`. Exact diagonal-rigging classification then gives `1 < Re rho`, excluding every strict-right Xi zero.

## Gates

- [x] Corpus and proof-chain audit
- [x] Dependency-closed paper proof `[PROVED HERE]`
- [x] Lean proof, targeted build, axiom audit `[LEAN-PROVED]`
- [ ] Publication-ready standalone paper

## No-go closure

- **Killed:** Every coefficientwise phase-gauge-equivariant positive Hilbert MSC completion; off-diagonal Gram mixing cannot evade diagonal wall.
- **Survivor:** Gauge-breaking non-diagonal or genuinely distributional completion.
- **New invariant:** Independent coordinate-gauge unitarity collapses non-diagonal sector exactly to reciprocal diagonal rigging class.
- **Lean:** `HedenmalmGammaSewnSquarefreeFisherPhaseGaugeRiggingNoGo.lean`; capstone `strictRightXiZero_mscPhysicalOverlapSignGaugeHilbertNoGo`.
- **Audit:** Targeted build passed; theorem axioms are only `propext`, `Classical.choice`, `Quot.sound`. Generic sign-gauge orthogonality is classical; exact MSC application had no corpus/literature collision through 2026-08.
