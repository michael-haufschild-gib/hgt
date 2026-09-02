# Suzuki quadratic-rank Hilbert--Schmidt Gamma response no-go

- **ID:** CCM-FU-C27
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `../1-in-progress/irregular-stokes-robin-gamma-holonomy-coercivity.md`
- **Statement:** Pairing the actual fixed Hilbert--Schmidt Gamma feature with any uniformly operator-bounded response of rank at most `(qN)²` is `o(N)`; no such pre-Gram response can lower-semibound the Suzuki transition-core Ward defect.

## Goal

Kill the natural moving finite-rank pre-Gram response class not covered by C24--C26. This does not prove RH; it forces superquadratic effective rank, operator-norm blow-up, or a cutoff-moving/non-Hilbert--Schmidt source.

## Gates

- [x] 0 → 1: corpus-derived from actual Hilbert--Schmidt Gamma feature, ordered-pair quadratic rank, and transition-core linear rigidity
- [x] 1 → 2: fixed-source finite-rank density gives little-`o`; trace cyclicity controls fixed head
- [x] 2 → 3: `RHTower.no_suzukiCausalDepthGammaQuadraticRankHSWardProducer`; direct check, targeted build, and axiom audit pass
- [ ] 3 → 4: publication-ready standalone statement and external novelty audit

## No-go closure

- **Exact theorem:** `no_suzukiCausalDepthGammaQuadraticRankHSWardProducer` in `SuzukiCausalDepthGammaQuadraticRankHSRobinTraceNoGo.lean`.
- **Mechanism:** approximate fixed `S²` source by fixed finite rank; quadratic-rank bounded response has `O(N)` Hilbert--Schmidt norm, but arbitrary source tail makes normalized pairing vanish; fixed head is `O(1)` by trace duality.
- **Positive survivor:** superquadratic effective rank, unbounded operator norm, or cutoff-moving/non-`S²` source before Gram formation.
- **Status:** paper proof dependency-closed; Lean theorem is `¬ Nonempty`; only `propext`, `Classical.choice`, `Quot.sound`; targeted module build passes.
