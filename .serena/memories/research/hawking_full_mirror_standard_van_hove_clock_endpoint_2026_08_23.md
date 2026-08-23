# Full theta-mirror standard van-Hove clock endpoint (2026-08-23)

New module: `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingFullMirrorVanHoveSelectionEndpoint.lean`.

Key idea: exact full Davies–Fulling eikonal amplitude contains indirect higher-order coherent paths, so finite-coupling mixing is unconditional and raw amplitude cannot equal canonical Cayley S-matrix. Build exact eikonal-fed conservative Cayley/KMS collision first, then apply standard van Hove collision clock λ^(-2). Define rate `|T(λ)|²/λ²`. Proved punctured limit

`|T(λ)|²/λ² → (ω⁴/4) |XiC(ω+a i)|²`.

Thus any sector with dark first-order theta/Xi coefficient but higher eikonal onset freezes on standard clock, even though it mixes at fixed nonzero coupling. This is physical direct-edge vs graph-connectivity distinction; inspired by Attal–Joye repeated-interaction weak-coupling limits (arXiv:math-ph/0501012), short-time quantum-walk graph-distance exponents (arXiv:1905.03914), and higher-order FGR literature.

Main declarations:
- `thetaCuspHawkingFullMirrorCayleyVanHoveRate`
- `thetaCuspHawkingFullMirrorVanHoveLimitRate`
- `tendsto_thetaCuspHawkingFullMirrorCayleyVanHoveRate`
- `tendsto_thetaCuspHawkingFullMirrorCayleyVanHoveRate_zero_of_XiC_eq_zero`
- `tendsto_thetaCuspHawkingFullMirrorCayleyVanHoveDeviationFlow`
- `thetaCuspHawkingFullMirrorVanHoveSectorMixes_iff_XiC_ne_zero`
- `riemannHypothesis_iff_thetaCuspHawkingFullMirrorStandardClockMixing`

Status: [BRIDGE] [NOVELTY UNVERIFIED], not RH proof. Remaining producer is to derive universality of one standard λ^(-2) Hawking clock across all source-labelled tilted sectors from full quantum backreaction, rather than impose it.

Verification: module compiled and .olean emitted. Main axiom audits only [propext, Classical.choice, Quot.sound]. Root RHTower umbrella import added; direct umbrella Lean check is blocked by unrelated missing `AnharmonicChebyshevCubicDescentCriterion.olean`. Full formal lint sees new module reachable but fails on unrelated pre-existing unreachable modules (EulerLogPrimePowerLaplace, FiniteCompletedFluxPassportPartnerSurjectivity, and several HTGeometry modules). docs/reports/endpoints.md updated.

Heat/OU pivot was rejected: existing Hawking KMS generator acts on resonance populations while de Bruijn heat acts on source/zero coordinate; no canonical intertwiner in corpus or audited literature. Do not assert KMS=heat without a new exact source map.
