# Suzuki v2 corrected convergence formulations (2026-08-19)

Lean module: `GaloisForLFunctions.RHTower.SuzukiV2SphericalConvergence`.

Definitions:
- `SuzukiV2PoleFreeConvergenceOn Ω W`: Ω open/preconnected, contains 0 and full XiC divisor, target analytic on Ω, local uniform W→target, eventual entire approximants and real zeros.
- `EventuallyZeroFreeOnCompacta W Ω`: necessary reciprocal-chart guard.
- `SuzukiV2SphericalAtlasCharacteristicLimitWall`: finite chart plus open infinity chart covering C, analytic reciprocal target, local uniform reciprocal convergence, compactwise eventual zero-freeness.

Key correction: pole-free domain cannot be defined as denominator-nonzero locus because multiple Xi zeros may be common numerator/denominator zeros with removable quotient zero. Reciprocal convergence alone is also invalid because Lean totalizes inversion (`0⁻¹=0`), confusing zero with infinity; eventual zero-freeness on infinity-chart compacta fixes this.

Theorems:
- `suzukiV2MeromorphicCharacteristicLimitWall_iff_exists_poleFreeConvergenceOn`
- `suzukiV2SphericalAtlasCharacteristicLimitWall_implies_meromorphicWall`
- `suzukiV2SphericalAtlasCharacteristicLimitWall_implies_riemannHypothesis`

Direct Lean and targeted module build pass; #print axioms only propext/Classical.choice/Quot.sound. Wired into RHTower umbrella, umbrella not built. Paper proof: `docs/drafts/pipeline/2-fully-proven/suzuki-v2-spherical-atlas-convergence.md`. Actual producer existence remains open.