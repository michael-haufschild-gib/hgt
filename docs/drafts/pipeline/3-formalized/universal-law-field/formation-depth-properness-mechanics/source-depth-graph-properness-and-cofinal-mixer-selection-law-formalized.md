# Source-depth graph properness and cofinal mixer selection law — Lean certificate

- **ID:** ULF-FDPM-2-LEAN
- **Stage:** 3 — formalized in Lean 4
- **Paper parent:**
  `docs/drafts/pipeline/2-fully-proven/universal-law-field/formation-depth-properness-mechanics/source-depth-graph-properness-and-cofinal-mixer-selection-law.md`
- **Lean modules:**
  `GaloisForLFunctions.HTGeometry.ConstitutiveFormationDepthProperness` and
  `GaloisForLFunctions.HTGeometry.ConstitutiveFormationDepthCompactness`
- **Umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`
- **Status:** `[LEAN-FORMALIZED FULL] [CLOSED GRAPH] [COMPACT SUBLEVELS] [GLOBAL PROPERNESS]`
  `[COFINAL MIXER] [NO SORRY] [NOT RH]`

## Certified theorem surface

The module defines the source depth generator, codiagonal, depth work, formation gauge, and
cofinal tails. It proves:

1. `tsum_norm_le_formationGauge`: the formation gauge dominates the full source `ell^1` norm;
2. `formation_joint_kernel`: codiagonal and depth generator have trivial joint kernel;
3. `formationGauge_eq_zero_iff`: gauge zero is equivalent to neutral source history;
4. `boundedFormationGaugeOrbit_iff`: a genuinely expanding formation orbit has bounded gauge
   exactly at the neutral source;
5. `formationTail_mul_le_depthWork` and `formationTail_le_depthWork_div`: uniform cofinal-tail
   control, excluding adaptive escape;
6. `summable_weighted_completeResolutionMultiplier`: the literal complete zeta resolution lies
   in the depth-generator graph domain;
7. `tendsto_completeResolution_boundary_zero`: terminal finite-aperture flux vanishes;
8. `summable_completeResolutionDeficit`: the accumulated reciprocal-zeta deficit is absolutely
   summable;
9. `hasSum_completeResolutionDeficit_eq_weighted`: infinite formation-generation conservation;
10. `isClosed_formationDepthGraph`: the literal depth-generator graph in `ell^1 × ell^1` is
    closed;
11. `mem_formationLpGaugeSublevel_iff_forall_finiteGauge` and
    `formationLpGaugeSublevel_eq_iInter`: exact graph-gauge sublevels are intersections of
    continuous finite-aperture inequalities;
12. `isClosed_formationLpGaugeSublevel` and
    `lowerSemicontinuous_formationDepthDomainGauge`: exact lower semicontinuity in the ambient and
    induced graph-domain topologies;
13. `norm_sub_formationTruncation_eq_tail`,
    `norm_le_of_mem_formationLpGaugeSublevel`, and
    `formationTail_le_of_mem_formationLpGaugeSublevel`: exact finite-head error plus uniform norm
    and sharp tail control on every sublevel;
14. `totallyBounded_formationLpGaugeSublevel`, `isCompact_formationLpGaugeSublevel`, and
    `isCompact_formationDepthDomainGaugeSublevel`: full relative compactness, ambient closedness,
    and compactness clauses;
15. `iUnion_formationDepthDomainGaugeSublevel`: natural-number sublevels exhaust the graph domain;
16. `formationDepthCompactProperness_capstone`: bundled closed-graph, lower-semicontinuity,
    compact-sublevel, and exhaustion theorem.

All results use existing mathlib and repository theorems only. No `sorry`, `admit`, added axiom,
`opaque`, `unsafe`, `decide`, `native_decide`, `norm_num`, or `omega` occurs in the new compactness
module. Direct source elaboration, targeted module build, and umbrella elaboration pass. Audited
capstones depend only on `propext`, `Classical.choice`, and `Quot.sound`.

## Remaining selection gate

Formalization proves source-side properness. RH still requires a source-faithful conservative
comparison sending physical off-centre displacement to a nonzero formation class while bounding
its formation gauge by physical work. The present theorem makes that missing comparison precise;
it does not assume or manufacture it.
