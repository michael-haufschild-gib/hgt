# Gauge-covariant resolution action -- Lean certification

- **ID:** ULF-TAFM-5
- **Paper card:**
  `docs/drafts/pipeline/2-fully-proven/universal-law-field/topologically-admitted-formation-mechanics/gauge-covariant-resolution-action-composition-curvature-and-detector-transfer-law.md`
- **Lean module:** `GaloisForLFunctions.HTGeometry.TopologicallyAdmittedGaugeAction`
- **Umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`
- **Status:** `[LEAN-CERTIFIED CORE]` `[NO PROJECT AXIOMS]` `[NOT RH]`

## Certified mechanism

Lean certifies a path law rather than an intrinsic cost assigned to one presentation:

1. resolution arrows compose and their path budgets are submultiplicative;
2. positive local gauge rescaling moves cost between adjacent arrows by an exact endpoint ratio;
3. every internal gauge cancels from the complete path budget;
4. endpoint-fixed path action is gauge invariant;
5. composition excess defines a nonnegative multiplicative curvature ratio and nonnegative log
   curvature;
6. additive tension is invariant under vertex-potential gauge change and obeys an exact two-cocycle
   identity.

Thus edge amplification is coordinate data; complete endpoint-fixed action and composition defect
are invariant data.

## Certified declarations

- `ResolutionArrow.comp_norm_le` and `pathAction_le`;
- `rescale_norm` and `rescale_path_budget`;
- `rescale_path_budget_source_fixed`;
- `one_le_curvatureRatio` and `logCurvature_nonneg`;
- `tensionCurvature_gauge_invariant`;
- `tensionCurvature_two_cocycle`.

## Formal boundary

Abstract path action and curvature are certified. Concrete seminormed detector-transfer
realizations and the Bernoulli countermodel remain paper-only. No source-native arithmetic bound or
RH selection consequence is asserted.

## Verification

Foreground checks:

```text
lake env lean GaloisForLFunctions/HTGeometry/TopologicallyAdmittedGaugeAction.lean
lake build GaloisForLFunctions.HTGeometry.TopologicallyAdmittedGaugeAction
```

Targeted leaf build passed. Module is imported by `HTGeometry.UniversalLawField`; umbrella was not
built. A `/tmp` `#print axioms` audit reports only `propext`, `Classical.choice`, and `Quot.sound`.
