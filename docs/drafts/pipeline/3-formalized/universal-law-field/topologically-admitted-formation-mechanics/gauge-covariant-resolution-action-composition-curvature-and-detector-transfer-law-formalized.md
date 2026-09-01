# Gauge-covariant resolution action and detector transfer -- Lean certification

- **ID:** ULF-TAFM-5
- **Paper card:**
  `docs/drafts/pipeline/3-formalized/universal-law-field/topologically-admitted-formation-mechanics/gauge-covariant-resolution-action-composition-curvature-and-detector-transfer-law.md`
- **Lean modules:**
  `GaloisForLFunctions.HTGeometry.TopologicallyAdmittedGaugeAction`,
  `GaloisForLFunctions.HTGeometry.TopologicallyAdmittedGaugeActionDetectorTransfer`
- **Umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`
- **Status:** `[FORMALIZED]` `[NO PROJECT AXIOMS]` `[BRIDGE]` `[NOT RH]`

## Certified mechanism

Lean now certifies every dependency-closed result `(GRA.5)`--`(GRA.22)`:

1. resolution-arrow composition, multiplicative path budgets, exact gauge covariance, internal
   gauge cancellation, positive log curvature, and additive two-cocycle identity;
2. source gauge price as an infimum over admitted effects, with the exact price/action/budget
   sandwich `(GRA.15)`;
3. literal tensor Neyman--Pearson source-effect admission at Hellinger contrast `(GRA.16)`;
4. exact finite-product localization at exponent `1/(n+1)` `(GRA.17)`;
5. equality of deterministic map Lipschitz constants and pullback amplification on bounded
   real-valued Lipschitz effects `(GRA.17a)`, proved with the bounded capped-distance detector;
6. binary first-disagreement distance and inherited finite-prefix distance, including nonnegativity,
   separation, symmetry, and strong triangle inequality;
7. exact prefix projection amplification `theta^(-(d-1))` in the discrete gauge and `1` in the
   inherited prefix gauge `(GRA.18)`--`(GRA.19)`;
8. explicit quarter/three-quarter Bernoulli tensor laws and their literal `fellerDecisionEvent`
   indicator, with adjacent boundary words differing only in the last coordinate;
9. exact detector costs `1` and `theta^(-(d-1))`, exact unchanged source-cylinder cost, and exact
   transfer identity `(GRA.20)`--`(GRA.22)`;
10. a hypothesis-free capstone at `theta = 1/2` for every positive tensor depth.

## Main declarations

- `metricPullbackAmplificationBound_iff_lipschitzWith`;
- `sourceGaugePrice_le_pathAction_le_budget`;
- `tensorDecisionEffect_sourceGaugePrice_le`;
- `exists_factor_ge_sourceGaugePrice_root`;
- `binaryStreamPrefixDist_ultrametric` and `binaryWordPrefixDist_ultrametric`;
- `binaryPrefix_discrete_exactPullbackAmplification`;
- `binaryPrefix_inherited_exactPullbackAmplification`;
- `bernoulliBoundary_decision_crossing`;
- `bernoulliQuarterNPDetector_discrete_exactLipschitz`;
- `bernoulliQuarterNPDetector_inherited_exactLipschitz`;
- `bernoulliQuarterNPDetector_pullback_exactLipschitz`;
- `bernoulliQuarterHalfPrefix_detectorTransfer_unconditional`.

## Formal boundary

The source-native arithmetic bound `(GRA.23)` is explicitly open in the paper card and is not
asserted. Formalization proves the structural invariant and its hostile countermodel; it does not
claim an RH-producing arithmetic formation path.

## Verification

Foreground checks:

```text
lake env lean GaloisForLFunctions/HTGeometry/TopologicallyAdmittedGaugeActionDetectorTransfer.lean
lake build GaloisForLFunctions.HTGeometry.TopologicallyAdmittedGaugeActionDetectorTransfer
```

Targeted leaf build passed at `8658/8658`. Module is imported by
`HTGeometry.UniversalLawField`; no umbrella or full build was run. Batched `/tmp` `#print axioms`
checks on seven new capstones report only `propext`, `Classical.choice`, and `Quot.sound`.
