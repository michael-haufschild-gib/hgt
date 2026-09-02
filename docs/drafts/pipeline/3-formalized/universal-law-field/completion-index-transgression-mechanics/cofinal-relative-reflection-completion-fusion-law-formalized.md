# Cofinal relative-reflection completion fusion law — Lean certification

- **ID:** `ULF-CRRCF-1`
- **Paper card:**
  `completion-index-transgression-mechanics/cofinal-relative-reflection-completion-fusion-law.md`
- **Lean module:**
  `GaloisForLFunctions.RHTower.CofinalRelativeReflectionCompletionFusion`
- **Universal-law umbrella:**
  `GaloisForLFunctions.HTGeometry.UniversalLawField`

## Certified declarations

- `tateClockCofinalTopCoefficient`: canonical reader of the new Tate top coordinate.
- `tateClockCofinalTopCoefficient_flatMinusRaw_exp`: forward naturality anomaly recovers forward
  Gamma leg.
- `tateClockCofinalTopCoefficient_flatMinusRaw_exp_neg`: reciprocal anomaly recovers reflected leg.
- `tateClockRelativeReflectionCofinalCoefficientMatrix_eq_curvedSuspension`: paired completion
  anomalies recover the full relative-reflection matrix.
- `tateClockRelativeReflectionCofinalCoefficientMatrix_sq`: exact completion Clifford law.
- `det_tateClockRelativeReflectionCofinalCoefficientMatrix`: determinant is paired Gamma
  curvature.
- `deningerIntegralRelativeReflection_determinant_eq_cofinalTate`: evaluated integral Laurent
  determinant equals completion-anomaly determinant at every stage.

## Verification

```text
lake env lean /tmp/cofinal_relative_reflection_scratch.lean
lake build GaloisForLFunctions.RHTower.CofinalRelativeReflectionCompletionFusion
lake env lean /tmp/cofinal_relative_reflection_axioms.lean
```

Scratch check, targeted module build, and axiom audit passed. Every certified theorem depends only
on `propext`, `Classical.choice`, and `Quot.sound`. Module is wired into universal-law umbrella; no
umbrella build was run.

## Exact field consequence

The universal source matrix now has a literal completion realization: it is canonical top readout
of reciprocal cofinal naturality defects. Remaining RH-bearing law is global integral strictness
of the assembled arithmetic Tate action, not another scalar detector or fitted fibre frame.
