# Hahn-label information conservation -- Lean certification

- **ID:** ULF-TAFM-6
- **Paper card:**
  `docs/drafts/pipeline/2-fully-proven/universal-law-field/topologically-admitted-formation-mechanics/hahn-label-approximation-spectrum-observer-deficit-and-tensor-convergence-law.md`
- **Lean modules:** `GaloisForLFunctions.HTGeometry.TopologicallyAdmittedHahnLabel`,
  `GaloisForLFunctions.HTGeometry.TopologicallyAdmittedMeasurableHahnLabel`
- **Umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`
- **Status:** `[LEAN-CERTIFIED CORE]` `[NO PROJECT AXIOMS]` `[MEASURABLE]` `[NOT RH]`

## New infrastructure

The measurable module builds the missing signed-measure layer instead of reducing the theorem to a
finite surrogate:

- signed current `Q.toSignedMeasure - P.toSignedMeasure`;
- canonical control law `P + Q`;
- real Radon--Nikodym Hahn density;
- exact reconstruction by vector-valued density;
- exact identification of signed-current variation with weighted density mass;
- measurable Hahn sign label and weighted label-error functional.

## Certified mechanism

For arbitrary finite measures on an arbitrary measurable space, Lean proves

\[
 \operatorname{TV}_{\rm RN}(P,Q)-J_g(P,Q)
 =\frac12\int |g-\operatorname{sgn}h|\,|h|\,d(P+Q),
 \qquad h=\frac{d(Q-P)}{d(P+Q)}.
\]

Here `J_g` is the probability-normalized signed current carried by a measurable soft label
`g : X → [-1,1]`. The identity is pointwise algebra lifted through signed Radon--Nikodym
reconstruction, not a finite computation.

Finite experiments additionally certify exact observer current pullback, stochastic-channel
current conservation, target canonical-label formation error, and serial observer-deficit
additivity.

## Certified declarations

- `currentControl_withDensity_measurableHahnDensity`;
- `variation_measurableSignedCurrent_eq`;
- `measurableHahnTV_eq_half_variation`;
- `measurableHahnTV_sub_decisionCurrent_eq_labelError`;
- `FiniteBinaryExperiment.tv_sub_decisionCurrent_eq_half_labelError`;
- `FiniteBinaryExperiment.decisionCurrent_pullLabel`;
- `FiniteBinaryExperiment.observerDeficit_serial`;
- `FiniteChannel.decisionCurrent_pullSoftLabel`;
- `FiniteChannel.half_labelError_pull_targetCanonicalLabel`.

## Formal boundary

Exact measurable regret and finite observer/channel conservation are certified. Dictionary-width
duality, continuous compact-dictionary obstruction, and tensor-product exponential convergence
remain paper-only. This certificate does not claim the arithmetic dictionary-width producer needed
for RH selection.

## Verification

Foreground checks:

```text
lake env lean GaloisForLFunctions/HTGeometry/TopologicallyAdmittedHahnLabel.lean
lake env lean GaloisForLFunctions/HTGeometry/TopologicallyAdmittedMeasurableHahnLabel.lean
lake build GaloisForLFunctions.HTGeometry.TopologicallyAdmittedHahnLabel
lake build GaloisForLFunctions.HTGeometry.TopologicallyAdmittedMeasurableHahnLabel
```

Both targeted leaf builds passed. Missing dependency oleans were built by the measurable leaf
target; no umbrella build was run. `/tmp` `#print axioms` audits of finite and measurable capstones
report only `propext`, `Classical.choice`, and `Quot.sound`.
