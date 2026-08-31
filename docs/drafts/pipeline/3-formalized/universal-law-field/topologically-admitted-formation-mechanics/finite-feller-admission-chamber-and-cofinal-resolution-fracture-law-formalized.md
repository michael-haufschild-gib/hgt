# Finite Feller admission chamber and cofinal resolution fracture law -- Lean certification

- **ID:** ULF-TAFM-4
- **Paper card:**
  `docs/drafts/pipeline/3-formalized/universal-law-field/topologically-admitted-formation-mechanics/finite-feller-admission-chamber-and-cofinal-resolution-fracture-law.md`
- **Lean modules:**
  `GaloisForLFunctions.HTGeometry.TopologicallyAdmittedFellerAdmission`,
  `GaloisForLFunctions.HTGeometry.TopologicallyAdmittedFellerTensorFracture`
- **Umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`
- **Status:** `[LEAN-CERTIFIED]` `[NO PROJECT AXIOMS]` `[NOT RH]`

## Certified mechanism

Lean certifies the exact split between finite admission and cofinal regularity:

1. for two mutually singular full-support finite source measures, a finite pair of probability
   laws is a Feller image exactly when the target laws have the same zero set;
2. rank-two endpoint interpolation constructs every strictly positive target pair, and extension by
   zero handles every common support face;
3. every tensor power of a common-support target pair has the same zero set and is exactly
   Feller-admitted;
4. the finite Neyman--Pearson event has contrast at least one minus Hellinger affinity, affinity
   multiplies exactly under tensor powers, and distinct laws have affinity strictly below one;
5. admitted tensor decision effects have contrast tending to one, hence are not equicontinuous;
6. on a compact metric source, every family of Lipschitz certificates for those effects has
   constants tending to infinity;
7. simultaneous transport of source measures by a homeomorphism preserves the complete finite
   admission set.

This is the exact formation/properness separation needed by the field programme: every finite
experiment in the admission chamber exists, while every cofinal family approaching perfect
separation leaves each compact regularity gauge.

## Certified declarations

- `FiniteFellerKernel.exists_pushMass_eq_iff_same_zero_set`;
- `FiniteProbabilityLaw.tensorPower_same_zero_set`;
- `FiniteProbabilityLaw.fellerHellingerAffinity_pos_of_same_zero_set`;
- `FiniteProbabilityLaw.fellerHellingerAffinity_tensorPower`;
- `FiniteProbabilityLaw.one_sub_fellerHellingerAffinity_le_decisionGap`;
- `FiniteFellerKernel.exists_pushMass_eq_tensorPower`;
- `FiniteFellerKernel.tendsto_tensorDecisionEffect_contrast`;
- `FiniteFellerKernel.tensorDecisionEffects_not_equicontinuous`;
- `FiniteFellerKernel.tensorDecisionEffects_no_equicontinuous_subsequence`;
- `FiniteFellerKernel.tensorDecisionEffects_lipschitzConstants_tendsto_atTop`;
- `FiniteFellerKernel.exists_pushMass_map_homeomorph_iff`;
- `FiniteFellerKernel.exists_tensorAdmission_with_decisionEscape`;
- `mixingMean_sub_lt_one_of_fullSupport`;
- `not_equicontinuous_of_mixingMean_sub_tendsto_one`;
- `no_equicontinuous_subsequence_of_mixingMean_sub_tendsto_one`;
- `lipschitzConstants_tendsto_atTop_of_mixingMean_sub_tendsto_one`.

## Formal boundary

All paper claims `(FAC.8)`--`(FAC.15)` are declared. The functional-equation clause is formalized at
its stated topological level as invariance under simultaneous source transport by a homeomorphism.
The card makes no RH claim and does not assert projectively compatible infinite-depth kernels.

## Verification

Foreground checks:

```text
lake env lean GaloisForLFunctions/HTGeometry/TopologicallyAdmittedFellerAdmission.lean
lake env lean GaloisForLFunctions/HTGeometry/TopologicallyAdmittedFellerTensorFracture.lean
lake build GaloisForLFunctions.HTGeometry.TopologicallyAdmittedFellerTensorFracture
```

Targeted tensor/fracture leaf build passed. Both modules are imported by
`HTGeometry.UniversalLawField`; umbrella was not built. A `/tmp` `#print axioms` audit of every new
public declaration reports only
`propext`, `Classical.choice`, and `Quot.sound`.
