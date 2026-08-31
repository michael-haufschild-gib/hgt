# Finite Feller admission and cofinal resolution fracture -- Lean certification

- **ID:** ULF-TAFM-4
- **Paper card:**
  `docs/drafts/pipeline/2-fully-proven/universal-law-field/topologically-admitted-formation-mechanics/finite-feller-admission-chamber-and-cofinal-resolution-fracture-law.md`
- **Lean module:** `GaloisForLFunctions.HTGeometry.TopologicallyAdmittedFellerAdmission`
- **Umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`
- **Status:** `[LEAN-CERTIFIED CORE]` `[NO PROJECT AXIOMS]` `[NOT RH]`

## Certified mechanism

Lean certifies the exact split between finite admission and cofinal regularity:

1. for two mutually singular full-support finite source measures, a finite pair of probability
   laws is a Feller image exactly when the target laws have the same zero set;
2. rank-two endpoint interpolation constructs every strictly positive target pair, and extension by
   zero handles every common support face;
3. a continuous unit-interval effect on two full-support laws cannot have mean gap one;
4. any sequence whose mean gap tends to one is not equicontinuous and has no equicontinuous
   subsequence;
5. on a compact metric source, every family of Lipschitz certificates for that sequence has
   constants tending to infinity.

This is the exact formation/properness separation needed by the field programme: every finite
experiment in the admission chamber exists, while every cofinal family approaching perfect
separation leaves each compact regularity gauge.

## Certified declarations

- `FiniteFellerKernel.exists_pushMass_eq_iff_same_zero_set`;
- `mixingMean_sub_lt_one_of_fullSupport`;
- `not_equicontinuous_of_mixingMean_sub_tendsto_one`;
- `no_equicontinuous_subsequence_of_mixingMean_sub_tendsto_one`;
- `lipschitzConstants_tendsto_atTop_of_mixingMean_sub_tendsto_one`.

## Formal boundary

Common-support tensor-power packaging and the paper's functional-equation action are not declared
in this module. Certification covers exact finite-image classification and the full cofinal
equicontinuity/Lipschitz escape mechanism, not RH selection.

## Verification

Foreground checks:

```text
lake env lean GaloisForLFunctions/HTGeometry/TopologicallyAdmittedFellerAdmission.lean
lake build GaloisForLFunctions.HTGeometry.TopologicallyAdmittedFellerAdmission
```

Targeted leaf build passed. Module is imported by `HTGeometry.UniversalLawField`; umbrella was not
built. A `/tmp` `#print axioms` audit of classification and escape capstones reports only
`propext`, `Classical.choice`, and `Quot.sound`.
