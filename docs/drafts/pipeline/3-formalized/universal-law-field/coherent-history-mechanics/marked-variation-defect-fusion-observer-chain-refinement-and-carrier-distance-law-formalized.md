# Marked-variation fusion and carrier-distance law — Lean formalization record

- **ID:** ULF-MVD-1-LEAN
- **Source theorem:** ULF-MVD-1
- **Stage:** 3-formalized
- **Status:** [LEAN-FORMALIZED] [UNCONDITIONAL FINITE CORE]
  [GENERATION-OBSERVATION INTERCHANGE] [FOURTH-ORGAN PREDICTION]
  [NO RH PREMISE] [NO COMPUTATIONAL PROOF]
- **Lean module:**
  `GaloisForLFunctions.HTGeometry.MarkedVariationDynamics`
- **Umbrella:**
  `GaloisForLFunctions.HTGeometry.UniversalLawField`

## Certified mechanism

The Lean module defines a positive kernel as a structure whose weights carry their nonnegativity
proof.  It then certifies:

1. real and complex execution, serial composition, order preservation, and
   `|Tf| <= T|f|`;
2. marked coherent execution, positive envelope, nonnegative variation defect, and exact
   reconstruction;
3. exact packet fusion into two inherited debts plus between-packet interference;
4. exact positive-observer chain rule;
5. conservative marked refinement and its exact positive increment;
6. the generation-observation interchange identity
   `D_(ST)(fine) = S D_T(coarse) + ST(excess) + observerLoss`;
7. exact three-sector genuine/splice/interference conservation and nonnegativity;
8. scalar serial-loss telescoping, macroscopic loss-count bound, and exact-return rigidity;
9. finite probability carriers, splice mass, total variation, universal lower bound against every
   genuine-supported carrier, and an explicit genuine carrier attaining that bound.
10. mass-preserving positive marked realizations, their exact global defect budget, and the
    impossibility of strict coherent amplification beyond source variation.

The capstone declaration
`markedVariationDynamics_fusion_capstone` packages nonnegativity, reconstruction, and the
generation-observation interchange law for every conservative refinement and every pair of
positive kernels.

The fourth-organ declaration
`finiteGenuineCarrier_exactDistance` proves the exact nearest-genuine-carrier theorem without
introducing an infimum API: it gives the universal lower bound and a marked transfer witness with
equality.

## Main declarations

- `FinitePositiveKernel`
- `FinitePositiveKernel.norm_applyComplex_le`
- `FinitePositiveKernel.applyReal_comp`
- `FinitePositiveKernel.applyComplex_comp`
- `markedVariationDefect_nonneg`
- `markedEnvelope_reconstruction`
- `markedVariationDefect_observerChain`
- `markedVariationDefect_fusion`
- `MarkedRefinement`
- `markedVariationDefect_refinement`
- `markedVariationDefect_interchange`
- `markedVariationDefect_interchange_increment`
- `genuineSpliceInterference_conservation`
- `finiteObserverLoss_telescope`
- `macroscopicObserverLoss_count`
- `observerLoss_zero_before_exactReturn`
- `markedVariationDefect_totalBudget`
- `markedCoherentOutput_l1_le_envelopeMass`
- `markedRealization_strictAmplification_impossible`
- `finiteSpliceMass_le_tv`
- `finiteHistoryTV_moveSplice_eq`
- `finiteGenuineCarrier_exactDistance`
- `markedVariationDynamics_fusion_capstone`

## Exact certification boundary

Lean certifies the mechanism needed by the user-mandated sequence: a genuine fusion law across
generation, coherent cancellation, positive observation, and recurrence accounting, followed by
the exact carrier-distance prediction.

The following paper clauses are not claimed Lean-certified by this record:

1. rowwise equality-case classification by a common complex phase;
2. parent-indexed refinement plateau classification, beyond the bundled conservative-refinement
   interface;
3. the full subsequential infinite-chain recurrence theorem, beyond exact finite-return rigidity;
4. explicit matrix block-sum expansion into genuine and observer-splice paths, beyond its exact
   scalar three-sector conservation law.

These are formalization backlog, not hidden premises of the certified interchange or carrier
theorems.

## Verification

- `lake env lean GaloisForLFunctions/HTGeometry/MarkedVariationDynamics.lean`: pass.
- `lake build GaloisForLFunctions.HTGeometry.UniversalLawField`: pass, 11,612 jobs.
- token scan: no `sorry`, `admit`, project `axiom`, `opaque`, or `unsafe`.
- axiom audit of capstone/interchange/loss/carrier declarations:
  `propext`, `Classical.choice`, `Quot.sound` only.
- generated indexes refreshed; repository lint reaches this module. Global lint remains nonzero
  only for nineteen unrelated modules not wired into their RHTower/HTGeometry umbrellas.

## RH boundary

No arithmetic marked packet, Xi specialization, route identification, or RH selector occurs in the
Lean module.  A later RH application must construct a coefficient-faithful source realization of
the certified structures before invoking any selection consequence.
