# Source-conjugate reflection orbit law — Lean certification

- **Paper card:**
  `../../../2-fully-proven/universal-law-field/orbit-generated-reflection-properness-mechanics/source-conjugate-reflection-orbit-tightness-recurrence-and-lifted-action-selection-law.md`
- **Lean module:**
  `GaloisForLFunctions.HTGeometry.ConstitutiveOrbitGeneratedReflectionProperness`
- **Umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`
- **Status:** `[LEAN-CERTIFIED FINITE CYCLIC CORE] [NO SORRY] [NO NEW AXIOMS]`

## Certified surface

| paper mechanism | Lean declaration |
|---|---|
| coordinate reflection fixes one sector and negates its complement | `coordinateReflection_apply_same`, `coordinateReflection_apply_ne` |
| every generated coordinate reflection is involutive | `coordinateReflection_involutive` |
| each reflection preserves Euclidean source energy | `coordinateEnergy_coordinateReflection` |
| reflection defect is supported on exactly one generated sector | `coordinateReflectionDefect_apply` |
| one complete orbit has exact tight work `4 E` | `orbitReflectionCycleWork_eq_four_energy` |
| complete generated family has zero common odd sector | `coordinateReflection_joint_odd_iff` |
| zero cycle work selects neutral state | `orbitReflectionCycleWork_eq_zero_iff` |
| repeated closed cycles accumulate exactly linear marked work | `repeatedOrbitReflectionWork_eq` |
| bounded-zero marked execution selects neutral state | `repeatedOrbitReflectionWork_all_zero_iff` |
| combined theorem surface | `orbitGeneratedReflectionProperness_capstone` |

## Exact boundary

Lean certifies the finite cyclic coordinate model with no analytical assumptions: one generated
observer cycle is a tight reporter with bound four, has trivial common odd sector, and repeated
observer returns accumulate marked work linearly.  The paper's general Hilbert-space identity,
fusion-frame classification, common recovery-kernel lift, and bilateral-shift completeness-without-
properness countermodel remain dependency-closed paper proofs, not claims of this Lean module.
