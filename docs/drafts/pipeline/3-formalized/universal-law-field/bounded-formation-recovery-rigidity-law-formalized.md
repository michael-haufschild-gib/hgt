# Bounded formation--recovery rigidity law — formalized

- **ID:** ULF-TAFM-30
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `docs/drafts/pipeline/2-fully-proven/universal-law-field/bounded-formation-recovery-rigidity-law.md`
- **Lean module:** `GaloisForLFunctions.HTGeometry.BoundedFormationRecoveryRigidity`
- **Capstone:** `boundedFormationRecoveryRigidityLaw`

## Certified content

`isSequentiallyClosableBetween_of_bounded_factorization` proves, for arbitrary real normed source,
formation, and target spaces, that exact factorization through bounded ingress and egress forces
sequential closability. `isSequentiallyClosableBetween_add_boundedFactor_iff` proves invariance
under every bounded completed-source correction, making nonclosability a class modulo bounded
coboundaries. The codiagonal specialization proves: for every complex normed
intermediate space `E`, bounded formation
`load : ell^2 -> E` and bounded recovery `recover : E -> C` cannot recover a constant codiagonal
on every finite packet unless its coefficient is zero. Hence the earlier formation-graph
regularization necessarily moves unbounded scale into its load.

## Audit

- scratch proof with arbitrary intermediate normed space: PASS
- `lake env lean GaloisForLFunctions/HTGeometry/BoundedFormationRecoveryRigidity.lean`: PASS
- `lake build GaloisForLFunctions.HTGeometry.BoundedFormationRecoveryRigidity`: PASS
- `#print axioms`: only `propext`, `Classical.choice`, `Quot.sound`
- imports wired into `HTGeometry/UniversalLawField.lean` and `HTGeometry.lean`; umbrellas not built

## RH consequence

This is a selector mechanism conditional only on one concrete source construction: derive the
actual pre-divisor Xi codiagonal through one common completion with bounded formation and bounded
recovery. Existing route-independent stratification then turns the forced zero coefficient into
RH. Unbounded or topology-changing one-way regularizations are excluded as information-losing
gauges.
