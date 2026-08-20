# Cohomological packet formation mechanics — Lean certification (folder record)

All five cards of this folder are Lean-certified, umbrella-wired and axiom-clean.

| Card | Lean module(s) |
|---|---|
| `coinduced-degree-lowering-exact-reporter-and-global-formation-recovery-law` | `HTGeometry.ConstitutiveCohomologicalDegreeLowering`, `HTGeometry.ConstitutiveCanonicalCoinducedReporter`, `HTGeometry.ConstitutivePacketDegreeLoweringFusion` |
| `plucker-packet-central-commutator-reconstruction-and-h1-degree-wall-law` | `HTGeometry.ConstitutiveCohomologicalPacketFormation` |
| `unitary-jordan-collapse-and-canonical-coinduced-hilbertization-fracture-law` | `HTGeometry.ConstitutiveUnitaryJordanFormationFracture` |
| `unitary-reflection-functor-jordan-horizon-carry-and-derived-formation-persistence-law` | `HTGeometry.ConstitutiveUnitaryReflectionPersistence` |
| `universal-unitary-formation-radical-cofinal-horizon-extinction-and-properness-law` | `HTGeometry.ConstitutiveUnitaryFormationRadical` |

## Verification (2026-08-20)

Each module was re-elaborated from the tree with a bare `lean` on the project `LEAN_PATH`
(no lake lock, no full or umbrella build) — **0 errors** in all seven files — and every one of the
**91** top-level `theorem`/`lemma` declarations across them was audited with `#print axioms`:
**no nonstandard axiom**, only `propext`, `Classical.choice`, `Quot.sound`.  All seven modules are
imported by `GaloisForLFunctions.HTGeometry.UniversalLawField`.

Claim-by-claim coverage checked against the cards:

* `(DL.3)`, `(DL.5)`, `(DL.8)`, `(DL.10)`–`(DL.15)`:
  `cohomologicalTwoCocycle_right_normalized_of_left`,
  `coinducedFormationTransgression_add`,
  `cohomologicalTwoCocycle_recovered_from_transgression`,
  `coinducedFormationTransgression_coboundary_iff`, `CohomologicalExactReporter`,
  `cohomologicalLoweredCocycle_zero`/`_add`,
  `cohomologicalTwoCocycle_coboundary_of_loweredCocycle_coboundary`,
  `coinducedQuotientRightTranslateEquiv`, `canonicalCohomologicalExactReporter`,
  `cohomologicalPacketCarry_isTwoCocycle`, `_antisymmetry`,
  `_not_coboundary_of_nonconstant`, `_no_exactReporter_fixedPoint`,
  `_lowered_not_coboundary_of_nonconstant`.
* `(CP.4)`, `(CP.5)`, `(CP.7)`, `(CP.9)`, `(CP.10)`: `source_unitSource_commutator`,
  `source_unitSource_pow_commutator`, `source_unitSource_zpow_commutator`,
  `cohomologicalPacketEnergy_eq_two_mul_gram`, `cohomologicalPacket_reconstruction`,
  `cohomologicalPacketEnergy_reflect`, plus `centralElement_comm`,
  `cohomologicalPacketEnergy_eq_zero_iff_constant`, `hom_to_commGroup_erases_packet`,
  `central_coordinate_mul_defect`.
* `(UJ.4)`, `(UJ.7)`, `(UJ.11)`, `(UJ.13)`: `linearIsometryEquiv_fixed_of_fixed_displacement`,
  `linearIsometryEquiv_fixed_of_iterated_displacement_eq_zero`,
  `coinducedLinearHistoryClass_fixed`, `coinducedQuadraticHistoryClass_translate`,
  `coinducedLinearHistoryClass_add_self_ne_zero`,
  `no_faithful_unitary_realization_of_coinduced_translation`.
* `(UFR.2)`–`(UFR.3)`, `(UFR.6)`–`(UFR.9d)`, `(UFR.11)`, `(UFR.12)`, `(UFR.17)`:
  `finiteUnipotentFormationSubmodule`, `unitaryFormationRadical`,
  `reporter_intertwines_displacement_power`, `unitaryFormationRadical_le_reporter_ker`,
  `unitaryReporter_kills_offUnit_eigenvector`, `algebraicUnitaryFormationRadical`,
  `algebraicUnitaryReporterFactor(_unique)`, `unitaryReporterSemisimpleFactor(_unique)`,
  `unitaryReporter_kills_cofinalPrimitiveHistory`,
  `unitaryReporter_eq_zero_of_cofinalPrimitive_spans`, `formationGauge_formationHorizon`.
* The reflection-persistence card's own declaration list
  (`map_finiteUnipotentFormationSubmodule_le`, `map_unitaryFormationRadical_le`,
  `unitaryFormationReflectionMap`, …) is present in
  `HTGeometry.ConstitutiveUnitaryReflectionPersistence` (39 declarations).

Property-(T) is cited parent mathematics on two of the cards and is deliberately **not**
axiomatized in Lean, exactly as the cards instruct.
