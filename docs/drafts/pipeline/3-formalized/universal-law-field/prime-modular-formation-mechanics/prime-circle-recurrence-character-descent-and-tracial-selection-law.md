# Prime-circle recurrence character descent and tracial selection law

- **ID:** ULF-PMFM-2
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `docs/drafts/pipeline/2-fully-proven/universal-law-field/prime-modular-formation-mechanics/prime-circle-recurrence-character-descent-and-tracial-selection-law.md`
- **Lean modules:**
  `GaloisForLFunctions.HTGeometry.ConstitutiveCompactRecurrenceCharacterDescent`;
  `GaloisForLFunctions.RHTower.HedenmalmThetaSourcePrimeModularCompactRecurrenceDescent`

## Certified declarations

- `continuousAddMonoidHom_eq_zero_of_compact`
- `compactCharacterDescends_iff`
- `denseRange_primeCircleHom`
- `primeCircleRecurrenceFormation`
- `primeModularCompactRecurrenceDescent_iff`
- `thetaXiPrimeModularLogOrbit_primeLogFormationLift`
- `thetaXiPrimeModularCompactRecurrenceDescent_iff`
- `thetaXiPrimeModularCompactRecurrenceDescent_lineConj_iff`
- `forall_thetaXiPrimeModularCompactRecurrenceDescent_iff_riemannHypothesis`

## Audit

- Direct elaboration: PASS
- Named leaf build:
  `lake build GaloisForLFunctions.RHTower.HedenmalmThetaSourcePrimeModularCompactRecurrenceDescent`
  PASS
- Axioms: only `propext`, `Classical.choice`, `Quot.sound`
- Forbidden declarations in both modules: none
- Umbrellas wired: `HTGeometry.UniversalLawField`, `RHTower`
- Full/umbrella build: intentionally not run

## Mathematical boundary

Faithful dense compact recurrence exists unconditionally and preserves every finite prime history.
Exact continuous recovery of the theta-source real modular log through that completion is tracial,
and global descent is equivalent to RH.  Thus theorem supplies a closed selection interface, not an
RH proof.  Remaining producer is source-native uniform continuity of literal theta conormal
recovery in the prime-circle recurrence topology before divisor selection.
