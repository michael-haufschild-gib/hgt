# Sonin aperture principal cyclic-mass conservation law — formalized

- **ID:** `sonin-aperture-principal-cyclic-mass-conservation`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Scientific status:** `[LEAN-PROVED] [SOURCE THEOREM] [NOT RH]`
- **Paper proof:**
  `../../2-fully-proven/new_scientific_knowledge/sonin/sonin-aperture-principal-cyclic-mass-conservation.md`
- **Status:** unconditional; no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe`

## Lean modules

- `formal/GaloisForLFunctions/RHTower/SoninApertureRestrictionDefect.lean`
- `formal/GaloisForLFunctions/RHTower/SoninApertureCyclicMassConservation.lean`
- `formal/GaloisForLFunctions/RHTower/SoninLayerWindowNormalForm.lean`
- `formal/GaloisForLFunctions/RHTower/SoninEulerTripleShellOverlap.lean`

The terminal-test side of `(13)` additionally uses
`SoninAperturePacketCurvatureTrace.lean`, `SoninUnboundedSourcePacket.lean`,
`SoninBurnolCompletionNoFloor.lean`, `SoninFixedChannelNoFloor.lean`,
`SoninChannelAnnulusBound.lean`, `SoninCompletionSummabilityCriterion.lean`,
`SoninCouplingEnergyGrowth.lean`, and `SoninBurnolConductorNoFloor.lean`.  The paper card carries
the full statement-to-declaration table.

## Formal theorem chain

1. `evenSoninApertureRestrictionDefect_compressed_cocycle` proves exact functorial restriction
   with compression of the earlier increment.
2. `evenSoninApertureRestrictionDefect_principalRelative_cocycle` proves additive flatness modulo
   the exact relative ideal in every strict common crossing chamber.
3. `evenSoninApertureRestrictionCurvature_memSchattenClass_one` proves that all residual path
   curvature is trace-class.
4. `soninScaleOneShellWindow_operator` proves exact scale-one live-shell realization.
5. `soninApertureTotalLayerWindow_operator_eq_retained_add_lost` proves exact retained/lost
   operator conservation.
6. `soninLiveWindowCyclicLogWeight_apertureCyclicLostLayer` identifies lost mass with
   `log b-log a`.
7. `soninAperture_cyclicMass_conservation` proves retained plus lost mass equals `log r`.
8. `soninAperture_cyclicMass_cocycle` proves path additivity.

## Verdict

The earlier relative-ideal cofinalization remains impossible: lost layers are genuinely
noncompact.  But the stronger enlarged-principal obstruction is false.  Existing Sonin normal
states already carry those layers, and their cyclic mass is exactly conserved.

The one aperture datum this left — the ordinary trace of the trace-class curvature counterterm — is
now settled, and negatively.  `evenBurnolConductorChannel` in `SoninBurnolConductorNoFloor.lean` is
the full Burnol conductor, logarithm of position plus logarithm of frequency at independent and
arbitrary tower heights, and
`not_bddBelow_soninCompletedPacketValueVar_burnolConductorFamily` shows its contribution on the
source packets is a constant plus a logarithm of the scale.  The curvature trace it must cancel is
minus a coupling energy that grows linearly in the scale.  So the terminal test `(13)` resolves to
its second branch: an unconditional unbounded-below sequence survives the Burnol subtraction in
every form, and the Suzuki--Burnol weld is retired.

## Verification state

- direct `lake env lean` passed on every module listed above;
- `#print axioms` on all 23 declarations realizing `(1)`–`(12)`, and on the 23 declarations named
  by the paper card for the terminal test `(13)`, returns only `propext`, `Classical.choice`, and
  `Quot.sound`;
- every module is imported by `GaloisForLFunctions.RHTower`;
- no `sorry`, `admit`, project `axiom`, `opaque`, or `unsafe` declaration is introduced.
