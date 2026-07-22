# Sonin aperture principal cyclic-mass conservation law — formalized

- **ID:** `sonin-aperture-principal-cyclic-mass-conservation`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Scientific status:** `[LEAN-PROVED] [SOURCE THEOREM] [NOT RH]`
- **Paper proof:**
  `../../2-fully-proven/new_scientific_knowledge/sonin-aperture-principal-cyclic-mass-conservation.md`

## Lean modules

- `formal/GaloisForLFunctions/RHTower/SoninApertureRestrictionDefect.lean`
- `formal/GaloisForLFunctions/RHTower/SoninApertureCyclicMassConservation.lean`

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
states already carry those layers, and their cyclic mass is exactly conserved.  Remaining
aperture datum is only the ordinary trace of the trace-class curvature counterterm.

## Verification state

- direct `lake env lean GaloisForLFunctions/RHTower/SoninApertureCyclicMassConservation.lean`
  passed;
- module imported by `RHTower.lean` and `RiemannHypothesisSOTA2026.lean`;
- final cached module build, axiom print, and lint remain for final audit.
