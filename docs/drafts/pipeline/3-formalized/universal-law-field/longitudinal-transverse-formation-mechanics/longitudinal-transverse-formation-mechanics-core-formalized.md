# Longitudinal--transverse formation mechanics core — formalized

- **ID:** ULF-LTFM-2-LEAN
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper parent:**
  `../../../2-fully-proven/universal-law-field/longitudinal-transverse-formation-mechanics/longitudinal-transverse-source-fusion-mixing-defect-and-selection-gate-law.md`
- **Lean module:** `GaloisForLFunctions.HTGeometry.LongitudinalTransverseFormationMechanics`
- **Status:** [LEAN-CERTIFIED CORE] [UMBRELLA WIRED] [NO AXIOMS ADDED]
  [EXACT CONSERVATION] [THREE-ORGAN FUSION] [SELECTION GATE] [NOT RH]

## Certified surface

Lean proves:

1. a marked codiagonal section splits every source into longitudinal coordinate and transverse
   radical;
2. applying an intervention and then the codiagonal obeys the exact conservation identity
   `output = mixing defect + section response`;
3. identically zero mixing is equivalent to preservation of the codiagonal kernel;
4. a no-mixing intervention whose section action is scalar can only rescale the longitudinal
   response;
5. any linear intervention applied after scalar divisor formation has zero output at a zero of
   that scalar;
6. the literal complete-resolution `ell^1` source fuses to its prescribed pole-unit factor;
7. endpoint fusion gives the exact corrected scale response;
8. arbitrary endpoint-dependent transverse perturbations are invisible to that response;
9. depth-weighted successive formation equals accumulated longitudinal deficit plus an exact
   terminal flux;
10. the literal complete-resolution packet realizes that law with reciprocal-zeta deficits;
11. the first successor change is an exact nonzero-mixing witness.

Principal declarations:

- `sourceSplitRadical_add_section`;
- `longitudinal_intervention_conservation`;
- `mixingDefect_zero_iff_preserves_kernel`;
- `noMixing_scalar_longitudinal_action`;
- `linear_intervention_zero_fibre`;
- `sourceFusionCodiagonal_completeResolutionFormedSource`;
- `completeResolutionFormedSource_scaleResponse`;
- `completeResolution_scaleResponse_transverse_blind`;
- `weighted_successiveFormation_conservation`;
- `completeResolution_weightedFusion_conservation`;
- `weighted_successiveFormation_one_ne_zero`.

## Exact boundary

Lean certifies the split-source mechanism, its literal complete-shell realization, and a canonical
finite source-generated depth mixer.  It does not prove cofinal closed-operator admission for that
unbounded generator, reflected analytic admission, or RH.  Nonzero mixing is only a necessary
selection gate.

## Verification

- direct command:
  `lake env lean GaloisForLFunctions/HTGeometry/LongitudinalTransverseFormationMechanics.lean`;
- leaf audit:
  `lake build GaloisForLFunctions.HTGeometry.LongitudinalTransverseFormationMechanics`;
- umbrella audit:
  `lake build GaloisForLFunctions.HTGeometry.UniversalLawField`;
- temporary `#print axioms` audit reports only `propext`, `Classical.choice`, and `Quot.sound`;
- no `sorry`, `admit`, project `axiom`, `opaque`, or `unsafe` declarations occur in the module.

## Log

- 2026-08-11 — split reconstruction, mixing conservation, kernel-preservation classification,
  scalar no-mixing law, complete-shell fusion, pole-unit response, and transverse blindness
  elaborated in Lean.
- 2026-08-11 — finite depth-generation conservation, literal reciprocal-zeta deficit landing,
  and first-successor nonzero mixing elaborated in Lean.
