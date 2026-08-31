# Theta-source prime-modular current field and tracial dichotomy

- **ID:** ULF-PMFM-1
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `docs/drafts/pipeline/2-fully-proven/universal-law-field/prime-modular-formation-mechanics/theta-source-prime-modular-current-field-and-tracial-dichotomy.md`
- **Lean module:** `GaloisForLFunctions.RHTower.HedenmalmThetaSourcePrimeModularCurrentField`

## Certified declarations

- `thetaPrimeModularDilation_reflection`
- `thetaPrimeModularDilation_comp_neg`
- `thetaPrimeModularDilation_commutes_current`
- `norm_thetaXiPrimeModularDilation_sq`
- `thetaXiPositivePrimeModularSpectrum_eq_univ_of_offline`
- `thetaXiPositivePrimeModularSpectrum_eq_singleton_of_onwall`
- `thetaXiPositivePrimeModularSpectrum_eq_singleton_iff`
- `thetaXiPositivePrimeModularSpectrum_dichotomy`
- `forall_thetaXiPositivePrimeModularSpectrum_eq_singleton_iff`

## Audit

- Direct elaboration: PASS
- Named leaf build: `lake build GaloisForLFunctions.RHTower.HedenmalmThetaSourcePrimeModularCurrentField` PASS (`12830/12830`)
- Axioms: only `propext`, `Classical.choice`, `Quot.sound`
- Forbidden declarations in module: none
- Umbrellas wired: `HTGeometry.UniversalLawField`, `RHTower`
- Full/umbrella build: intentionally not run
