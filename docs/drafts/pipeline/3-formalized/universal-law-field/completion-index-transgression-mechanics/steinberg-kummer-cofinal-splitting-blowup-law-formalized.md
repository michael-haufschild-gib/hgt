# Steinberg--Kummer cofinal splitting blowup — Lean certification

- **ID:** `ULF-SKSB-1`
- **Stage:** 3-formalized
- **Paper card:** `completion-index-transgression-mechanics/steinberg-kummer-cofinal-splitting-blowup-law.md`
- **Lean module:** `GaloisForLFunctions.RHTower.SteinbergKummerCofinalSplittingBlowup`

## Certified declarations

- `norm_deningerKummerAugmentation_le_coefficientL1`: augmentation is bounded by the exact
  coefficient `ell¹` norm.
- `deningerKummerAugmentation_secondDerivation_cell`: exact second-jet augmentation `2AB`.
- `deningerSteinbergSecondJet_coefficientL1_lower_bound`: every three-jet Bezout splitting has
  second coefficient norm at least `(2‖AB‖)⁻¹`.

## Verification

Direct `lake env lean` check and targeted `lake build` passed. Targeted axiom audit reports only
`propext`, `Classical.choice`, and `Quot.sound`. Module is wired into `RHTower.lean` and
`HTGeometry.UniversalLawField`; no umbrella build was run.
