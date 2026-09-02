# Steinberg--Kummer second-jet unit saturation — Lean certification

- **ID:** `ULF-SKJS-1`
- **Stage:** 3-formalized
- **Paper card:** `completion-index-transgression-mechanics/steinberg-kummer-second-jet-unit-saturation-law.md`
- **Lean module:** `GaloisForLFunctions.RHTower.SteinbergKummerSecondJetUnitSaturation`

## Certified declarations

- `skEuler_cell` and `skEuler_cell_two`: exact first and second Euler-jet identities.
- `skJetIdeal_eq_top`: cell and first two jets generate the unit ideal.
- `skStableIdeal_eq_top`: every Euler-stable ideal containing the cell is the whole ring.

## Verification

Direct `lake env lean` check and targeted `lake build` passed. Targeted axiom audit reports only
`propext`, `Classical.choice`, and `Quot.sound`. Module is wired into `RHTower.lean` and
`HTGeometry.UniversalLawField`; no umbrella build was run.
