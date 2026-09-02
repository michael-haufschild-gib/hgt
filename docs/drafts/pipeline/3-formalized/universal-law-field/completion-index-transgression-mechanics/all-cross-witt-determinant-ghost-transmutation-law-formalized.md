# All-cross Witt determinant ghost transmutation — Lean certification

- **ID:** `ULF-ACW-1`
- **Stage:** 3-formalized
- **Paper card:** `completion-index-transgression-mechanics/all-cross-witt-determinant-ghost-transmutation-law.md`
- **Lean module:** `GaloisForLFunctions.RHTower.AllCrossWittDeterminantGhostTransmutation`

## Certified declarations

- `allCrossWittSource` and `wittPowerMoment`: exact finite all-cross source and moment tower.
- `allCrossWittSource_lowDegreeTransmutation`: exact ACW-2 theorem; centered first moments force
  ghosts one through three to vanish and ghost four to equal `-6 L₂ R₂`.

## Verification

Direct `lake env lean` check and targeted `lake build` passed. Targeted axiom audit reports only
`propext`, `Classical.choice`, and `Quot.sound`. Module is wired into `RHTower.lean` and
`HTGeometry.UniversalLawField`; no umbrella build was run.
