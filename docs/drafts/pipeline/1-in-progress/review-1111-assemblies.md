# Review-1111 assemblies of proved pieces

- **ID:** review-1111-assemblies
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** `docs/reports/review-1111/obstacles-summary.md`, §2.1, "Assemblies of proved pieces".
- **Goal:** a complete, unconditional Lean solution for each task, easiest first.

## Status

| Task | Status |
|---|---|
| A78 | Already a theorem: `SurfaceOfSpecZ.ScaleLocality.finite_top_negative_in_every_window` (any finite top layer, no separation, windows longer than `card(S)π/Γ`). |
| A47 | Already formalized: `3-formalized/one-quartet-current-constant.md`. |
| A136 | Integrated: all six modules are wired into their umbrellas and compile cleanly (`lake --old env lean`): `HodgeTheoryOfAFixedPart/TheUnshiftedCombIndexAtItsOwnAperture`, `FloorFreeArithmetic/TheSplineTraceClassificationAtTheZeroAbscissa`, `FloorFreeArithmetic/ReflectedHalvesAreNotDirichletSeries`, `AbsoluteGeometryOfSpecZ/TheLaguerreTailsOfTheCombTendToTheLiCoefficients`, `BlackHoleRingdown/TheOptimalHorocycleExponentAndEulerAnnihilators`, `MultiscaleMollifiedZetaField/TheDetectorMomentErrorsAreSmall`. |
| A134 | Owned by the peer Levinson card `levinson-gate-from-below-square-root-twists.md` (A111): not duplicated. |
| A133 | Formalized: `3-formalized/artin-degree-two-character-of-the-cube-roots-of-two.md`. |
| A135 | Formalized: `3-formalized/step-packet-matrices-explicit-block-error.md` (explicit error; no sign certified). |
| A137 | Formalized: `3-formalized/tangent-data-of-mobius-and-liouville-in-world-one.md`. |
| A132 | Open: triple exponential traced to gap height and low-band extrapolation; double exponential needs an input absent from the corpus. `verification-height-order.md`. |
| A89 | Prescribed radius `R(T) ≤ (C/256) log log T` formalized: `3-formalized/double-logarithmic-windows-miss-the-minimal-face.md`. Open for `log log T ≪ R = o(log T)` (`prescribed-sublogarithmic-window-radius.md`). |
