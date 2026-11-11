# Review-1111 assemblies of proved pieces

- **ID:** review-1111-assemblies
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** `docs/reports/review-1111/obstacles-summary.md`, §2.1, "Assemblies of proved pieces".
- **Goal:** a complete, unconditional Lean solution for each task, easiest first.

## Status

| Task | Status |
|---|---|
| A78 | Already a theorem: `SurfaceOfSpecZ.ScaleLocality.finite_top_negative_in_every_window` (any finite top layer, no separation, windows longer than `card(S)π/Γ`). |
| A47 | Already formalized: `3-formalized/one-quartet-current-constant.md`. |
| A136 | Integrated: all six modules are wired into their umbrellas and compile cleanly (`lake --old env lean`): `HodgeTheoryOfAFixedPart/TheUnshiftedCombIndexAtItsOwnAperture`, `FloorFreeArithmetic/TheSplineTraceClassificationAtTheZeroAbscissa`, `FloorFreeArithmetic/ReflectedHalvesAreNotDirichletSeries`, `AbsoluteGeometryOfSpecZ/TheLaguerreTailsOfTheCombTendToTheLiCoefficients`, `BlackHoleRingdown/TheOptimalHorocycleExponentAndEulerAnnihilators`, `MultiscaleMollifiedZetaField/TheDetectorMomentErrorsAreSmall`. |
| A134 | Formalized (A111): eventually `((1 − log(18/5)/(13/10))/4)·N(U) ≤ #` odd-multiplicity critical zeros, mollifier length `⌊U^{13/50}⌋` (`eventually_critical_odd_fiber_proportion_from_short_twisted_moment`, `MultiscaleMollifiedZetaField/TheTwistedMomentGivesAPositiveCriticalProportion`; axioms clean). `3-formalized/levinson-gate-from-below-square-root-twists.md`. |
| A133 | Formalized: `3-formalized/artin-degree-two-character-of-the-cube-roots-of-two.md`. |
| A135 | Formalized: `3-formalized/step-packet-matrices-explicit-block-error.md` (explicit error; no sign certified). |
| A137 | Formalized: `3-formalized/tangent-data-of-mobius-and-liouville-in-world-one.md`. |
| A132 | Formalized: RH through `exp(exp(C a))` ⇒ window positivity, `log log H = O(a)` (`exists_doubleExp_windowPositive`; derivative minorant `σ²W(g) − W(g')` + local sampling from separated verified zeros). `3-formalized/verification-height-order.md`. |
| A89 | Formalized for every nonnegative `R = o(log T)` (`exists_classZ_prescribed_sublogarithmic_windows_bddBelow_beyond_every_bound`, self-consistent interpolation weights; `3-formalized/prescribed-sublogarithmic-window-radius.md`), and one configuration for all `R ≤ (C/256) log log T` (`3-formalized/double-logarithmic-windows-miss-the-minimal-face.md`). |
