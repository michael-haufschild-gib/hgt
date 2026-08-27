# GTA actual theta-stage Green cofinal mixed inertia (2026-08-27)

Corpus-led conjecture `[GTA-PQ4-P]` completed and formalized.

`formal/GaloisForLFunctions/RHTower/HedenmalmThetaStageGreenBoundaryCofinalMixedInertia.lean` proves:

- operator-norm convergence of actual complete Green boundaries transports to real quadratic forms on every fixed vector;
- the fixed `pinnedPositiveMode` and `pinnedNegativeMode` simultaneously give values `>1/12` and `<-1/12` at every sufficiently late stage;
- neither eventual positivity of the boundary nor eventual positivity of its negative is possible.

Scientific boundary: one-sided positive/negative semidefinite Green laws cannot be the missing GTA arithmetic selector. Surviving selector must be genuinely indefinite and mode-sensitive. Positive survivor is fixed-witness quantitative cofinal mixed inertia, stronger than a negative statement. Both witnesses have squared norm `13/12`; every sufficiently late boundary lies at operator-norm distance `> 1/13` from each of the positive and negative operator cones, excluding approximate semidefinite descent.

Verification: direct Lean, exact targeted build, formal lint passed; axioms only `propext`, `Classical.choice`, `Quot.sound`. Card: `docs/drafts/pipeline/5-failed/theta-stage-green-boundary-cofinal-mixed-inertia.md`.