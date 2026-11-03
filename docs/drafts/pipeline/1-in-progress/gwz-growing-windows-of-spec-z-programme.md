# Growing Windows of Spec ℤ (GWZ) — programme card

- **ID:** GWZ
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) programme
- **Source:** docs/reports/review-0311/obstacles-summary.md §2.7 (also §2.4, §2.5.1, §2.6.1)
- **Statement:** the exact theory of growing windows: two-collar forms and kicks (continuum), the
  lattice canonical system of Spec ℤ (Schur–Levinson evolution of Weil sequences), ground states,
  zero modes, angles and margins.

## Goal
Answer the §2.7 questions by Lean theorems. Folder `formal/GaloisForLFunctions/GrowingWindowsOfSpecZ/`,
umbrella `GrowingWindowsOfSpecZ.lean` (wired into `MainTheorems.lean`), README there.
WTZ, DZG, CWS, ACT, F1/F2 cards are owned by other agents: import, never edit.

## Lean modules [L]
TheTwoCollarFormOfAStage, TheKickIsTheCollarReflection, TheTwoCollarFormIsBornZero,
ZeroModesHaveReflectionParity, TheLatticeCanonicalSystem, TheAnglesOfADegenerateWindow,
ADegenerateWindowIsACurve, TheSchurParametersOfSpecZ, AWindowIsTheUnionOfItsLattices,
TheLatticeReadsThePrimesCausally,
TheEvolutionStartsPositive, TheLatticeSelectsTheVonMangoldtWeight, ThePoleIsAHyperbolicPairOfAngles,
MarginsAreBoundedByRecurrence, TheLatticeHasNoSlackUnderRH, RefiningTheLatticeLowersTheMargin,
TheSzegoVerblunskyLaw, TheContinuumMarginIsTheDyadicLimit, ForbiddingLatticeZeroModesIsRH,
TheFirstPrimeStageOpensPositive, TheLatticeSchurDataCoalesce, GapContinuationIsNotStructural. Each passes an individual `lake --old env lean` check; key theorems
audited to `propext, Classical.choice, Quot.sound`.

## Status
- Continuum: kick reads collar data only; two-collar form (EReal infimum), kick law, stage criterion,
  reflection invariance; born zero at each stage and monotone in the collar width; the kick is the
  collar Rosati form, `±` the signature of the collar reflection on the `σ_A`-sectors; parity
  splitting; frozen-negative tests forced into the source sectors; zero modes have parity; gap law.
- Lattice: one/two-collar decompositions (`[[E, β], [β, E]]`), Levinson law, positivity ⇔ margins,
  prediction interval `|β| < E`, kick law, causality, margins as products, monotone, recurrence bound;
  degeneration: unique palindromic zero mode, `n + 1` simple unit-circle angles, Carathéodory–Fejér
  (degenerate window = curve window with positive weights); outer predictors.
- Spec ℤ: Toeplitz identity for lattice tests, independence of translates, window `W_A` ⇔ all lattices
  of total length `≤ A`, RH ⇔ all margins positive
  ⇔ all reflection coefficients in `(−1, 1)`; degenerate lattice refutes RH; locality/causality in the
  primes, single-kick formula, rigidity interval of a weight; base positivity to total length
  `181/250`; selection of `Λ` by the lattice; every kick necessary; free evolution fails; the pole as
  the hyperbolic pair `e^{±h/2}`; under RH every lattice is singular (margins → 0; RH ⇔ all lattices
  positive and singular); refinement lowers margins and the dyadic limit is the continuum corner
  margin; Szegő–Verblunsky: collapse ⇔ `Σγ² = ∞`, under RH never square-summable; Lyapunov identity and
  two-sided bounds for `Σγ²`, lower bound by orbit recurrence; RH ⇔ no lattice
  degenerates; zero modes continue uniquely from an end collar; the pole plane has one negative
  square; the first prime stage opens positive (`log 2 ≤ A ≤ 181/250`); fixed-index Schur data
  coalesce under refinement; gap continuation fails structurally (three-angle curve).

Relation: CSWT (`CanonicalSystemOfTheWindowTower`, other agent) is the continuum register (closed form
of the frozen two-collar form via trivial-divisor moments; translation-contraction growth law).

## Next directions (README §7)
All §2.7 questions answered (README §5). Beyond them: closed form of the minimized first-stage form
`Φ_ε`; a stage-uniform law placing every kick in its interval (RH); continuation across interior
gaps; limits of Schur parameters (Krein system); sharp asymptotics of `Σγ²`; AHD's additive angle.
