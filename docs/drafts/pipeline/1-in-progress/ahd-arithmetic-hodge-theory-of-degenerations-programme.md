# Arithmetic Hodge Theory of Degenerations (AHD) — programme card

- **ID:** AHD
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) programme
- **Source:** docs/reports/review-0111/obstacles-summary.md §2.7
- **Statement:** RH as a structure theorem for the degeneration of the scaling surface along the
  resolution axis; positivity carried through the critical curve by a count, an inherited
  polarization or an integer with a structural bound; one global gluing; calibrations.

## Goal
Develop the field of §2.7: answer its questions by Lean theorems, build its tools. Folder
`formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/`, umbrella
`ArithmeticHodgeTheoryOfDegenerations.lean`, README there.

## Lean modules
TheHorizonTermOfAConductor, TheZeroLedgerOfTheBulk, TheHorizonLayerReadsWeilSummands,
TheCriticalMultiple, TheLedgerOfAWindowOfZeros, TheJordanLimitCountsProjectiveSpace,
TheHorizonBlockIsQuietBelowTheGrid, TheAliasingTailOfAHorizonBlock,
TheHorizonBlockOnTheArithmeticSide, TheHorizonLayerBecomesWeilsForm, TheHorizonCriterion,
TheCriticalMultipleOfAWindow, TheAliasingIsCoercive, TheEnergyOfAHorizonBlock,
TheHorizonBlockBelowTheGridIsSharp, TheSecondOrderTermOfAHorizonBlock,
TheAliasingIsTheDilationDerivativeOfTheBulk, TheAliasingConstantOfTheTiltedSpline,
ThePrimesOfAHorizonWindow, TheBulkDeterminesTheSecondOrderTerm, TheWindowIndex,
TheCountLawOverEveryFiniteRing, TheTwistedHorizonLayerIsZeroBlind.

## Status
- First order = count: `J(m) = J(1) #ℙ⁷(ℤ/m)`; count law over every finite ring (𝔽_q[T] calibration) [L].
- Zero ledgers: bulk (pole only, positive), horizon (Weil summands), twisted horizon (none), window exhaustion [L].
- Horizon theorem: past the critical curve `c⁻¹⟨Wx,x⟩ → κ Q(H)`; RH ⇔ horizon blocks
  nonnegative past the critical curve [L].
- Second order exact: `c⁻¹⟨Wx,x⟩ = κQ(H) − log N·N⁻¹Σ h_n² E₁'(cn/N) + o(1)`; aliasing density
  `= −(∫φ²/2)E₁'`; tilted spline at `c⁸/log N → K`: `→ κQ(H) + (7J(1)/K)∫e^{−8y}H²`; exact
  critical multiple `7J(1)‖H‖²_{−8}/(κ|Q|)` [L].
- General: `s^βE₁(s) → J` ⇒ at `c^{β+1}/log N → K`: `→ κQ(H) + (βJ/K)‖H‖²_{−(β+1)}` [L].
- Primes of a window: departing jumps pay their creation; Markov form at level `⌊e^A⌋` [L].
- Window index: horizon Gram → pencil `κQ + (βJ/K)⟨,⟩`; ind₋(pencil) ≤ eventual ind₋(G_N) ≤ #right zeros [L].

## Open
Window index as counting function in K; bulk second order; uniform bulk ledger to `N^{1/2−ε}`;
count of the second order; integer; `𝔽_q[T]` calibration. See README §9.
