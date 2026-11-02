import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheHorizonTermOfAConductor
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheZeroLedgerOfTheBulk
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheHorizonLayerReadsWeilSummands
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheCriticalMultiple
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheLedgerOfAWindowOfZeros
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheJordanLimitCountsProjectiveSpace
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheHorizonBlockIsQuietBelowTheGrid
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheAliasingTailOfAHorizonBlock
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheHorizonBlockOnTheArithmeticSide
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheHorizonLayerBecomesWeilsForm
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheHorizonCriterion
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheCriticalMultipleOfAWindow
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheAliasingIsCoercive
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheEnergyOfAHorizonBlock
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheHorizonBlockBelowTheGridIsSharp
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheSecondOrderTermOfAHorizonBlock
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheAliasingIsTheDilationDerivativeOfTheBulk
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheAliasingConstantOfTheTiltedSpline
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.ThePrimesOfAHorizonWindow
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheBulkDeterminesTheSecondOrderTerm
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheWindowIndex
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheCountLawOverEveryFiniteRing
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheTwistedHorizonLayerIsZeroBlind
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheWindowIndexCountsTheRightZeros
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheTwistedHorizonLayerIsPositive
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheAlternatingWindowCountsTheConductorTwoPoints
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.ThePrimeWindowCountsTheProjectivePoints
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheHorizonLayerIsGradedByConductor
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheWindowIndexCountsTheJumpMultiples
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheEnergyOfAPeriodicTwist
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheRamanujanWindowCountsEveryConductor

/-!
# Arithmetic Hodge Theory of Degenerations

Umbrella for the arithmetic Hodge theory of the degeneration of the scaling surface along the
resolution axis: the horizon term of a conductor (only the pole conductor carries one); the zero
ledger of the bulk (a point of the strip enters a fixed conductor packet only through a positive
pole weight); the horizon layer (a point enters a horizon block through Weil's summand of the
synthesized test); windows of zeros and their exhaustion to Weil's form; the calculus of critical
multiples of a second-order term; the Jordan limit as the point count of `ℙ⁷` over `ℤ/m`; the
horizon layer on the arithmetic side (Kuzmin–Landau below the atom grid, aliasing tails above it)
and its limit: past the critical curve it is Weil's form of the synthesized test, at it up to
`O(1/K)`; the horizon criterion for RH; the critical multiple of a window; coercivity of the
aliasing part; the exact energy of a horizon block (Plancherel and Poisson on the atom grid); the
sharp part below the grid; the second-order term (Weil's form plus `log N` times the window average
of the aliasing density); the aliasing density as the dilation derivative of the bulk energy; the
exact second-order term at the critical curve for the tilted spline, `κ Q(H) + (7 J(1)/K) ∫ e^{−8y} H²`,
and the exact critical multiple of a window; the primes of a horizon window (departing prime jumps
pay their own creation potential); the bulk determines the second-order term (for every profile with
`s^β E₁(s) → J`, the correction is `(β J/K) ∫ e^{−(β+1)y} H²`); the window index (the pencil Gram
matrix of a family of windows is the limit of the complete family's horizon Gram matrices, its
negative index is read by them and bounded by the number of right zeros); the count law over every
finite ring (calibration: the first-order count is the same over `ℤ` and `𝔽_q[T]`); the twisted
horizon layer is zero-blind and positive (windows twisted by a mean-zero periodic weight see no
zero and lie above the archimedean horizon); the window index counts the right zeros; the
alternating (conductor-two) window has second-order term `7 J(2)/K ‖H‖²_{−8}`, and for every prime
`p` the conductor-`p` window has `7 (p − 1) J(p)/K ‖H‖²_{−8}`: the conductor-`p` count, and for
every `m ≥ 2` the Ramanujan window of conductor `m` has `7 φ(m) J(m)/K ‖H‖²_{−8}` (energy law of
periodic twists through their autocorrelation); the
horizon layer is graded by conductor (untwisted and prime windows are orthogonal at second order,
so their span carries the direct sum of the two blocks); the window index of an independent
family counts its jump multiples `βJ/(−λ_i)`, `λ_i` the relative eigenvalues of Weil's part against
the aliasing part.
See `ArithmeticHodgeTheoryOfDegenerations/README.md`.
-/
