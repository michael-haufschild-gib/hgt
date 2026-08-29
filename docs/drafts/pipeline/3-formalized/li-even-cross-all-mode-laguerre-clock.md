# LI even-cross all-mode Laguerre clock

- **ID:** LI-CAB2
- **Stage:** 3-formalized
- **Lean module:** `GaloisForLFunctions.RHTower.LiEvenCrossAllModeLaguerreClock`
- **Corpus sources:** `LiEvenCrossCayleySquareDefectPrimeSignWall`, `XiShiftedHardEdgeMehlerHeine`, `CayleyLaguerreFourier`, `VanDerCorput`

## Result

Let `P_m` be the associated-Laguerre polynomial used by the corpus Cayley Fourier theorem, let `m = 2(n+1)`, and set

`Q_n(r) = P_m''(r) - P_m'(r)`.

Lean proves the exact unit-scale no-`2pi` Fourier law

`Fourier(unitDensity_n)(xi) = (pi/2) exp(-|xi|) Q_n(2|xi|)`

and, after the exact critical half-mass dilation,

`Fourier(criticalDensity_n)(xi) = (pi/4) exp(-|xi|/2) Q_n(|xi|)`.

The proof is all-mode and treats positive, negative, and zero frequencies. It includes the required polynomial majorants, integrability, and dominated differentiation under the Fourier integral.

## Proof-burden reduction and route test

The LI route no longer has an unknown Fourier kernel or mode-dependent analytic regularization. Every mode is represented by one explicit finite polynomial clock multiplying the critical exponential.

Remaining producer is exact and route-decisive: establish nonnegativity of the jointly completed prime--polar--Gamma finite part on every `Q_n`. A negative completed value kills this LI route; a uniform nonnegative theorem closes its remaining arithmetic burden.

## RH chain

`completed prime--polar--Gamma finite part nonnegative on every Q_n`
`=> every LI common-reversal cross capital nonnegative`
`=> every positive even paired Li coefficient nonnegative`
`=> RiemannHypothesis`.

## Novelty audit

Lagarias relates Li coefficients to Weil quadratic functionals, and generalized Li literature contains Chebyshev/Laguerre arithmetic formulas. Mazhouda--Smajlović likewise use Chebyshev expressions for generalized Li coefficients. The audit found no statement of this corpus-specific common-reversal Cayley square-defect clock, its exact `P''-P'` profile, or its role as the all-mode completed-sign interface. Novelty claim is limited to that exact synthesis and formal theorem, not to classical Li, Weil, Chebyshev, or Laguerre ingredients.

Primary sources audited:

- J. C. Lagarias, *Li Coefficients for Automorphic L-Functions*, arXiv:math/0404394.
- A. Mazhouda and L. Smajlović, *On relations equivalent to the generalized Riemann hypothesis for the Selberg class*, arXiv:1511.04603.

## Audit

- `lake env lean GaloisForLFunctions/RHTower/LiEvenCrossAllModeLaguerreClock.lean`: passed.
- `lake build GaloisForLFunctions.RHTower.LiEvenCrossAllModeLaguerreClock`: passed.
- Umbrella import added to `GaloisForLFunctions/RHTower.lean`.
- Capstone axioms: `propext`, `Classical.choice`, `Quot.sound` only.
