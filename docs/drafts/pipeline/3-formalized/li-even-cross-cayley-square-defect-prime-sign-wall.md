# LI even-cross Cayley square defect and prime sign wall

- **ID:** LI-CAB1.SW
- **Stage:** 3-formalized
- **Lean module:** `GaloisForLFunctions.RHTower.LiEvenCrossCayleySquareDefectPrimeSignWall`
- **Corpus source:** `LiArithmeticProgressionSquareSourceCriterion`, `LiEvenCrossCriticalAbelBoundaryNoGo`

## Result

For every LI mode `n`, Lean proves the critical common-reversal density identity

`density_n(x) = (1 - T_{n+1}(u(x))^2) / 2`

and the exact range classification

`density_n(x) in [0,1/2]`.

For the zeroth mode, the real Fourier profile is negative exactly when `2 < |xi|` and vanishes exactly when `|xi| = 2`. At prime frequencies the literal signed leg is

`(pi/2) * (Lambda(n)/n) * (1-log(n)/2)`.

Its tail is nonpositive, and both this normalized sequence and the literal prime-leg sequence are not summable in natural order.

## Route consequence

Pointwise nonnegative bounded Cayley density does not imply Fourier positivity. Ordinary signed prime summation also fails, not merely absolute summation. Any viable LI producer must preserve prime, polar, and Gamma contributions in one completed Abel/Hadamard finite part.

## RH chain

`completed Abel prime--polar--Gamma finite part >= 0 for every mode`
`=> LI common-reversal cross capitals >= 0`
`=> positive even paired Li coefficients >= 0`
`=> RiemannHypothesis`.

## Audit

- `lake env lean GaloisForLFunctions/RHTower/LiEvenCrossCayleySquareDefectPrimeSignWall.lean`: passed.
- `lake build GaloisForLFunctions.RHTower.LiEvenCrossCayleySquareDefectPrimeSignWall`: passed.
- Umbrella import added to `GaloisForLFunctions/RHTower.lean`.
- Capstone axioms: `propext`, `Classical.choice`, `Quot.sound` only.
