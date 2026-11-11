# Power comb tails detect the zero width

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Target:** A82's remaining power-tail extension; AGZ question 5.

## Target

For `0<a<1/2`, let
`P_a(N)=combForm([1,N], n↦(N/n)^a)/N`.
Classify its growth by the rightmost zeta zeros. In particular, prove that
convergence of every such power tail is equivalent to RH, and identify the
limit in the convergent range by the Mellin pairing of the two powers.
The primary theorem must be unconditional; no zero-free or analytic input
may be assumed without proving the corresponding implication.

## Connection

The existing Laguerre-tail theorem reaches all logarithmic moments, but
its Mellin integral is established only to the right of the boundary.
A positive power probes beyond that boundary. The exact contact increments
have Dirichlet transform involving
`ζ(s+2a)·(-ζ′/ζ)(s+a)`.
A zero `ρ` contributes at `s=ρ-a`, except when `ζ(ρ+a)=0` cancels it.
Iteration of a fixed positive real shift cannot stay in the critical strip;
this may recover the sharp rightmost obstruction without a no-cancellation
hypothesis. The archimedean and polar terms must be controlled separately
at the same normalization.

## Required proof

1. Exact arithmetic increment/Dirichlet identity for the literal power comb.
2. Analytic continuation of the remaining terms in the required half-plane.
3. Convergence or growth control implies exclusion of uncancelled zeta poles;
   resolve possible cancellations by finite shift propagation.
4. Prove the converse from existing zero-free prime-error estimates, including
   singular weighted sums and the actual finite-comb limit.

## Existing sources

- `AbsoluteGeometryOfSpecZ/TheLaguerreTailsOfTheCombTendToTheLiCoefficients`:
  unsmoothed logarithmic tails already solved; not a new contribution.
- `AbsoluteGeometryOfSpecZ/TheRowOfTheFlatTailHasTheMellinTransformOfTheZeros`:
  exact Mellin row identity to the right of the boundary.
- `HodgeTheoryOfAFixedPart/TheNormalFormOfThePairingOfTheDegreePoints`:
  literal contacts, counterterm and pole degrees.

No new Lean theorem yet. Algebraic and analytic claims above remain to be
proved; a growth-only intermediate result does not finish the target.
