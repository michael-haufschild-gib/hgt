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
A zero `ρ` with `Re ρ>1-a` contributes at `s=ρ-a`. In this region
`Re(ρ+a)>1`, so the Euler product excludes cancellation by `ζ(ρ+a)`. The archimedean and polar terms must be controlled separately
at the same normalization.

## Required proof

1. Exact arithmetic increment/Dirichlet identity for the literal power comb.
2. Analytic continuation of the remaining terms in the required half-plane.
3. Convergence or growth control implies exclusion of uncancelled zeta poles;
   exclude cancellation using the Euler half-plane.
4. Prove the converse from existing zero-free prime-error estimates, including
   singular weighted sums and the actual finite-comb limit.

## Existing sources

- `AbsoluteGeometryOfSpecZ/TheLaguerreTailsOfTheCombTendToTheLiCoefficients`:
  unsmoothed logarithmic tails already solved; not a new contribution.
- `AbsoluteGeometryOfSpecZ/TheRowOfTheFlatTailHasTheMellinTransformOfTheZeros`:
  exact Mellin row identity to the right of the boundary.
- `HodgeTheoryOfAFixedPart/TheNormalFormOfThePairingOfTheDegreePoints`:
  literal contacts, counterterm and pole degrees.

The finite contact reduction is formalized in
`AbsoluteGeometryOfSpecZ.combForm_powerTailWeight_eq`.
`partialSumPowerBound_centeredContact_iff_zeroHalfPlane` classifies the
centered contact exponent `1-2a+σ` by `Re ρ≤1-a+σ`.
Reference and archimedean bounds are formalized; the literal-comb growth
theorem `powerCombTailGrowth_iff_zeroHalfPlane` is formalized.
`riemannHypothesis_iff_all_powerCombTails_subpolynomial` gives the exact
RH criterion for subpolynomial growth of all positive subcritical tails.
Convergence and its Mellin limit remain open;
a growth-only intermediate result does not finish the target.

## Arithmetic reduction

For unscaled coefficients `c_n=n^(-a)`, the contact sum is
`2 Σ_{n≤N} n^(-2a) Σ_{d|n} Λ(d)d^a`. Subtract
`2ζ(1+a) Σ_{n≤N} n^(-a)`. The difference from the full comb form
should be `O(N^(1-2a) log N)` for `0<a<1/2`: the pole-product tail
costs `O(N^(1-2a))`, while absolute jet and counterterm bounds cost one
logarithm. This reduces the lower analytic obstruction to the summatory
Dirichlet coefficient
`n^(-2a)Σ_{d|n}Λ(d)d^a - ζ(1+a)n^(-a)`.

The convolution decomposition is
`C_a-ζ(1+a)w_a = w_(2a)*(w_a(Λ-1)) + H_a`, where
`H_a=w_(2a)*w_a-ζ(1+a)w_a`. Integral comparison and the tail of the
`(1+a)`-series give summatory `H_a=O(N^(1-2a))`.
Weighted Möbius inversion preserves strict growth exponents
`θ≥1-2a`; thus the contact defect has the same growth class as
`w_a(Λ-1)`. This avoids a separate complex pole argument for growth.
