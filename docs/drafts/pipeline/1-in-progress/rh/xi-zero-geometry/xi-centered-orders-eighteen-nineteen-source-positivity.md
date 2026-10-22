# Xi centered orders eighteen and nineteen source positivity

## Status

- Stage: Lean-proved locally; final axiom and umbrella audit pending
- Type: theorem
- Target Lean area: `formal/GaloisForLFunctions/RHTower`

## Corpus audit

Existing reusable inputs:

- centered reciprocal-square coordinate and atomwise-to-moment bridge;
- exact sector certificates for reciprocal powers eighteen and nineteen;
- off-line zero height floor `85 < gamma^2`;
- critical-strip bound `delta^2 < 1/4`;
- FE--Schwarz quartet budget against `normalizedPrimeArchMoment 1`;
- source upper bound `normalizedPrimeArchMoment 1 < 9/50000`;
- order-eighteen corner fourth-trace estimate.

No theorem currently proves positivity of centered reciprocal-square powers eighteen or nineteen,
normalized moments seventeen or eighteen, or the full degree-nine square-coefficient cone.

## Theorem

For every Xi zero copy `q`,

1. `0 < Re (xiZeroCopyReciprocalSquare q)^18`;
2. `0 < Re (xiZeroCopyReciprocalSquare q)^19`.

Consequently:

1. `0 < normalizedPrimeArchMoment 17`;
2. `0 < normalizedPrimeArchMoment 18`;
3. every degree-at-most-nine integer polynomial with nonnegative real self-convolution
   coefficients has nonnegative prime--Gamma trace--Hankel value.

## Exact attack

Write

`u = (Re rho - 1/2)^2`, `v = (Im rho)^2`, `A = v-u`, `B^2 = 4uv`.

- Power eighteen: use sector coefficient `132`. Failure is confined by exact rational
  inequalities to `4/25 < u < 1/4`, `85 < v < 133`.
- Power nineteen: use sector coefficient `147`. Replace coarse height `148` by the exact rational
  threshold `295/2`; failure is confined to `7/50 < u < 1/4`,
  `85 < v < 295/2`.
- Prove throughout the union corner that one fourth reciprocal-trace atom exceeds `9/200000`.
  Four distinct FE--Schwarz copies then contradict the complete-source upper bound
  `normalizedPrimeArchMoment 1 < 9/50000`.

All inequalities must be proved symbolically over exact rationals in Lean.

## Proof certificate

Exact rational sector arguments confine failures to the two stated corners. The common
fourth-trace estimate proves

`9/200000 < Re (xiZeroCopyReciprocalSquare q)^2`

through their union. The existing four-copy FE--Schwarz budget then gives

`9/50000 < normalizedPrimeArchMoment 1`,

contradicting its strict source upper bound. Atomwise positivity transfers to moments seventeen
and eighteen through the existing summable-moment bridge. Generic HTGeometry square-coefficient
moment positivity then proves the full degree-nine cone.

## Novelty audit

Post-proof searches covered reciprocal-zero power sums, secondary/superzeta functions, and Li
criteria. Arias de Reyna's secondary-zeta work, Voros's superzeta framework, and Coffey's
Li-coefficient inequalities concern related reciprocal sums but did not state the exact
unconditional centered powers eighteen/nineteen sign or the resulting degree-nine cone. No exact
collision found; no priority claim made.

## Lean status

Checked with `lake env lean`:

- `RHTower/XiCenteredOrdersSeventeenEighteenSourcePositivity.lean`
- `RHTower/PrimeArchCoefficientSignCone.lean`
- `RHTower/PrimeArchCombinedResidualSonin.lean`

Main results:

- `xiZeroCopyReciprocalSquare_pow_eighteen_re_pos`
- `xiZeroCopyReciprocalSquare_pow_nineteen_re_pos`
- `normalizedPrimeArchMoment_seventeen_pos`
- `normalizedPrimeArchMoment_eighteen_pos`
- `re_primeArchSourceTraceHankel_nonneg_of_degreeNineSquareCoeffCone`
- `primeArchDegreeNineSquareCoeffPolynomial_not_combinedResidual`
