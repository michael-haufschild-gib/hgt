# Uniform absolute payment of the prime correction above touching

- **ID:** uniform-absolute-prime-correction-payment-above-touching
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Statement rejected:** At a fixed plateau overlap `c>1`, a horizon-independent
  Euclidean operator bound controls the actual normalized non-ratio prime correction.

## Obstruction

At `N_Y=2Y!-1`, the image of the last unit coordinate has squared norm at least
`[Cφ(t_(N_Y)/c)/∫φ²]² Σ_(p≤Y)(log p)²/p`. The correlation factor tends to a
strictly positive limit for `c>1`, while the prime sum diverges. Every proposed bound
therefore fails at arbitrarily late horizons.

## Positive survivor and exact insight

Eventual boundedness is classified exactly by `0<c≤1`; throughout that range the actual
correction even tends to zero uniformly in operator action. The finite-column inequality
identifies the arithmetic source of the transition: many prime divisors of one successor
product share a positive correlation. This is a Euclidean obstruction independent of
the different Schur weights in the logarithmic divisor-fiber theorem.

Any positivity proof above touching must retain compensation with the other complete-form
terms. The obstruction alone proves no negative eigenvalue of the complete Weil matrix.

## Proof status

The finite-column argument and sharp boundary are dependency-closed on paper and formalized
in `TransMetzlerWeilPositivity/FactorialSuccessorsForceUnboundedPrimeCorrections.lean`,
particularly `factorialSuccessor_action_sq_ge`, `factorialSuccessor_action_atTop`, and
`eventually_bounded_fullWeilNonRatio_action_iff`.
Direct check and all four transitive axiom audits passed with default limits;
only `propext`, `Classical.choice`, `Quot.sound` occur. Umbrella import is wired.
