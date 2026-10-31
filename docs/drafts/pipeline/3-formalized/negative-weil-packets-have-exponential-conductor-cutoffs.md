# Negative Weil packets have exponential conductor cutoffs

- **ID:** negative-weil-packets-have-exponential-conductor-cutoffs
- **Stage:** 3-formalized
- **Statement:** For each squared approximation error `η>0`, fixed positive
  constants `C,D,H` give, for every `c≥1`, a conductor cutoff
  `R≤exp(D(Cc^16+1))`. At every horizon `N≥Hc^8`, every unit packet of
  nonpositive complete tilted-spline Weil energy is within squared error `η`
  of the Ramanujan modes with conductors at most `R`.

## Proof

The complete signed Weil reserve bounds the prime defect of each such packet
by `Cc^16`. The exponential conductor approximation theorem, with defect
budget `K=Cc^16`, supplies a single cutoff `R≤exp(D(K+1))`, uniformly in the
horizon and coefficient vector. The Euclidean unit norm is exactly the
finite coefficient square mass. Substitution proves the claim, retaining
all prime powers, poles and Gamma terms in the energy condition.

## Inputs

`exists_negative_completeWeil_poleDefect_polynomial_bound`,
`exists_exponential_conductor_cutoff_of_poleDefect_le`, and
`sum_primeHorizonExtension_sq`.

## Verification

`CriticalArithmeticCorrelationTheory/NegativeWeilPacketsHaveExponentialConductorCutoffs.lean`:
`exists_negative_completeWeil_exponential_conductor_cutoff` passed its direct
`lake --old env lean` check. Transitive axioms: `propext`, `Classical.choice`,
`Quot.sound`. Umbrella import wired.
