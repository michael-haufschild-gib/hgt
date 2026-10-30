# Explicit conductor cutoffs for finite sieve profiles

- **ID:** finite-sieve-profiles-have-explicit-conductor-cutoffs
- **Stage:** 3-formalized
- **Statement:** For a finite prime sieve `Q`, prefix `A` and error `η>0`, put
  `E_Q=sieveEuler(Q)−γ`,
  `N₀=max(A²,ceil(exp(2E_Q+4)))`, and
  `R=max(2,ceil(exp(16(log A+E_Q)/η)))`.
  At every `N≥N₀`, every profile supported on sieve classes at most `A` has
  a Ramanujan approximation using sieve-supported conductors at most `R`,
  with relative squared error at most `η` in the actual harmonic class mass.

## Proof

The chosen horizon gives `A²≤N+1` and `2E_Q+4≤log(N+1)`.
The chosen conductor cutoff gives `R>1` and
`16(log A+E_Q)≤η log R`. Apply
`exists_sieveProfile_ramanujan_approximation`, whose relative error is
`16(log A+E_Q)/log R`. All harmonic class masses are nonnegative, so
the bound transfers directly. The cutoff is independent of the horizon
and of the profile coefficients.

## Verification

`RenormalizedArithmeticPotentialTheory/FiniteSieveProfilesHaveExplicitConductorCutoffs.lean`:
`exists_sieveProfile_ramanujan_approximation_explicit` passed its direct Lean check.
Transitive axioms: `propext`, `Classical.choice`, `Quot.sound`. Umbrella wired.
