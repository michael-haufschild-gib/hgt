# Prime-valuation sector: independence is the mechanism

`formal/GaloisForLFunctions/HTGeometry/PrimeValuationSector.lean`.

## The two closing theorems

- `iIndepFun_primeValuation` — the coordinate valuations are independent under
  `primeValuationMeasure = Measure.infinitePi primeValuationLaw`. Proof is a one-line
  instantiation of mathlib's `ProbabilityTheory.iIndepFun_infinitePi` with `X i = id`
  (`fun _ => measurable_id`); the statement's `fun i ω => X i (ω i)` is then defeq to
  `fun p k => k p`.
- `primeValuationMeasure_dividedCylinder P = ofReal (∏ p ∈ P, 1/p)` — the density of the
  multiples of `∏ P`. Same `Measure.infinitePi_pi` route as the survivor cylinder, with the
  local target `{0}ᶜ` instead of `{0}`.

Together with `primeValuationMeasure_cylinder = ofReal (sieveDensity P)` this makes the sector
the honest probabilistic model of the Euler sieve: both arithmetic densities are event masses,
and independence — not a computation — is why they factor. That is the probabilistic content
of the Euler product.

## Import trap

`iIndepFun_infinitePi` lives in `Mathlib.Probability.Independence.InfinitePi`, which
`Mathlib.Probability.ProductMeasure` does NOT pull in. Both `ProbabilityTheory.iIndepFun` and
the lemma read as unknown identifiers until that import is added — the "unknown identifier
`ProbabilityTheory.iIndepFun`" error is a missing import, not a wrong namespace.

## Build state

`lake build GaloisForLFunctions.HTGeometry.PrimeValuationSector` — 3008 jobs, exit 0, both
declarations `[propext, Classical.choice, Quot.sound]`.

`RHTower/RouteRFirstDivisorPartition.lean` now has its olean too (11307 jobs, exit 0), so the
first-divisor layer is complete and umbrella-reachable: `RouteRSieveWeightIsEventMass` gives the
sieve weight as an event mass, `RouteRFirstDivisorPartition` gives pairwise disjointness and
total mass one.

See `mem:prime_valuation_sector_formalized_2026_08_07` for the sector's construction.
