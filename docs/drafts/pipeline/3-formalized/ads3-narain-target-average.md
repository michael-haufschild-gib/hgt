# Actual target-horocycle average and its scalar Mellin transform

- **ID:** W11-NA
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [W11](../1-in-progress/ads3-scalar-modular-bootstrap.md)
- **Statement:** For every pair of positive heights `Y,Z`, the actual heat
  average `A(y)=∫₀¹∫₀¹ H_(x+iY,w+iZ)(y) dw dx` has an absolutely convergent
  Mellin transform on `Re s>1`, equal to `narainMellinMean Y Z (s−1/2)`.

## Proof

For horizontal coordinates in `[0,1]`, put

`K*=YZ(2Z²+3)Z⁻²(2+3Y⁻²)>0`.

The proved mass coercivity constant is at most `K*`, so every charge obeys
`M²≥(|n|²+|w|²)/K*`. The square-target Boltzmann sum at height `y/K*`
uniformly dominates all target heat sums. Its Mellin norm is integrable
for `Re s>1`: absolute scalar Dirichlet convergence and the corpus's
`WeilSingularArithmetic.mellinConvergent_of_exponential_series` give this
after countable reindexing.

The parameter-dependent summands are measurable. Uniform domination on
the two finite target intervals proves joint integrability and permits
the two target integrals to commute with the height integral. The proved
`integral_mellin_narainScalarHeat` then identifies the result with the
explicit meromorphic mean.

On each positive height neighborhood, the same bound at half the base
height gives dominated continuity. At large height it transfers the
square-target exponential tail to the average. Thus the averaged source
has the local integrability and cusp decay required by Mellin continuation.

Every arithmetic pole survives in that mean with full multiplicity at
every `Y,Z`. This proved interchange reduces family pole detection to one
fixed positive source profile. It supplies no small-height
remainder or arithmetic zero-free region.

## Lean

- `mellinConvergent_narainScalarHeat` in `NarainMellinConvergence`: absolute
  height integrability on `Re s>1` for every target pair.
- `norm_narainScalarHeat_uniform_upper` in `NarainTargetBounds`: uniform
  square-target majorant; joint measurability is also proved.
- `integrable_narainScalarHeat_target_mellin` in `NarainTargetAverage`: absolute
  target/height integrability and hence Fubini.
- `mellin_narainScalarHeatAverage`: the actual averaged source has the
  explicit meromorphic mean as its Mellin transform on `Re s>1`.
- `continuousOn_narainScalarHeatAverage` and
  `exists_isBigO_narainScalarHeatAverage_exp`: positive-height regularity
  and exponential cusp decay.

All declarations lie in namespace
`GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap`.
All three modules pass direct Lean checks; eight endpoint axiom audits
use only `propext`, `Classical.choice`, and `Quot.sound`. Umbrella imports
are wired.

The [fixed-source decay obstruction](ads3-narain-average-pole-decay-boundary.md)
and its rate-to-RH implication are also formalized.

## Gates

- [x] 0 → 1: explicit uniform majorant and source identity identified.
- [x] 1 → 2: source convergence, joint measurability and norm-Fubini discharged.
- [x] 2 → 3: direct Lean checks, axiom audits and umbrella imports.
