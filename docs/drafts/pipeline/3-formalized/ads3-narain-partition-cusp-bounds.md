# Positivity majorant and cusp bounds for the actual Narain partition

- **ID:** W11-NC
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** [Regularized overlap](ads3-narain-regularized-overlap.md)

## Statements

For positive target heights and every worldsheet point `τ=x+iy`:

- `|Z_(B+iV,σ)(τ)|≤Z_(iV,σ)(τ)`, with the right side real and nonnegative.
- `∫₀¹ |Z_(ρ,σ)(x+iy)|dx≤y[1+|H_(iV,σ)(y)|]`.
- For every `a>0`, `|Z_(ρ,σ)(x+iy)|≤C(a)y` on `y≥a`, where
  `C(a)=Σ_q exp(−πaM²(q))`.
- On `y≥1`, `|Z_(ρ,σ)(x+iy)−y|≤By exp(−cy)`, uniformly in `x`,
  with `B=C(1/2)` and `c=π/(2K)`, where `M²(q)≥1/K` off the vacuum.
- The partition is jointly measurable in `(x,y)` and continuous on each
  positive horocycle.

## Proof

Poisson triality exchanges `ρ` and `τ`; removing the spin phase and
exchanging back gives the positive majorant. Exact scalar projection
then gives its angular integral. Nonnegative masses make each Boltzmann
weight decrease in height, proving the linear bound. Split each
nonvacuum exponent between height `1/2` and half the current height;
the mass gap supplies exponential decay. Summable Gaussian domination
justifies continuity and each norm-series interchange.

The angular bound supplies the sharp absolute-convergence threshold
`Re s>1` for truncated overlap unfolding. The linear cusp bound alone
controls the remaining Eisenstein cusp correction in that region.
Neither bound supplies an RH-strength small-height estimate.

## Lean endpoints

Modules in `ArithmeticScatteringHolography/ModularBootstrap`:

- `NarainPartitionBounds`: `norm_narainPartition_le_pureArea`,
  `narainPartition_pureArea_nonneg`.
- `NarainPartitionRegularity`: `measurable_narainPartition`,
  `continuous_narainPartition_fixedHeight`, `narainPartition_linear_cusp`,
  `narainPartition_exp_cusp`.
- `NarainPartitionAngularBounds`: `integral_norm_narainPartition_le`.

All three modules passed direct Lean checks. Seven endpoint axiom audits
contain only `propext`, `Classical.choice`, `Quot.sound`; umbrella imports
are wired.

## Gates

- [x] 0 → 1: exact majorants and mass-gap constants identified.
- [x] 1 → 2: all actual-source inequalities checked.
- [x] 2 → 3: direct Lean checks, axiom audits and umbrella imports.
