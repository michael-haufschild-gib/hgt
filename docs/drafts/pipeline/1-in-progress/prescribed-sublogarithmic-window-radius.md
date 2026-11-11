# A prescribed radius for the density-matched window model

- **ID:** A89
- **Stage:** 1-in-progress
- **Type:** CONJECTURE

## Target

For a prescribed nonnegative radius `R(T)=o(log T)`, construct a tempered
reflection-symmetric configuration with logarithmic local zero count,
unattained positive top depth, and arbitrarily late windows of radius `R(T)`
on which the spline trace exceeds every fixed floor.

## Existing result and obstruction

`SubLogarithmicWindowsMissTheMinimalFace` constructs its own radius,
equal to `k+1` at the recursively chosen centres. It does not establish
the prescribed-radius quantifier.

Its binomial block has degree `m₀=4ΓR`, coefficient cost `64^m₀`,
and phase-splitting error proportional to `1/T`. The existing error bound
therefore requires `log T` to dominate `ΓR`. The sufficient local-count
condition separately requires `log Γ` to dominate `R`. These sufficient
conditions are incompatible with many sub-logarithmic prescriptions,
including `R(T)=sqrt(log T)` for all sufficiently large `T`.

This is a limitation of the present construction, not a counterexample
to the target. A new block construction or sharper phase-error estimate
is required; enlarging the recursive centres alone is insufficient.

## Lean status

The endogenous-radius theorem is already formalized. The prescribed-radius
construction remains open; no new theorem is claimed.
