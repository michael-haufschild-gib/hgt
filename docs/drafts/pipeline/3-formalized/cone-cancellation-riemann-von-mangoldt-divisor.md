# Exact spline divisors with the Riemann–von Mangoldt count

- **Stage:** 3-formalized
- **Type:** THEOREM; direct Lean and transitive axiom audits passed.
- **Parent:** SC2; separate arithmetic source data from zero geometry.

For distinct primes `p,q` and `0<d<D`, there exists a countable simple
divisor invariant under sign and conjugation, with `|Im z|≥1`,
`|Re z|<D`, and real parts cofinal at the unattained width `D`.
Every coefficient is exactly `(sinh z/z)^8` and is nonzero.
All real Laplace moments converge absolutely. The resulting kernel is
real and even, and its mixed natural two-prime cone coupling is bounded.
Its positive-height count is locally finite and satisfies

```text
N(T)=T/(2π) log(T/(2π))−T/(2π)+O(log T).
```

This is an abstract divisor. No zeta identification, Euler product, or
entire-function realization is asserted.

## Proof

Let `F(T)=T/(2π)log(T/(2πe))+7/8` and prescribe
`n_j=max(6,⌊F(j+1)⌋₊−⌊F(j)⌋₊)` points in `[j,j+1)`, for `j≥1`.
The smooth increment tends to infinity, so the reserve changes only
finitely many blocks. Prefix counts telescope to the rounded main term
plus a fixed offset. Adjacent prefixes bracket every real-height count;
the smooth unit increment is `O(log T)`, giving the stated remainder.

Use the existing exact sparse off-axis model. Each unit block contains
at most three core points, hence at most six positive-height quartet
points. Fill the remaining slots with critical-line points of distinct
rational heights `j+(k+1)/(n_j+1)`, then adjoin negative partners.
Irrationality of `π` makes every critical spline weight nonzero.
Each weight has norm at most `j⁻⁸`, while `n_j≤C(j+1)` globally;
the resulting critical coefficient series is summable by the
seventh-power series. All real critical Laplace multipliers have norm one.

An explicit block bijection identifies the literal atom series with the
original quartet kernel plus the critical-pair kernel. The former has
mixed cone coupling at most `20`; the latter at most eight times its
positive coefficient mass. This proves the bounded full-divisor coupling
without changing the off-axis core or its unattained width.

## Formalization and scope

Main theorem:
`ConeMoments/RVMCompletedSplineDivisor.lean` —
`exists_two_prime_rvm_prescribed_spline_divisor`.

Supporting modules: `RVMCompletionCounts`, `CriticalSplineSlots`,
`RVMCompletionGeometry`, and `RVMCompletionSeries`.
The count is the literal `Nat.card` of the positive-height truncation;
local finiteness is proved separately. Kernel decomposition is the exact
equality `rvmCompletion_kernel_decomposition`, with absolute convergence.

All five modules pass individual direct Lean checks. Displayed transitive
axiom audits contain only `propext`, `Classical.choice`, and `Quot.sound`.
The umbrella imports all five modules.

Corpus audit found actual Riemann–von Mangoldt counts and radial divisor
capacity bounds, but no critical-line block completion retaining this
exact spline coupling. External priority is unchecked. Actual SC2 remains
open: the counting law alone does not supply the missing rigidity.
