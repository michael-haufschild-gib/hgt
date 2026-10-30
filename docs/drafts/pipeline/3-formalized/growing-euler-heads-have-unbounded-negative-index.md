# Growing Euler heads have unbounded negative index

- **ID:** growing-euler-heads-have-unbounded-negative-index
- **Stage:** 3-formalized
- **Statement:** For every natural `K`, all sufficiently large heads `p≤Y` and
  horizons satisfying `K≤X` and `Y(K+1)≤X+1` admit a `K`-parameter linear
  family on which Gamma minus the complete mixed head source is strictly
  negative away from the zero parameter. Every positive log-power head
  schedule therefore has unbounded negative index.

## Proof

Use the first `K` Haar details and `K` disjoint coarse windows translated by
`log Y`. Their head coupling divided by `√Y` converges to a lower-triangular
matrix `L` with negative diagonal. Hence `Lᵀ` is injective and
`Σ(Lᵀx)²≥σ‖x‖²` for some `σ>0`.

Choose the coarse coefficients as `(s/√Y)Lᵀx`. The mixed head contribution
has a fixed negative main term proportional to `sσ‖x‖²`. The detail Gamma
cost is bounded independently of `Y`; translation invariance makes the coarse
Gamma cost `O(s²/Y)‖x‖²`. First choose `s` to dominate the detail cost, then
choose `Y` to absorb the coarse cost and coupling error. Negativity also
proves injectivity of the parameter map. Positive log-power heads grow to
infinity and eventually satisfy the required horizon inequalities.

## Lean

`ArithmeticIndexDescent/TheIndexOfAGrowingEulerHeadIsUnbounded.lean`:

- `eventually_eulerHead_negative_family`
- `eventually_logPowerHead_negative_family`

Direct named-file check passed. Both transitive axiom audits contain only
`propext`, `Classical.choice`, and `Quot.sound`. Imported by the owner umbrella.
