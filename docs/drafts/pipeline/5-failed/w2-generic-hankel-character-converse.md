# Hankel tests do not characterize generic cycle characters

- **ID:** w2-generic-hankel-character-converse
- **Stage:** 5-failed
- **Type:** FALSIFIED / EXACT POSITIVE CLASSIFICATION
- **Source:** [W2 construction](../1-in-progress/w2-representation-construction.md).
- **Statement:** Geometric cycle values pass all common-pivot tests for `|t|≤1`, but full character positivity holds exactly at `t=0` or `t=±1/m`, `m` a positive integer.

## Exact obstruction

Set `p_k=t^k`, so a cycle of length `r` contributes `t^(r−1)`.
The common-pivot Hankel matrix is `(t^r_i)(t^r_j)`, an outer product; its diagonal
is at most one for `|t|≤1`. Hence every replicated common-pivot Gram test is positive.

The full alternating projection at rank `n` is

`Σ_(σ∈S_n) sign(σ) χ_t(σ) = Π_(j<n)(1−jt)`.

For `t>0` not equal to a reciprocal integer, choose the first integer `j` with
`jt>1`. All preceding factors are positive and this factor is negative, contradicting
positivity of the sign projection. Sign twist sends `t` to `−t` and gives the other half
of the classification.

## Proof of the projection formula

For each fixed word, sum signs over its stabilizer. Distinct letters have trivial stabilizer.
If two letters coincide, multiplication by their transposition pairs stabilizer elements
with opposite signs, so the sum is zero. Uniform `m`-color words therefore have alternating
mass `m(m−1)…(m−n+1)/m^n`. The two sides of the proposed formula are polynomials in `t`
agreeing at all `t=1/m`, hence identical.

## Strongest positive survivor

The classification is exact and constructive. At `t=1/m`, use uniform independent coloring;
at `t=−1/m`, twist this character by sign. At `t=0`, use the regular character.
Thus every surviving parameter has positive Gram matrices at every rank, with no missing
representation premise.

The obstruction separates a generic moment criterion from character positivity. W2's
endpoint equivalence remains valid because it uses the actual Xi divisor, not a generic
converse from arbitrary Hankel data. This is a classical character boundary, not a novelty claim.

## Formal certificate

`formal/GaloisForLFunctions/HTGeometry/SymmetricCharacters/GeometricCharacters.lean`:

- `geometric_all_pivotGram_posSemidef`.
- `stabilizerSignSum_eq`, `sum_sign_coloring_uniform`.
- `alternatingCycleMass_geometric`, `alternatingCycleMass_nonneg`.
- `positiveCycleFamily_signTwist`, `positiveCycleFamily_geometric_iff`.

The obstruction and exact positive survivor pass direct Lean leaf checking. The module
is wired into the HTGeometry umbrella.
