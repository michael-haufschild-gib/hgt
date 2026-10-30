# Prime boundary errors have polynomial harmonic bounds

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** fixed-conductor-packets-remain-positive-at-growing-overlap

## Statement and proof

For any integer strip width `B`, the exact cutoff replacement error has
normalized squared row mass at most `K_m(B+1)⁶/√(log N)` when `log N≥1`
and `0<c≤N`.

The reciprocal Mangoldt mass in `[Y−B,Y+B+1]` is at most `2B+2`.
For `Y≥2B+2`, every index is at least `Y/2`; using
`Λ(k)≤log k` and `log k/√k≤2` improves this to `8(B+1)/√Y`.
The exact cutoff error is bounded by `4Bϕ(m)` times this mass.

Put `L=log N`, `b=B+1`, and split rows at real quotient `N/n=4bL²`.
Since `N/n<2 floor(N/n)`, the good range has `floor(N/n)≥2bL²`,
giving numerator bound `32ϕ(m)b²/L`; globally `32ϕ(m)b²` suffices.
The harmonic cutoff bound gives
`D²b⁴[(1+L)/L²+1+log(8bL²)]`, with `D=32ϕ(m)`.
Use `log L≤2√L`, `1+log(8b)≤8b`, `b≥1`, `L≥1` to bound this by
`14D²b⁶√L`. Division by `L` proves the result.

## Lean status

`PrimeBoundaryErrorsHavePolynomialHarmonicBounds.lean` proves
`primeIndexBoundaryMass_le_sqrt` and
`exists_linearizedUpwardCoefficient_boundary_polynomial_harmonic_bound`.
Final direct Lean audit passed without warnings; both axiom audits contain
only `propext`, `Classical.choice`, `Quot.sound`. No separate count.
