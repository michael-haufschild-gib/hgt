# Harmonic quotient tails cost a logarithm

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** fixed-conductor-packets-remain-positive-at-growing-overlap

## Statement and proof

For `N≥1` and `T≥1`,

`Σ_(1≤n≤N, N/n<T) 1/n ≤ 1+log(2T)`.

Put `M=floor(N/T)`. The sum is at most `H_N−H_M`. If `M=0`,
then `N<T`, and `H_N≤1+log N≤1+log(2T)`. Otherwise
`M≥N/(2T)`. The harmonic bounds `log M≤H_M` and
`H_N≤1+log N` give the result.

Consequently, if `|R_n|≤B/√n` everywhere and `|R_n|≤A/√n`
when `N/n≥T`, then

`Σ_(n≤N) R_n² ≤ A²(1+log N)+B²(1+log(2T))`.

Square the two row bounds and sum after splitting at the quotient cutoff.
The tail cost stays logarithmic even when `T` grows with `N`.

## Lean status

`HTGeometry.HarmonicQuotientTailBound` proves
`harmonic_quotient_tail_le` and `sum_sq_le_harmonic_quotient_tail`.
Final direct Lean check passed without warnings; both dependency audits
contain only standard logical axioms. HTGeometry umbrella wired.
Supporting norm transfer; no separate contribution count.
