# Arithmetic upper bounds for the filtered prime current

- **Obstacle:** B13.
- **Stage:** 1-in-progress
- **Type:** CONJECTURE

## Required estimate

For the actual pole-and-divisor filter, find a prime-side bound smaller than
`h(t)^d K(exp(−at),ρ₀−σ−it)` at some supercritical speed. Its exponential
rate is `a(β−σ)/2−π/4−dκ` when `h(t)=exp(−κt)`.
The bound must not assume the zero exclusion it is intended to prove.

## Arithmetic candidates

The absolutely convergent Euler region gives the bound
`|A(t)| ≤ C h^d (1+t)^d exp(a(c−σ)t/2)` for each fixed `c>1`.
A Mellin–Barnes integral on `Re z=c` retains every filter factor:
`P_h(exp(h(z−β)))=O(h^d(1+|z|)^d)`.
Gamma decay makes the vertical integral finite; the literal Euler series
bounds `|ζ′/ζ(c+iv)|` independently of the exceptional divisor.
This estimate still exceeds the selected mode by exponential rate
`a(c−β)/2+π/4`. Contraction subtracts `dκ` from both rates.
Its paper proof and successful Lean audit are recorded in
`../3-formalized/b13-euler-bound-and-fast-contraction.md`.

Existing prime–pole estimates include
`ArithmeticIndexDescent.exists_screwPrimeSum_explicit_classical_rate` and
`exists_allPrimesMixedSource_all_detail_growing_coarse_rate`.
They have square-root-logarithmic savings, insufficient to bridge a fixed
power gap. Their transfer to this Gaussian filter is not assumed.

Ordinary mean-square estimates must be checked at the actual scale:
prime length `X=exp(at/2)`, height `t=2 log X/a`. Bounds requiring height
comparable to `X` do not control these readings.

## Status

The Euler bound forces decay when `dκ>a(1−σ)/2`. The exceptional-layer
growth theorem applies when `dκ<a(β−σ)/2−π/4`; the two regimes are disjoint.
No independent bound contradicting the exceptional-layer signal is proved.

An upper estimate on one unbounded sequence of heights would suffice,
because the filtered lower law holds at every sufficiently large height.
A fixed-damping mean-square limit does not establish such a sequence for
`y=exp(−at)`; the required interchange of cutoff and height limits remains open.
