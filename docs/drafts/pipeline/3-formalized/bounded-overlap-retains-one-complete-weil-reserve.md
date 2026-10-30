# Bounded overlap retains one complete Weil reserve

- **ID:** bounded-overlap-retains-one-complete-weil-reserve
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** one-horizon-makes-every-bounded-overlap-positive

## Statement

For the explicit tilted unit spline and `K≥1`, there are `a>0,C≥0` and
one horizon such that the actual complete Weil form at every `1≤c≤K`
satisfies `W_N(c)/M_N(c)≥a D_N−C S_N` on every signed coefficient packet.

## Proof [PROVED HERE]

The spline Fourier transform never vanishes on the real line. Its squared
modulus therefore has a positive minimum `m` on `[1,101K]`. The existing
Dirichlet polynomial band bound, applied on `[N,101N]`, and the physical
Gram estimate give a common Gamma reserve
`Γ_N(c)/M_N(c)≥(a₀ log N−b)S_N`, with
`a₀=48m/(2πM)>0` and
`b=(GammaOffset+log 2)(1+2K exp K)`.

Put `δ=min(a₀,1/2)`. Choose one integer `L` exceeding both `4K` and
`128 exp(2)K/δ`. The prefix through `⌊N/L⌋` is separated for every
`c≤K`. Its unit self coefficient pays its logarithmic mass with defect
loss at most `δ/4`. The tail keeps the common Fourier reserve. Ordered
Gamma interaction costs at most `2π(1+2K exp K)S_N`; the source tail-mass
inequality absorbs its logarithm at cost `1+δ/4`. All remaining constants
are uniform because `0≤log c≤log K` and `c≤K`.
Thus Gamma pays the logarithmic counterterm with defect cost at most
`1−δ/2`, up to fixed square mass. The already uniform signed arithmetic
source retains `1−δ/4` of the defect. Their exact complete-form identity
leaves the positive reserve `δ/4`, with a common square-mass loss.

## Lean status

`CriticalArithmeticCorrelationTheory/BoundedOverlapKeepsACompleteWeilReserve.lean`
proves the uniform Gamma payment, complete reserve and Euclidean energy form.
Final direct Lean check passed; all four axiom audits contain only
`propext`, `Classical.choice`, and `Quot.sound`. Umbrella import is wired.
Counted only with the resulting uniform complete spectral theorem.
