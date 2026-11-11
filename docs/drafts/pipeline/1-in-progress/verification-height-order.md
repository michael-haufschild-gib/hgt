# The order of the verification height

- **ID:** A132
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `docs/reports/review-1111/obstacles-summary.md` §2.1; walls Σ171.

## Target

RH verified through `H(a)` with `log log H(a) = O(a)` gives Weil positivity on `[−a, a]`
(currently `windowHeight`, `log log log windowHeight(a) ~ c a^{4/3}`).

## Where the triple exponential comes from

`windowPositiveAt_of_rhVerifiedThrough` writes `W(f,f) = κ⁻¹W(f,g) + ∫|h_f|²(1 − q²/κ)(μ + P_X)`
and must control the mass of `h_f` on `|τ| ≤ T₁`, `T₁ = 4e^{E+2π} ≈ exp(4e^a)`, by values at
verified zeros. Two steps are each triple exponential:

1. **Gaps.** Nodes need a zero in every interval of length `σ = 48⁻⁴/(9a)`. The gap theorem
   (`exists_zero_near_of_onLine`) supplies this only above
   `gapHeight σ ≈ exp(c·e^{Y})`, `Y = gapScale σ ≍ σ^{−4/3}`: the test of width `Y` must beat
   the primes up to `e^Y`. So nodes start at `exp(exp(c a^{4/3}))`.
2. **Extrapolation.** One Taylor–Lagrange polynomial of degree `n ≈ (node height)/σ` covers
   `|τ| ≤ T₁` from those nodes, with constant `48^{2n}`.

## Why double exponential needs a new input

Splitting the range does not suffice. Above the gap-guarantee height `G` local Lagrange blocks
have polynomial constants, but `[0, G]` must be reached by extrapolation from nodes near `G`,
at cost `exp(c a G)`; `G` is at least double exponential because a Nyquist-type gap
(`< π/a`) is guaranteed by the RH gap bound `(2π + o(1))/log log t` only for
`log log t > 2a`, i.e. above `exp(e^{2a}) ≫ T₁`. Below `T* ≈ 2πe^{2a+1}` the zeros are
sub-Nyquist for type `a` (`N(T)` versus `2aT/π`), and the margin ceiling
`exp(11a/2 − πe^{2(a−2)})` is attained there.

So `log log H = O(a)` requires one of: maximal zero gaps `≤ (π − ε)/a` at heights
`exp(e^{O(a)})` below `T₁` (beyond the RH-conditional gap bound), a finite gap certificate on
`[e^{Ca}, 2T₁]` (a premise, not a theorem), or a positivity argument that does not sample the
low band at the zeros. None is in the corpus.

## Possible survivor

A test with Fourier decay of growing order in the gap theorem lowers `gapScale` from `σ^{−4/3}`
to `σ^{−1} log(1/σ)`, giving `log log log windowHeight(a) = O(a log a)`; still triple
exponential. Not formalized.
