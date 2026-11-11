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

## What the margin bound must be

In `W(f,f) = κ⁻¹W(f,g) + ∫|h_f|²(1 − q²/κ)(μ + P_X)` the zero side must pay `D·∫_{|τ|≤T₁}|h_f|²`
up to a fixed fraction of `∫|f|²`: `∫_{|τ|≤T₁}|h|² ≤ K Σ_γ q(γ)²|h(γ)|² + c₀‖h‖²` on `PW_a`. Then
`b ≍ K^{−1/2}` and the tail `b⁻⁶H⁻⁴` give `log log H = O(log log K)`; so `K = exp(e^{O(a)})` is the
target. The prolate bound (`2e^{2a}` missing degrees of freedom below `T* = 2πe^{2a}`) shows
`K ≥ exp(c e^{2a}/a)`, so the order is right. Any single interpolation from nodes at height `G`
costs `exp(caG)`; `K` must come from local sampling. Local sampling needs separated zeros at
density `> a/π` in windows of bounded length: Counting alone cannot supply it: clusters of size `K = C log t/log log t` at spacing
`2πK/log t > π/a` are compatible with `S(t) ≪ log t/log log t`, and on such a lattice
`sin(πu/s)φ(u)` (`φ` of type `a − π/s`) vanishes at every zero.

The explicit formula excludes that adversary: for `h ∈ PW_a`,
`Σ_γ |h(γ)|² = ∫|h|²S/2π + poles − tail`, `S = log-density − 2P`, `P` the prime sum of length
`e^{2a}`. So at resolution `1/(2a)` the zero measure is the symbol, and a Beurling–Selberg
minorant of type `2a` (integral `2δ − π/a`) puts a zero in every interval of length `π/a + ε` wherever
the smoothed symbol is `≥ η log τ`: exactly Nyquist, so gap-based sampling stays borderline and
the margin is the smallest eigenvalue of the symbol form `∫|h|²S/2π + poles` on `PW_a`. The margin is then governed by the near-zero set of the smoothed symbol
in `[T*, T_a]`, i.e. by how closely `2P(τ)` can approach `log τ` there (simultaneous
approximation of `τ log p`, `p ≤ e^{2a}`). Missing: a lower bound `exp(−e^{O(a)})` for that
eigenvalue, i.e. quantitative Weil positivity at scale `a`; RH through `H` only gives `≥ −tail`.
Not in the corpus.

## Possible survivor

A test with Fourier decay of growing order in the gap theorem lowers `gapScale` from `σ^{−4/3}`
to `σ^{−1} log(1/σ)`, giving `log log log windowHeight(a) = O(a log a)`; still triple
exponential. Not formalized.
