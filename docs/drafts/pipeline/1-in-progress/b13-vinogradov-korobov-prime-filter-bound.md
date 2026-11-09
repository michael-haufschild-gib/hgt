# Vinogradov–Korobov saving for the complete prime filter

- **Obstacle:** B13.
- **Stage:** 1-in-progress
- **Type:** CONJECTURE

## Target

Write `w(T)=(log T)^(−2/3)(log log T)^(−5/3)/10^8`, the width actually
proved in the corpus. For `σ<1`, `a>0`, and the divisor filter of degree `d`,
prove an independent bound, uniformly for `0≤h≤1`, of the form

`|A_h(t)| ≤ C h^d (1+t)^N exp(a(1−σ)t/2 − a t w(2t+1)/4)`.

The local rectangle contains only total zeta ordinates `[t/2,3t/2]`.
Shift its left edge to `1−w(2t+1)/2`; monotonicity of `w` puts the rectangle
inside the actual zero-free region. The existing logarithmic-derivative
estimate supplies `O(log(2t)/w(2t+1))`. Gamma decay controls horizontal
edges and omitted Euler tails. All filter factors must remain before norms.

## Required consequence

Prove raw decay for contraction weakened below the previous critical rate
by a positive multiple of `w(2t+1)`:
`h(t)^d ≤ exp(−a(1−σ)t/2 + a t w(2t+1)/8)` eventually.
This is an arithmetic improvement independent of a finite-layer assumption.
The fixed exponential gap to exceptional-layer growth remains unresolved.

The explicit schedule is
`h(t)=exp((−a(1−σ)/2+a w(2t+1)/8)t/d)`.
Its degree power cancels the main exponential in the upper bound, leaving
`C(1+t)^(d+5) exp(−a t w(2t+1)/8)→0`. For this last limit, the coarse
inequality `1/w(T)≤10^8(log T)^3` suffices: every fixed power of `log T`
is dominated by `T`. The width tends to zero, so the schedule eventually
lies in `(0,1]`.

## Lean target

`ExceptionalLayerTheory/VinogradovKorobovBoundsForDampingFilters.lean`:

- `exists_primeDampingFilter_vinogradovKorobov_bound`
- `tendsto_primeDampingFilter_zero_of_vk_relaxed_contraction`
- `tendsto_primeDampingFilter_zero_of_vk_schedule`

Direct source verification remains in progress; no theorem status claimed yet.

## Sources

- `RHTower/Sieve/VinogradovKorobovLogDeriv.lean`:
  `exists_logDeriv_zeta_bound_vk`.
- `ExceptionalLayerTheory/ZeroFreeBoundsForDampingFilters.lean`:
  filter–Gamma strip envelope and the local contour mechanism.
