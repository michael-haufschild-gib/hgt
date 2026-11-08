# A universal arithmetic saving constant for all target averages

- **ID:** W11-NQU
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** [Quantitative saving](../3-formalized/ads3-narain-quantitative-boundary-saving.md)

## Conjecture

Put `w(L)=(log L)^(−2/3)(log log L)^(−5/3)/10^8` and
`R_YZ(y)=yA_YZ(y)+(3/π)log y−B_YZ`. For every positive target pair,
there is `C>0` such that, eventually as `y→0+`,

`|R_YZ(y)|≤C√y exp(−Lw(L)/128)`, `L=−log y`.

The exponent constant is explicit and independent of target heights;
prefactors and thresholds may depend on them. A stronger refinement,
using the proposed complex-clock disk estimate, has the same constant
for every clock derivative:

`|H_YZ^(n)(L)|≤C n! (π/16)^(−n) exp(−Lw(L)/128)`

for every `n≥0` and every `L≥L₀`, with `C,L₀` depending only on `Y,Z`.

## Mechanism

The existing contour uses `d_δ(L)=min(min(δ,1),w(2L+1))/8`, for some
fixed positive `δ`. The corpus's `vkHadamardWidth_le` supplies an explicit
threshold for `w(T)≤ε`, for every `ε>0`. Hence eventually
`d_δ(L)=w(2L+1)/8≥w(L)/64`, using the proved doubling estimate.
The factor `min(δ,1)` in the earlier lower bound is unnecessary
asymptotically.

The already proved polynomial absorption loses only half of `d_δ(L)L`.
Its threshold may depend on `δ` and polynomial degree, but the remaining
exponent is at least `Lw(L)/128`. The discarded exponential tail is
smaller. Applying the existing actual-source contour and exact Fourier
normalization yields the scalar candidate.

The [complex-clock refinement](ads3-narain-logarithmic-derivative-saving.md)
would give the derivative statement on fixed disks, followed by Cauchy's
estimate. Neither argument needs the proposed target-scaling identity
or a uniform bound on target-dependent prefactors.

The exact eventual-width identity, strengthened absorption and source
conclusion still require Lean verification. No fixed power above `1/2`
is claimed.

## Gates

- [x] 0 → 1: actual contour, width threshold, doubling and polynomial absorption identified.
- [ ] 1 → 2: universal scalar saving and factorial derivative refinement proved.
- [ ] 2 → 3: direct Lean checks, transitive axiom audits and umbrella imports.
