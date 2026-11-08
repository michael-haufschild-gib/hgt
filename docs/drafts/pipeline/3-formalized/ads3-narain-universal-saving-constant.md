# A universal arithmetic saving constant for all target averages

- **ID:** W11-NQU
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Quantitative saving](ads3-narain-quantitative-boundary-saving.md)

## Theorem

Put `w(L)=(log L)^(−2/3)(log log L)^(−5/3)/10^8` and
`R_YZ(y)=yA_YZ(y)+(3/π)log y−B_YZ`. For every positive target pair,
there is `C>0` such that, eventually as `y→0+`,

`|R_YZ(y)|≤C√y exp(−Lw(L)/128)`, `L=−log y`.

The exponent constant is explicit and independent of target heights;
prefactors and thresholds may depend on them.

## Proof

The contour uses `d_δ(L)=min(min(δ,1),w(2L+1))/8`, for some fixed
`δ>0`. The corpus’s `vkHadamardWidth_le` supplies a threshold for
`w(T)≤ε` for every `ε>0`. Thus eventually
`d_δ(L)=w(2L+1)/8≥w(L)/64`, by the proved doubling estimate.

Polynomial absorption loses only half of `d_δ(L)L`. Its threshold may
depend on `δ` and polynomial degree, but the remaining exponent is at
least `Lw(L)/128`. The discarded exponential tail is smaller. The
actual-source contour and exact Fourier normalization give the theorem.
No target-scaling identity is needed.

## Lean

- `NarainUniversalVKAbsorption`: eventual raw-width identity, universal retained fraction and explicit absorption exponent.
- `NarainAverageUniversalVKRate`: actual boundary integral and physical source bounds, including elementary logarithmic normalization.

Both modules passed final direct Lean checks and are imported by the
umbrella. All six endpoint axiom audits contain only `propext`,
`Classical.choice` and `Quot.sound`.

The [complex-clock refinement](../1-in-progress/ads3-narain-logarithmic-derivative-saving.md)
remains under formalization. Its target is
`|H^(n)(L)|≤C n! (π/16)^(−n) exp(−Lw(L)/128)` with one threshold
for every derivative order. The scalar theorem supplies no fixed power
above `1/2`.

## Gates

- [x] 0 → 1: actual contour, width threshold, doubling and polynomial absorption audited.
- [x] 1 → 2: universal scalar saving and exact source normalization proved.
- [x] 2 → 3: final direct Lean checks, transitive axiom audits and umbrella imports.
