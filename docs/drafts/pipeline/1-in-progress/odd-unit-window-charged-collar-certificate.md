# A charged collar certificate for the odd unit window

- **ID:** odd-unit-window-charged-collar-certificate
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Wall:** Σ47
- **Statement:** Every real odd `C²` function supported in `[-1/2,1/2]` has nonnegative Weil quadratic form.

## Exact target

The shifted ground-state identity supplies a positive exterior sinh charge. After cancelling weighted edges leaving the window, prove that the remaining charge and Lévy energy dominate the negative prime-2 collar term. No verified-zero input is allowed in this certificate.

## Established inputs

- `fullZeroForm_shiftedGroundState_ge`: the complete charged lower bound.
- `outsideCharge_pos`: the exterior charge is strictly positive.
- `kick_add_collarLevyEnergy_nonneg`: the negative reflected kick is localized to its collar.
- `odd_unit_nonneg_iff_markov_hankel`: equivalent half-window inequality, retaining the exact Gamma squares and prime-2 correlation.
- `SpacingScaleHarmonicAnalysis.archLevyDensity_ge_inv_two_mul`: `ω(t)≥1/(2t)` for `0<t≤1`, covering every distance inside the unit window's prime-2 collar.

## Open proof obligation

The untruncated shifted gauge has weighted prime edges outside the window. Its reflected difference energy cannot be replaced by the prime-2 term without cancelling those exterior edges against the source. After that cancellation, an unconditional quantitative comparison with the negative collar conductance is required. Positivity of the exterior charge alone proves neither step.

An alternative is to retain the positive part under collar reflection while paying its antisymmetric part with the exact short-distance Lévy bound. The remaining archimedean potential and pole moment still require a joint estimate.
