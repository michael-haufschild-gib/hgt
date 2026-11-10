# Verified heights give explicit prime two-bump rungs

- **ID:** A56
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** An explicit cutoff `P(T)→∞` satisfies: `RHVerifiedThrough T` implies nonnegative Weil form for every cubic-spline two-bump packet with prime separation `log p`, `p≤P(T)`, and every complex second coefficient.

## Proof

The cubic spline has support radius four, so its two-bump packet at separation `log p` has aperture `4+log p/2`. Define `P(T)` as the largest integer `n≤⌊T⌋` whose aperture has sufficient height at most `T`, with value zero when none qualifies. The verified-height window theorem certifies every prime below this cutoff. For each fixed `n`, every `T≥max(n,windowHeightOfOne(4+log n/2))` admits `n`, so `P(T)→∞`.

No monotonicity assumption on the explicit height formula is needed.

## Formalization

- Module: `VerifiedHeightRungs/PrimeTwoBumpEntries.lean`.
- Declarations: `primePacketRung`, `tendsto_primePacketRung`, `prime_twoBump_nonneg_of_rhVerifiedThrough`.
- Direct `lake --old env lean` audit passed; transitive axioms are `propext`, `Classical.choice`, `Quot.sound` only.
- Imported by `VerifiedHeightRungs.lean`.
