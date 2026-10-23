# Uniform product-weight CRT transfer fails at full height

- **ID:** twin-prime-uniform-full-height-crt-transfer
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** [certified boundary](../3-formalized/twin-prime-full-height-crt-boundary.md).
- **Statement killed:** A period-transfer error `o(X)` uniform over bounded product weights on all odd divisors up to the physical horizon.

## Exact obstruction

For `T>=12`, set `X=8T+2` and `d_i=4T+3+2i`, `0<=i<2T`.
Take both coefficient sequences equal to one on this odd block.
The actual incidence count is `2T-1`; the compatible period
contribution is at most `(8T+1)25/144`. Consequently their
difference divided by `X` is at least `1/20`.

This refutes the proposed uniform extension of the balanced CRT
bound. It does not refute the balanced theorem, the four-long-variable
operator conjecture, or a source-specific bound for the complete
Möbius sum.

## Positive survivor and closure

- **Exact killing mechanism:** At `X/2+2<=d,e<=X`, both positive
  complementary quotients must equal one. The incidence kernel
  is exactly `[e=d+2]`.
- **Strongest positive survivor:** Complete shift-kernel
  classification for every horizon, its bilinear identity for
  arbitrary real weights, and the explicit uniform linear and
  normalized discrepancy lower bounds.
- **New insight:** The full-height endpoint is a shifted scalar
  correlation, not an inverse-residue averaging problem. Its
  compensation must involve the actual source.
- **Second positive pass:** The complete Möbius zero sum transfers
  the damping weight to the cofactor; that weight vanishes at
  one. The isolated boundary block need not be estimated on its
  own. The source-specific problem survives on growing nonunit
  cofactors, with mixed terms retained.
- **Status:** Complete elementary paper proof and unconditional
  Lean certificates in `twin-prime/FullHeightCRTBoundary.lean`.
  `upperHalfCrtKernel_eq_shift`, `upperHalfCrtForm_eq_shift`,
  `fullHeightOddDivisor_odd`, `fullHeightOddCrtDefect_lower`, and
  `fullHeightOddCrtDefect_normalized_lower` passed the leaf and
  foundational-axiom audits. No scientific novelty claimed.

The surviving analytic target is recorded in
[nonunit cofactor dispersion](../1-in-progress/twin-prime-nonunit-cofactor-dispersion.md).
Twin-prime infinitude remains open.

## Log

- 2026-10-23 — Closed the uniform full-height extension only after
  formalizing the exact positive boundary and checking the
  full-source compensation that survives it.
