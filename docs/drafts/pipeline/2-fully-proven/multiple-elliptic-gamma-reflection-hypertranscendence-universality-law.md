# Multiple elliptic Gamma reflection--hypertranscendence universality law

## Status

Fully proven on paper; formalized in Lean 4.

## Theorem-first source

- `hypertranscendentalOver_multipleEllipticGammaMero_of_rankThreeMinor`: a finite period family
  containing two periods rationally independent with `1` gives a hypertranscendental genuine
  multiple elliptic Gamma meromorphic element.
- `hypertranscendentalOver_multipleEllipticGammaLogDerivMero_of_rankThreeMinor`: its logarithmic
  derivative is hypertranscendental over the rational coordinate field as well.
- `multipleEllipticGammaProduct_reflection`: reflection through the sum of periods inverts the
  product in even rank and fixes it in odd rank.
- `multipleEllipticGammaProduct_mul_reflection_of_even` and
  `logDeriv_multipleEllipticGammaProduct_reflection`: regular-locus product-one and uniform
  `(-1)^rank` logarithmic-derivative reflection laws.

Hypertranscendence and reflection parity were terminal in separate modules; no corpus theorem
classified them simultaneously on the same all-order object.

## Universal law

Every finite upper-half-plane period family with a rank-three minor produces a
hypertranscendental multiple elliptic Gamma and a hypertranscendental logarithmic derivative,
while the same pointwise product obeys a complete rank-parity reflection classification.  Even
rank gives a reciprocal reflection cocycle and product one wherever both all-order products are
regular.  Odd rank gives a reflection-fixed product.  At every rank the logarithmic derivative
transforms by `(-1)^rank`.

## Paper proof

The rank-three-minor face argument supplies both hypertranscendence statements.  Reflection swaps
every forward and backward product atom.  The genuine product is their quotient in even rank and
their product in odd rank, yielding reciprocal and fixed reflection respectively.  Nonvanishing
of both products makes the even-rank reciprocal identity a product-one law.  Differentiating at
the logarithmic level, with reflected regularity inherited by swapping the two products, yields
the uniform parity sign.

## Lean formalization

- Module:
  `GaloisForLFunctions.HTGeometry.MultipleEllipticGammaReflectionHypertranscendenceUniversalityLaw`
- Theorem:
  `GaloisForLFunctions.multipleEllipticGamma_rankThreeMinor_reflectionHypertranscendenceUniversality`
- Exact check:
  `lake env lean GaloisForLFunctions/HTGeometry/MultipleEllipticGammaReflectionHypertranscendenceUniversalityLaw.lean`
  passed on 2026-07-22.

## Novelty audit

Pending literature audit after theorem-generation phase. Corpus audit is negative.
