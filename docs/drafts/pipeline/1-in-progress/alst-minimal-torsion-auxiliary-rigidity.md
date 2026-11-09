# Rigidity of minimal torsion auxiliaries

- **ID:** alst-minimal-torsion-auxiliary-rigidity
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Statement:** An integer prime-coordinate polynomial of length at most `2^(qr)` with multiplicity `r` at every order-`q` torsion point is an integer scalar multiple of `(u₂^q − 1)^r` (zero if the prime-two coordinate is absent).

## Mathematical purpose
Classify equality in the full torsion support law; resolve ArithmeticHarmonicAnalysis Q2 and identify the exact auxiliaries available to ALST at the smallest admissible length. Realizes S1/S3 on the complete torsion locus, with exact multiplicity and price `2^(qr)`. Source-independent: does not separate zeta from integer-norm one-offs.

## Proof route
Fourier extraction of shifted Euler words detects any polynomial whose quotient exponents have total order below `r`. At the arithmetic boundary subtract the coefficient of `u₂^(qr)` times `(u₂^q−1)^r`. Every remaining support integer is strictly below `2^(qr)`, so detection kills the difference. This strengthens a sharp inequality to a classification; the existing boundary example alone does not prove it.

## Gates
- [x] Corpus audit: AHA has the strict support inequality and boundary example; Q2 explicitly requests classification.
- [ ] Complete paper proof, including all boundary cases.
- [ ] Lean proof and axiom audit.
