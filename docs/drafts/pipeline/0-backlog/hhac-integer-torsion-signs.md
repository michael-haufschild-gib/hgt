# Integer torsion probes survive finite-rank corrections

- **ID:** hhac-integer-torsion-signs
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Statement:** Every finite-rank real bilinear correction of the weighted torsion limit leaves finitely supported integer arithmetic probes of both signs.

## Mathematical target

For every `δ>0` and finite-rank bilinear form `C` on `Hδ`, construct probes
`u₋,u₊` whose original conductor coefficients are finitely supported integers
and satisfy `(Lδ+C)(u₋,u₋)<0<(Lδ+C)(u₊,u₊)`.

This strengthens the real Hilbert-space obstruction in
[the spectral classification](../1-in-progress/hhac-weighted-torsion-spectrum.md).
It would rule out finite-rank repair even when the proposed arithmetic height
is tested only on integer cycles. It asserts no exact annihilation of arbitrary
real linear constraints by integer vectors.

## Proof mechanism and distinction

Prime-pair probes have unit integer coefficients. On a sufficiently large
finite family, the correction has a kernel containing a strictly negative
vector for the torsion form. The corrected quadratic form on the finite
coefficient space is continuous; rational approximation and clearing a common
positive denominator preserve its strict sign. Positive prime probes give the
other sign by the same argument.

The generic density step already exists as
`ArithmeticScatteringHolography.realQuad_nonneg_of_integer` in
`TheIntegerProbesOfTheHorizon.lean`; its contrapositive supplies an integer
negative vector for any finite real matrix. No novelty is claimed for this step.
The remaining obligation is its application to the actual torsion operator,
with an explicit finitely supported integer conductor certificate.

## Status

The real finite-rank sign obstruction is under formalization. Integer
coefficient certificates and this exact stronger conclusion are not formalized.
The positive content remains the arithmetic prime-pair matrices and the
compact-operator and Hilbert–Schmidt classification, rather than a restated sign failure.
