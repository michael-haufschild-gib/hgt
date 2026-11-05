# Primitive character windows are graded by conductor

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Wall:** Σ1j, different moduli
- **Statement:** Real parts of primitive characters of distinct positive
  moduli have identically zero cross spectrum at every common period;
  their complete critical-curve second-order cross term vanishes.

At period `M=dq`, a `q`-periodic twist has Fourier coefficient zero unless
`d|k`; at `k=dj` its coefficient is `d` times the period-`q` coefficient.
The Gauss-sum formula for a primitive character makes the latter zero
unless `gcd(j,q)=1`. Thus a nonzero coefficient has reduced frequency
denominator exactly `q`. Two distinct conductors cannot share a nonzero
coefficient, so their cross power vanishes pointwise. The existing exact
critical-curve polarization then gives the vanishing limit.

This extends the same-modulus parity grading to conductor and parity.
The Gauss-sum and polarization formulas are already formalized in
`TheSecondOrderOfACharacterWindowReadsAnLValue` and
`TheCharacterWindowsAreGradedByParity`. Period lifting and the distinct
conductor support argument remain to be formalized. Moving frequencies
are not covered by this fixed-conductor statement.
