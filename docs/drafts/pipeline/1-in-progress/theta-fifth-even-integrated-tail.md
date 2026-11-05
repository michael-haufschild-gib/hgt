# Fifth even integrated tail

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Wall:** Σ6
- **Statement:** The complete matrix
  `T₅(r) = [∫_(s>r) thetaCuspNativeSignedJet (s/2) (2(i+j)) ds]`
  is positive definite for every `r ≥ 0`.

The seam is a strict derivative Gram at every finite rank. The native fifth
section is positive from `q=πexp(r)≥5`. Global fifth-tail positivity would
pay the fifth even aperture integral and, with the proved odd fourth
section, give rank-nine positivity.

The [first-atom tail](../3-formalized/first-atom-fifth-even-tail.md) and the
[leading-pair tail](../3-formalized/leading-pair-fifth-even-tail.md) are
positive definite from `q≥3`. The latter retains ordered pairs `(1,1)`,
`(1,2)`, `(2,1)` with their exact source weights.

Write `E(q)=q^(3/2)exp(−2q)` and `A=M(0,1)>0`. The leading tail retains

`R_lead(q) ≥ E(q)L(q) + E(q)(3/(32q²)−3/(128q³))A`,

where `L(q)>0` for `q≥3`. The rate-five mass lies between
`1/5+3/(50q)+3/(500q²)−3/(5000q³)` and
`1/5+3/(50q)+3/(500q²)`; both endpoint matrices and the literal integral
identification are formalized.

Remaining: pay the other five unequal pairs among the first four atoms
and the infinite remainder. Its existing `1/20000` quadratic bound uses
scale-dependent Gaussian coordinates; transferring it to a fixed tail
quadratic form remains necessary.

The current comparison replaces the leading first-atom gamma mass by `1/2`,
releasing `3A/(8q)` as well as the cubic reserve. The reduced leading
comparison is formalized for `q≥3`; extraction from the literal tail is in
progress. Both `(1,3)` gamma endpoints become positive after adding `A/8`
at `q=3`; their ray determinant certificates remain unfinished.

The other four unequal pairs have relative rates `15,11,18,23`; the `(1,3)`
rate is `8`. Their radial polynomials have degree at most eighteen. A
candidate allocation gives `3A/(8q)` to `(1,3)`, one eighth of the cubic
reserve to each other pair, and half to the infinite remainder.

For the infinite remainder, retain the stronger Cauchy bound
`n!·20000 f₁² exp(−431q/25)/(3/20)^n` through integration. The fixed diagonal
comparison `A > 10^(−11) diag(1000^(2i))` has an exact matrix certificate.
The scalar integral bound and transfer to the literal tail remain to prove.

A smaller allocation is excluded: at `q=3`, the lower-gamma `(1,3)` model
paid by half the cubic reserve has negative fourth principal minor. This
auxiliary obstruction does not decide the complete-tail sign.
