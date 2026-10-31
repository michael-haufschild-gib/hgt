# Affine shell correlations select conductor quotients

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** [Q1/O1](three-frontier-questions-full-solutions.md).

For positive `m,l` dividing a common period `M`, conjecture the exact identity

`sum_(n<M)c_m(n)c_l(kn+h)`
`=1_(m=l/gcd(l,k)) M c_l(h)`.

Thus a dilation retains precisely the reduced conductor `l/gcd(l,k)`;
the successor shift retains the full coefficient `c_l(h)`. Expanding finite
packets would give every mixed entry of the complete-period shell form.

Primitive Fourier expansion reduces the mean to root pairs
`z w^k=1`. The power `w^k` has exact order `l/gcd(l,k)`; when that order is
`m`, its inverse supplies the unique matching primitive root. Summing the
remaining `w^h` gives `c_l(h)`.

Lean verification is pending. A complete-period identity alone does not
control the finite logarithmic shell boundary or the complete Weil form.
