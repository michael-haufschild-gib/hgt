# Exact bounds for the exponential theta aperture profile

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Wall:** Σ6

Let `w(r)=sinh(r/4)+(r/4)cosh(r/4)`, let `G(c,q)` be the
[averaged radial square profile](../3-formalized/exponential-tail-square-profile.md),
and put

`A(c,x)=4πx^(−1/2)∫_(r>0)w(r)G(c,x exp r)dr`.

For `x>0`, `0<c≤1`, this integral converges absolutely and

`x^(7/8)A(c,x)≤1024π c^(−39/8)Γ(39/8)exp(−cx)`.

For `N≥1`, `D≥3`, `0<q≤ND`,

`G(1/N,q)≥N^(9/2)T_(7/2)(2,D)>0`.

If also `x exp 2≤ND`, integration over `1≤r≤2` gives

`x^(1/2)A(1/N,x)≥4πw(1)N^(9/2)T_(7/2)(2,D)`.

## Proof

The exact aperture satisfies `w(r)≤4exp(5r/16)` for `r≥0`.
Raise the radial power by `3/8` in the exponential-tail estimate.
For `q=x exp r`, cancellation of the two exponential center powers leaves

`w(r)G(c,x exp r)≤16 c^(−39/8)Γ(39/8)x^(−3/8)exp(−cx)exp(−r/16)`.

The last factor has integral `16`; multiplication by the aperture
prefactor gives the upper bound.

For `u≥3`, `(2u−3)²+12(1−c)u≥u²`. The polynomial kernel is integrable,
being a finite linear combination of exponential power kernels. Restrict
its nonnegative integral to `u>ND`, then use exact scaling to obtain the
radial lower bound. On `1≤r≤2`, the cutoff condition holds and `w(r)≥w(1)`.
The interval has measure one, giving the aperture lower bound.

These are bounds for the exponential profile. Interchange with the literal
frequency-weighted Bessel aperture series is not asserted here.

## Lean

`CompletedArithmeticForms/ThetaExponentialApertureProfile.lean` proves
`integrableOn_quarter_aperture_exponentialProfile`,
`thetaExponentialApertureProfile_weighted_upper`,
`besselFirstAtomExponentialTail_scaled_lower`, and
`thetaExponentialApertureProfile_weighted_lower`.
Final file check passed; capstone axiom audits contain only
`propext`, `Classical.choice`, and `Quot.sound`.
