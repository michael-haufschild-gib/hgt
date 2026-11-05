# All-rank first-atom center tails

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Wall:** Σ6
- **Statement:** For every finite `N` and `r≥0`, the matrix with entries
  `∫_(s>r) Re((-i)^(j+k)) ∂ₜ^(j+k)[φ(s/2+t)φ(s/2−t)]|ₜ₌₀ ds`,
  where `φ(x)=thetaCuspSourceTerm x 1`, is positive definite.

The proved fifth even tail uses an incomplete-gamma reserve. The first
atom's pointwise signed moments fail at some order at every center
(`CompletedArithmeticForms.exists_firstAtom_signed_moment_neg`); this
does not decide the integrated tail. Complete-source tails are already
strict near the seam and beyond rank-dependent horizons
(`CompletedArithmeticForms.SeamCoercivity`).

Put `q=πexp(r)` and `K(u)=K_(iτ)(2u)`. Fourier transformation of the
literal radial pair suggests the scalar tail, up to a positive factor,

`F(q,τ)=∫_q^∞ u^(3/2)((4u²+9)K(u)+6u K'(u)) du`

`=4∫_q^∞ u^(7/2)K(u)du−6∫_q^∞ u^(3/2)K(u)du−6q^(5/2)K(q)`.

The boundary term is essential. A proof needs positivity of this entire
combination, including frequencies outside the established Bessel band.
A product-square representation of weighted Bessel tails is a candidate
mechanism; neither that representation nor the required signed comparison
has been proved here. No all-rank positivity claim is accepted.

Even a proof of this conjecture leaves the complete theta sum's unequal
atom pairs and infinite remainder to be controlled uniformly in rank.
