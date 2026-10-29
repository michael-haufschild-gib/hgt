# Centred physical square source: Gamma plus detail mass

- **ID:** acs-centered-square-source-gamma-mass-bound
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Set
  `Q(f)=S₂(f)−(∫f)²/2−m(0)∫f²`. For every ε>0 there is C≥0,
  independent of supports, such that all real compact BV f,h satisfy
  `|Q(f+h)−Q(f)−Q(h)|≤ε(Γf+Γh)+C∫h²`.

## Proof

First let f,h be real smooth compact profiles. Their exact square-source
boundary identity and Plancherel give

`Q(f)=∫(m(2πξ)−m(0))|Ff(ξ)|² dξ`.

All three centred spectral densities for f,h,f+h are integrable: each is
the difference of the proved regular square density and m(0) times its
integrable square Fourier mass. Fourier linearity and complex norm-square
polarization give the mixed integrand

`2(m(2πξ)−m(0)) Re(Ff(ξ) conj(Fh(ξ)))`.

Its absolute value is at most
`2|m(2πξ)−m(0)||Ff(ξ)||Fh(ξ)|`. The centred multiplier theorem bounds
this by

`εγ(2πξ)(|Ff(ξ)|²+|Fh(ξ)|²)+C|Fh(ξ)|²`.

Integrate, then use the exact Gamma Fourier identity and Plancherel.
The multiplier constant C depends only on ε; it is independent of the
aperture, support, and both profiles.

For compact BV profiles, apply the same pole-preserving convolution to
both f and h. Boundedness and measurability give exact linearity of this
smoothing. A common support radius puts every smoothed pair into the same
smooth core. Existing convergence theorems give convergence of S₂, ordinary
mean, square mass, and Gamma energy. Hence Q and its mixed difference
converge, and the smooth inequality passes to the limit without changing C.

The ordinary mean and constant-multiplier corrections remain in Q. No
orthogonality of the smoothed profiles is asserted or needed.

## Arithmetic consequence

For literal pair averages and balanced details, the detail mean and mixed
ordinary inner product vanish. Then the mixed Q equals the mixed S₂.
The homogeneous projection and weighted tail-mass bounds can absorb both
terms above into any fixed share of the original complete-profile Gamma
energy. The final uniform tail result is formalized on
[the parent card](acs-square-mixed-source-lower-order.md).

## Lean verification

`ArithmeticIndexDescent/TheCenteredSquareSourceHasAGammaMassBound.lean`.

Declarations:

- `centeredSquarePrimeSource`
- `exists_centeredSquareSource_gamma_mass_core`
- `tendsto_poleSmooth_centeredSquareSource`
- `exists_centeredSquareSource_gamma_mass_bv`

Direct check passed, without diagnostics:

```
lake --old env lean GaloisForLFunctions/ArithmeticIndexDescent/TheCenteredSquareSourceHasAGammaMassBound.lean
```

No web search, novelty checks, numerical experiments or axiom checks.
