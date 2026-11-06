# Mayer boundary exclusion by the lifted norm

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Target:** B46, zero-freeness on `Re(2s)=1` without the boundary Euler-product inequality.
- **Status:** Exact boundary theorem and Mayer consequences passed the direct production check with standard axioms. Transitive dependency audits exclude the boundary Euler-product inequality.

For `u=it`, `t>0`, write `A(u)=Λ(1+2u)` and `B(u)=Λ(2u)`.
Functional equation and conjugation give `B(u)=conj(A(u))`. A hypothetical
zero of `ζ(1+2it)` therefore annihilates both coefficients. Every term of
the exact Maass–Selberg line value contains `A` or `B`, so

`∫_fd |truncatedLineModel(it,Y,z)|² dz = 0` for every `Y≥1`.

Both constant coefficients vanish, so truncation equals the full field
at every cutoff. Zero norm gives almost-everywhere vanishing on the
fundamental domain; continuity and modular invariance give vanishing on
the entire upper half-plane. Its first nonconstant Fourier coefficient is
`2 sqrt(y) K_it(2πy)`. This is nonzero for `2πy≥|t|`, by the existing
Bessel spectral-band theorem. Taking `y=|t|+1` gives a contradiction.

The geometric field is the actual Mayer carrier: the independently proved
`MayerEisensteinLift.cauchyKernel_eisenstein_period` maps its normalized
height restriction to the literal Mayer period. Its source identity is
denominator-cleared and holds at hypothetical zeta zeros.

## Consequences

Conjugation extends zero-freeness to the whole boundary. The completed
scattering quotient satisfies `|B(it)/A(it)|=1`. Reflection also gives
`ζ(2it)≠0` for `t>0`.

For `Re w=1`, `w≠1`, the actual Mayer cofactor identity therefore resolves as

`polePart(w,1) = −2 sourceDeterminant(w,1) ζ(w−1)/ζ(w)`.

On the upper boundary the two zeta factors are nonzero, so the determinant
and pole cofactor have exactly the same zero set.

## Independence

- Zero truncated norm implies vanishing of the full field; its first
  Fourier mode gives the checked contradiction.
- The transitive audit of the Maass–Selberg norm, modular invariance,
  Fourier extraction, Bessel nonvanishing and actual Mayer lift found no
  boundary zero-free theorem or three-four-one inequality. The norm's
  absolute-chamber unfolding invokes
  `riemannZeta_ne_zero_of_one_lt_re` only where `Re(1+2u)>2`.
  Mathlib proves this by the absolutely convergent Möbius convolution
  identity `LSeries_zeta_mul_Lseries_moebius`, without an Euler-product
  inequality. It supplies no boundary nonvanishing.
- The cofactor identity and Mathlib's assigned value at the pole have
  no boundary zero-free or Euler-product-inequality dependency either.
  The proof does not use `msA_ne_zero_or_msB_ne_zero`.

## Corpus anchors

- `RHTower.integral_norm_sq_truncatedLineModel_line` and `msLineValue`.
- `RHTower.fourierCoeffOn_eisensteinLineTailPart_pos`.
- `CompletedArithmeticForms.modifiedBesselKOrder_ne_zero_on_band`.
- `RenormalizedIntersectionTheory.GaussMayerEisensteinLift`.

## Lean certificate

`RenormalizedIntersectionTheory/GaussMayerBoundaryNorm.lean`, namespace
`MayerBoundaryNorm`:

- `riemannZeta_ne_zero_of_re_eq_one` and `mayer_boundary_denominator_ne_zero`.
- `boundary_scattering_norm_one` and `boundary_shifted_zeta_ne_zero`.
- `boundary_mayer_polePart_eq` and `boundary_mayer_polePart_zero_iff`.

The direct `lake --old env lean` check passes. Transitive axioms are only
`propext`, `Classical.choice`, and `Quot.sound`. The umbrella import is wired.
