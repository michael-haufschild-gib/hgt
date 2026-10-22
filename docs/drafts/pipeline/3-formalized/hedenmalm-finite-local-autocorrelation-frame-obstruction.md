# Finite local autocorrelation frames cannot orient the Hedenmalm current

- **ID:** `hedenmalm-finite-local-autocorrelation-frame-obstruction`
- **Stage:** 3-formalized
- **Type:** THEOREM / POSITIVE CARRIER NECESSITY LAW
- **Scientific status:** `[PROVED] [LEAN] [NOVELTY PROVISIONAL] [BRIDGE CORE]`
  `[NOT AN RH PROOF]`
- **Parent:** `hedenmalm-center-mixed-double-positivity-law.md`

## Claim under attack

Let

```text
X(w)=xi(1/2+w),
f_a(x)=exp(a x)k(x),
0<a<1/2,
```

where `k` is Hedenmalm's normalized theta source.  The center-mixed density is the first transverse
variation of the autocorrelation of `f_a`, and its Fourier transform is

```text
partial_a |X(a+i b)|^2.                                  (1)
```

Suppose `(1)` admitted a finite local autocorrelation-frame factorization made from
constant-coefficient differential transforms of `f_a`.  Fourier transformation would give

```text
partial_a |X(a+i b)|^2
  =|X(a+i b)|^2 Q(b),                                    (2)
```

where `Q` is a finite sum of polynomial modulus squares.  Schwarz reality and central evenness
then analytically continue `(2)` to a polynomial finite-difference relation for `X'/X`:

```text
(X'/X)(w)-(X'/X)(w-2a)=P(w).                             (3)
```

The polynomial right side has no poles.  Hence every zero of `X` must propagate under the
nonzero translation `w -> w-2a`, with multiplicity.  Iteration leaves the critical strip, which
is impossible for a zero of `xi`.

The spectral-density conclusion is now unconditional and stronger than the original finite claim:

> The horizontal Xi derivative at any positive aperture cannot be a multiple of `|xi|^2` by any
> entire spectral density.  In particular, it cannot have a finite Gram density whose entries are
> constant-coefficient polynomial spectral symbols.  Every successful source factorization must
> carry a non-entire transverse divisor singularity; nonlocality or infinite dimension alone is
> insufficient if the resulting density still extends holomorphically.

The spatial statement is now unconditional for the actual theta source.  For every `0<a<1`, let

```text
k_a(x)=exp(-a x)k(x),
dot k_a(x)=-x k_a(x).
```

Both are concrete Schwartz functions.  The first variation

```text
Corr(dot k_a,k_a)+Corr(k_a,dot k_a)
```

cannot equal a finite sum of autocorrelations of constant-coefficient polynomial differential
filters applied to `k_a`.  Fourier transformation gives `(2)` exactly, and the entire-coboundary
obstruction then gives the contradiction.  No abstract source, Plancherel, sign, or reconstruction
hypothesis remains in the theorem.

## Competing mechanisms and attacks

1. **Positive mixture of raw center slices.**  This fails as a universal mechanism by Hudson
   rigidity: the unmixed Wigner fibers cannot all be positive for the non-Gaussian theta source.
2. **Positive Hecke element.**  The divisor characters are self-adjoint principal-series
   characters, but their pointwise values change sign and the archimedean Bessel coefficient also
   depends on the spectral parameter.  No source-independent positive Hecke element has been
   isolated.
3. **Finite local differential frame.**  This is the present target.  Unlike the first two
   reformulations, it predicts the concrete forbidden divisor translation `(3)` and can be
   attacked without assuming RH or positivity.

## Proof obligations

- [x] prove in Lean that the completed Xi logarithmic flux admits no nonzero real-shift polynomial
      coboundary;
- [x] prove the zero-propagation lemma without a simplicity hypothesis;
- [x] strengthen polynomial coboundary exclusion to every entire spectral multiplier;
- [x] formalize the finite polynomial spectral Gram and prove its nonexistence at every positive
      aperture;
- [x] formalize the Fourier transform of finite constant-coefficient differential
      autocorrelation frames on Schwartz space;
- [x] prove that every exponential tilt `exp(a x) k(x)`, `|a|<1`, of the actual theta-cusp
      source is a Schwartz function with explicit residual decay rate `1-|a|`;
- [x] prove the complex Fourier--Laplace identity
      `Fourier(exp(a x) k(x))(b)=XiC(b+i a)` without a source interface;
- [x] derive `(3)` from `(2)` using Schwarz reality, central evenness, and analytic continuation;
- [x] combine the preceding results into the unconditional no-frame theorem;
- [ ] audit finite-frame spectral factorization, exponential-polynomial difference equations,
      and de Branges/canonical-system literature before making any novelty claim.

## Publication boundary

The entire-coboundary obstruction has an elementary divisor-rigidity core.  Scientific significance
can attach only to the resulting source classification: a Hedenmalm--Hilbert--Polya orientation
must use a non-entire, divisor-sensitive, cofinal arithmetic carrier.

## Preliminary parent-theory and literature audit

The meromorphic parent mechanism is elementary: if a logarithmic-derivative difference is entire,
its pole residues force translation invariance of the zero divisor.  Difference-Nevanlinna theory
provides much broader growth and value-distribution results for shifts and logarithmic differences,
including Halburd--Korhonen and Chiang--Feng, but the searched primary sources do not state the
finite polynomial spectral-frame obstruction for the Riemann Xi horizontal derivative.

The June 2026 theta-kernel preprint of Planat reformulates horizontal Xi growth as a two-variable
oscillatory theta-kernel problem and isolates its positive and oscillatory sectors.  It does not
classify finite differential or polynomial spectral Gram factorizations.  The present theorem is
therefore provisionally new as an application and carrier classification, but its proof core is a
`[BRIDGE]` until a wider specialist audit clears difference equations, translation-invariant local
operators, and spectral factorization.

Primary comparison points:

- R. G. Halburd and R. J. Korhonen, *Difference analogue of the lemma on the logarithmic
  derivative with applications to difference equations*, arXiv:math/0504245.
- Y.-M. Chiang and S.-J. Feng, *On the growth of logarithmic differences, difference quotients and
  logarithmic derivatives of meromorphic functions*, arXiv:math/0610480.
- M. Planat, *A Theta-Kernel Positivity Reformulation of the Growth Theorem and the Riemann
  Hypothesis*, doi:10.20944/preprints202606.0062.v1.
- H. Hedenmalm, *Spectral interpretation of Riemann zeta zeros*, arXiv:2606.17494.
- W. Lawton, *Spectral Factorization and Entire Functions*, arXiv:1906.06087.

Hedenmalm's preprint constructs the theta differential eigenvalue problem and leaves the
sesquilinear orientation as the missing Hilbert--Polya input.  It contains no moment,
autocorrelation, or finite differential Gram-factorization theorem.  Lawton's paper and the
Fejer--Riesz/Ahiezer line concern existence of spectral factors for nonnegative functions; they do
not address the Xi horizontal derivative or its forced translated-divisor singularities.  The
exact Hedenmalm source-space obstruction was not found in these primary comparison points.
Novelty therefore remains provisional at the application level, while the proof mechanisms are
classified as bridges.

## Honest significance score

The strengthened result scores `76--84/100`.  It excludes every entire spectral density, proves the
finite local-frame obstruction for the actual tilted Hedenmalm source, and handles the Xi divisor
without simplicity.  Its residue and Fourier cores remain classical, it does not classify every
continuous local operator, and it supplies no sign theorem.  It does not clear the `90/100`
publication gate.

## Formal theorem surface

The unconditional layer is in
`formal/GaloisForLFunctions/RHTower/XiFiniteLocalSpectralFrameObstruction.lean`:

```text
polynomialSpectralSquare_eval_real
xi_zero_shift_of_entireFluxCoboundary
no_XiEntireFluxCoboundary_of_pos
xi_zero_shift_of_polynomialFluxCoboundary
no_XiPolynomialFluxCoboundary_of_pos
entireFluxCoboundary_of_entireHermitianDiagonalLaw
no_XiEntireHermitianDiagonalLaw_of_pos
polynomialFluxCoboundary_of_hermitianDiagonalLaw
no_XiPolynomialHermitianDiagonalLaw_of_pos
not_XiFiniteLocalPolynomialSpectralFrame_of_pos.
```

The zero-propagation proof uses the residue-filled completed-flux germ, so repeated Xi zeros are
handled without a simplicity assumption.  No RH, positivity, zero enumeration, or hidden analytic
interface is assumed.

The generic spatial harmonic-analysis layer is formalized in
`formal/GaloisForLFunctions/HTGeometry/SchwartzPolynomialDifferentialFrame.lean`.  Its theorem
`fourier_finitePolynomialAutocorrelationFrame` proves that every finite normalized differential
autocorrelation frame has spectral density `sum_j |p_j(i t)|^2`; the same module constructs
cross-correlation and its first variation.

The actual tilted source and its Fourier--Laplace continuation are formalized in

```text
formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspTiltedSchwartz.lean
formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspFourierLaplace.lean.
```

The latter proves strip analyticity by dominated differentiation and identifies the whole strip
with `XiC` by the identity theorem.  The source-space capstone is in
`formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmLocalFrameObstruction.lean`:

```text
fourier_thetaCuspRightLineSource_scaled
fourier_thetaCuspRightLineTangent_scaled
fourier_thetaCuspHorizontalAutocorrelationTangent_scaled
xiFiniteLocalPolynomialSpectralFrame_of_spatial_identity
no_finitePolynomialAutocorrelationFrame_for_Hedenmalm_tangent.
```

All source objects and Fourier identities are explicit.  No hard proposition is hidden behind a
realization interface.
