# Continuum matrix spectral block Hankel positivity

- **ID:** `continuum-matrix-spectral-block-hankel`
- **Stage:** 3-formalized
- **Type:** THEOREM, `[BRIDGE]`, multi-field continuum observability
- **Scientific status:** `[PROVED] [FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lean module:** `GaloisForLFunctions.HTGeometry.ContinuumMatrixSpectralHankel`

## General integral-Gram law

Let `f_i(omega)` be a finite family of real spectral features over a positive measure `mu`.
Define

```text
G(i,j) = integral f_i(omega) f_j(omega) dmu(omega).
```

If every pairwise product is integrable, then for every coefficient vector `x`,

```text
x^T G x = integral (sum_i x_i f_i(omega))^2 dmu(omega).    (1)
```

Equation `(1)` proves that `G` is positive semidefinite.  If every nonzero coefficient vector
produces a feature combination whose support has positive `mu`-measure, then the integral is
strictly positive, `G` is positive definite, and `det G > 0`.

The strictness hypothesis is an exact observability condition: no nonzero finite reporter
combination is invisible almost everywhere.  It is not an assumption about a flow, field
equation, or time evolution.

## Continuum multi-field specialization

For a latent spectral state `omega`, a transfer node `r(omega)`, and channel couplings
`g_a(omega)`, define the joint clock-channel features

```text
f_(i,a)(omega) = g_a(omega) r(omega)^i.
```

The matrix-valued moments and their block Hankel matrix are

```text
M_k(a,b) = integral g_a g_b r^k dmu,
H((i,a),(j,b)) = M_(i+j)(a,b).
```

The formal theorem identifies `H` exactly with the integral Gram matrix of the features
`f_(i,a)`.  Pairwise integrability therefore gives `H >= 0`; positive-measure separation of all
nonzero joint combinations gives `H > 0` and `det H > 0`.

This is the continuum extension of the existing finite-line module
`FiniteMatrixSpectralHankel`.  Together they cover discrete particles or resonances, mixed
discrete-continuum spectra, and continuous spectral densities.

## Pole-plus-continuum composition

Integral Gram matrices are additive in the positive spectral measure.  Therefore, if one
component is jointly separating and a second component is only positive semidefinite, their sum
is still positive definite:

```text
strict component + positive component = strict mixed spectrum.       (2)
```

This is the precise pole-plus-cut law needed for particle poles plus multiparticle continua,
black-hole quasinormal poles plus branch-cut tails, and discrete-plus-archimedean source splits.
Only one component must provide strict observability; adding positive spectral material cannot
destroy it.

## Direct scalar-corpus extraction

For every individual field/reporter channel `a`, its scalar Hankel moment matrix is a principal
submatrix of the joint block matrix.  Hence joint continuum separation proves

```text
det Hankel(channel a, n) > 0                               (3)
```

for every finite size `n`.  This is not an isolated matrix API: equation `(3)` discharges the
strict scalar determinant input used throughout the existing moment, recurrence, finite-state,
and RH-facing spectral modules whenever a target moment sequence is identified with one channel.
The same scalar extraction holds for a mixed measure under equation `(2)`.

## Physics scope and provenance

The representation applies to:

- matrix-valued Kallen--Lehmann and Euclidean correlators;
- mixed scalar, Higgs, inflaton, vector, fermion, and graviton channels;
- multi-field EFT dispersion positivity;
- lattice QCD variational correlation matrices;
- multi-reporter black-hole, neutron-star, and gravitational-wave spectra;
- general continuum relaxation and passive-response reporters.

Primary literature:

- X. Li, H. Xu, C. Yang, C. Zhang, and S.-Y. Zhou, *Positivity in Multi-Field EFTs*,
  Phys. Rev. Lett. 127 (2021), 121601, DOI 10.1103/PhysRevLett.127.121601.
- S.-L. Wan and S.-Y. Zhou, *Matrix moment approach to positivity bounds and UV reconstruction
  from IR*, arXiv:2411.11964.
- R. Abbott, W. I. Jay, and P. R. Oare, *Moment problems and bounds for matrix-valued smeared
  spectral functions*, arXiv:2508.01377.

## Lean surface

- `integralFeatureGram`
- `integralFeatureCombination`
- `integralFeatureGram_quadratic_eq_integral_sq`
- `integralFeatureGram_posSemidef`
- `integralFeatureGram_posDef_of_support`
- `integralFeatureGram_add_measure`
- `integralFeatureGram_add_measure_posDef_of_left_support`
- `continuumMatrixSpectralMoment`
- `continuumMatrixSpectralBlockHankel`
- `continuumMatrixSpectralFeature`
- `continuumMatrixSpectralBlockHankel_eq_integralFeatureGram`
- `continuumMatrixSpectralBlockHankel_posSemidef`
- `continuumMatrixSpectralBlockHankel_posDef_of_jointSeparation`
- `continuumMatrixSpectralBlockHankel_add_measure_posDef_of_leftSeparation`
- `det_continuumMatrixSpectralBlockHankel_pos_of_jointSeparation`
- `continuumMatrixSpectralChannelMoment`
- `momentHankelMatrix_continuumMatrixSpectralChannelMoment_eq_submatrix`
- `det_momentHankelMatrix_continuumMatrixSpectralChannelMoment_pos_of_jointSeparation`
- `det_momentHankelMatrix_continuumMatrixSpectralChannelMoment_add_measure_pos_of_leftSeparation`

## RH impact and boundary

The existing Euclidean spectral RH bridge reduces RH to a positive spectral representation of
the normalized prime--Gamma moment sequence.  The new scalar extraction law permits a stronger
producer format: it is enough to realize that sequence as one channel of a jointly separating
positive continuum spectral system.  Other physical channels may then help establish strictness
instead of being discarded before scalarization.

The missing step remains source identification.  No known Higgs, gravitational, holographic, or
quantum-field spectral measure has been proved to reproduce the normalized prime--Gamma moments.
Therefore this enlarges the admissible producer class and strengthens the Lean corpus, but does
not prove RH.

## Verification

- [x] exact module target built and cached
- [x] touched Lean file checks directly after scalar extraction was added
- [x] no full or concurrent build used
- [x] no numerical computation used
