# Universal classification of positive Hedenmalm theta forms

- **ID:** `hedenmalm-universal-positive-form-classification`
- **Stage:** 3-formalized
- **Type:** THEOREM / POSITIVE SPECTRAL-MEASURE CLASSIFICATION
- **Scientific status:** `[PROVED] [FORMALIZED] [CLASSICAL REPRESENTATION BRIDGE] [NOT AN RH PROOF]`

## Theorem

Let `Q` be a jointly continuous sesquilinear form on complex Schwartz space. If `Q` is
nonnegative and the momentum operator is symmetric for `Q`, then there is a unique positive Borel
measure `mu` of temperate growth such that

```text
Q(u,v)=integral_R hat(u)(t) conjugate(hat(v)(t)) dmu(t).  (1)
```

The measure is constructed canonically from compact spectral packets. No representation measure
is assumed. An explicit expanding cutoff proves compactly supported Schwartz functions dense in
Schwartz space with `O((n+1)^(-1))` control in every seminorm, so the compact Riesz representation
extends to all Schwartz pairs. Applying the same construction to a pre-existing spectral measure
recovers that measure exactly; hence `(1)` is unique.

For the normalized Hedenmalm theta source `k`, if

```text
Q(k,k)=0,                                                 (2)
```

then the unique measure in `(1)` is supported on the real `Xi` divisor and is purely atomic:

```text
mu=sum_(gamma in R:Xi(gamma)=0) mu({gamma}) delta_gamma. (3)
```

Moreover, `(2)` makes `k` a left-radical vector. Such a form is sequentially closable through
ordinary Lebesgue `L^2` exactly when `mu=0`, equivalently when `Q` vanishes identically. Conversely,
every positive temperate measure supported on the real `Xi` divisor yields a nonnegative
momentum-symmetric theta-null form through `(1)`.

## Source and orientation boundary

The pointed Hedenmalm moment module determines the analytic source and reconstructs its Bezoutian.
The theorem above classifies all positive forms compatible with that source. These are different
statements: the classification assumes nonnegativity and does not prove that the reconstructed
Bezoutian is nonnegative.

The exact remaining implication is

```text
source-determined Hedenmalm Bezoutian
  belongs to the nonnegative orientation chamber.         (4)
```

For the actual theta source, `(4)` is already formalized as equivalent to RH. Thus the analytic
carrier is complete and unique, while its orientation remains open. All moments determine what
must be oriented; they do not determine its sign.

## Formal certificate

Files:

```text
formal/GaloisForLFunctions/HTGeometry/SchwartzCompactPositiveFunctional.lean
formal/GaloisForLFunctions/HTGeometry/SchwartzPositiveMeasureRepresentation.lean
formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmUniversalPositiveFormClassification.lean
```

Principal theorem surface:

```text
ContinuousSchwartzSesquilinearForm.compactSpectralRieszForm_eq
compactSpectralRieszMeasure_spectralMeasureForm
spectralMeasureForm_eq_iff_measure_eq
existsUnique_temperateSpectralRepresentation
universalPositiveForm_thetaNull_iff_canonicalMeasure_support_realDivisor
existsUnique_temperateSpectralRepresentation_supported_realDivisor_of_thetaNull
universalPositiveForm_canonicalMeasure_atomic_of_thetaNull
universalPositiveForm_thetaNull_closable_iff_canonicalMeasure_zero
```

## Scientific boundary

The positive-form representation is the classical Bochner--Schwartz/Riesz--Markov mechanism
proved here in the exact project category. The theta-source specialization may be a useful new
classification of Hedenmalm's 2026 setup, but its novelty has not received a complete literature
audit. It is therefore conservatively classified as a bridge. Honest score: **47/100**. A result
at publication-level RH significance still requires a source-specific proof of `(4)`.

## Gates

- [x] compact spectral locality without a Schwartz kernel theorem
- [x] positive compatible functional on `C_c(R,R)`
- [x] canonical Riesz measure of temperate growth
- [x] all-Schwartz representation
- [x] exact recovery and uniqueness of the representing measure
- [x] theta-null support and atomic classification
- [x] radical and ordinary-`L^2` nonclosability classification
- [x] formalization without `sorry`, `admit`, `axiom`, `opaque`, or `unsafe`
- [ ] source-specific Bezoutian sign theorem
- [ ] RH
