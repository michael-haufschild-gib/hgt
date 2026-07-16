# Euclidean spectral pushforward, strict Hankel geometry, and RH capstone

- **ID:** `euclidean-spectral-pushforward-hankel-rh-capstone`
- **Stage:** 3-formalized
- **Type:** THEOREM, `[BRIDGE]`, positive spectral-measure source interface
- **Scientific status:** `[PROVED] [FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lean modules:**
  - `GaloisForLFunctions.HTGeometry.ObservablePushforwardHankelStrict`
  - `GaloisForLFunctions.HTGeometry.EuclideanSpectralHankelStrict`
  - `GaloisForLFunctions.RHTower.PrimeArchEuclideanSpectralRH`

## General observable-pushforward law

Let `mu` be a positive measure on an arbitrary measurable hidden space and let
`node : X -> R` be a measurable reporter.  Define

```text
s_n = integral node(x)^n dmu(x).
```

The pushforward measure `nu = node_* mu` satisfies

```text
s_n = integral y^n dnu(y).                                (1)
```

Integrability of the reported powers transports through the pushforward.  If the reporter retains
positive mass outside every finite palette of reported values, then `nu` has infinite support and

```text
det H_N(s) > 0                                             (2)
```

for every `N`.

This theorem makes the location of strictness explicit: hidden-state multiplicity is irrelevant if
the reporter collapses it to finitely many values; what matters is infinite support after
observation.

## Euclidean spectral specialization

At fixed clock spacing `tau`, report a spectral energy `E` by

```text
z_tau(E) = exp(-tau E),
C_n       = integral exp(-tau E)^n dmu(E).                 (3)
```

For `tau != 0`, `z_tau` is injective.  Infinite support of `mu` therefore survives observation.
Under moment integrability, every sampled-correlator Hankel determinant is positive.  Consequently
`C` has no prescribed finite modal width and is outside every fixed-dimensional local linear
state-space closure.

This is the value skeleton of a Källén--Lehmann or lattice Euclidean correlator.  It applies to
positive spectra in quantum field theory, QCD and the strong force, electromagnetic and weak
current correlators, Higgs and other scalar sectors, thermal response, and continuum relaxation
kernels.  The theorem uses only the observed samples, not a postulated time evolution.

Primary literature motivating the interface:

- M. Bruno, L. Giusti, and M. Saccardi, *Spectral densities from Euclidean lattice correlators via
  the Mellin transform*, arXiv:2407.04141.
- M. Saccardi, M. Bruno, and L. Giusti, *Spectral densities from Euclidean-time lattice correlation
  functions*, arXiv:2501.16527.
- L. Giusti, M. Saccardi, and D. Toniolo, *Spectral densities from Euclidean correlators via
  integral transforms: theoretical framework*, arXiv:2606.28167.

## RH-facing source theorem

Define `PrimeArchEuclideanSpectralRepresentation` by the existence of one positive measure `mu`
and one spacing `tau` such that every normalized prime--Gamma moment equals `(3)` and all reported
powers are integrable.

No support-size and no nonzero-spacing hypothesis is required for RH.  Equations `(1)` and `(3)`
produce the existing arbitrary positive moment representation, so

```text
PrimeArchEuclideanSpectralRepresentation
  -> PrimeArchMomentRepresentation
  -> RH.                                                   (4)
```

The stronger interface `PrimeArchInfiniteEuclideanSpectralRepresentation` adds `tau != 0` and
infinite energy support.  It yields the existing infinite-support moment representation and hence
strict positivity of every leading prime--Gamma Hankel determinant.

The separation is a real hypothesis discharge: infinite support is useful for strictness but is
superfluous for RH, whose non-strict polynomial-square cone already consumes an arbitrary positive
representing measure.

## Positive statement after the no-go

The construction does not merely exclude finite spectra.  It identifies the positive object that
would close the RH source gate: a positive Euclidean spectral measure whose reported moments are
the normalized prime--Gamma tower.  The pushforward is canonical and produces the exact measure
already required by the formal RH criterion.

## Lean surface

General pushforward:

- `observablePushforwardMeasure`
- `integral_pow_observablePushforwardMeasure`
- `integrable_pow_observablePushforwardMeasure`
- `observablePushforwardMeasure_infiniteSupport`
- `det_momentHankelMatrix_pos_of_observable_infiniteSupport`

Euclidean spectral sampling:

- `euclideanSpectralNode`
- `euclideanSpectralNode_measurable`
- `euclideanSpectralNode_injective`
- `euclideanSpectralNode_infiniteSupport`
- `euclideanSpectralMoments`
- `euclideanSpectralMoments_eq_pushforward_moment`
- `det_momentHankelMatrix_euclideanSpectralMoments_pos`
- `euclideanSpectralMoments_not_finiteModalWidthAtMost`
- `euclideanSpectralMoments_not_linearRecurrence`
- `euclideanSpectralMoments_not_fixedStateSpaceDimensionLocalClosure`

Prime--Gamma/RH specialization:

- `PrimeArchEuclideanSpectralRepresentation`
- `PrimeArchInfiniteEuclideanSpectralRepresentation`
- `primeArchEuclideanSpectralRepresentation_of_infinite`
- `primeArchMomentRepresentation_of_euclideanSpectral`
- `primeArchInfiniteSupportMomentRepresentation_of_euclideanSpectral`
- `primeArchSourceMomentHankelDeterminantsPositive_of_euclideanSpectral`
- `riemannHypothesis_of_primeArchEuclideanSpectralRepresentation`

## Exact remaining research task

Construct `mu` and `tau` from the normalized continued prime--Gamma source itself and prove

```text
normalizedPrimeArchMoment n
  = integral exp(-tau E)^n dmu(E)
```

for every `n`, with `mu` positive.  Infinite support is optional for RH.  This is a genuine source
producer if achieved; the present theorem closes the entire consumer chain but does not construct
the source spectral measure.

## Verification

- [x] all three touched modules check directly
- [x] exact dependency artifacts and deepest RHT artifact are cached
- [x] weak RH interface removes the unnecessary infinite-support hypothesis
- [x] no numerical computation used
