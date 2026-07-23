# Prime--archimedean universal strict-Hankel-ray adjoining law

## Status

In progress — paper proof and parent source exact-check complete; full Lean source check deferred
until final dependency build; literature novelty audit pending.

## Theorem-first provenance

- `RHTower/PrimeArchBlackHoleReciprocalSpectralConeUniversalityLaw.lean`
  - `primeArchBlackHoleReciprocalMixedClock_hankel_posDef_of_riemannHypothesis`
  - `riemannHypothesis_iff_primeArchBlackHoleReciprocal_spectralCone_posDef`
- `HTGeometry/DiscreteMomentHankel.lean`
  - `discreteMomentHankel_posDef`
- `HTGeometry/GeometricKallenLehmannResponse.lean`
  - `geometricKallenLehmannMoment_eq_tsum`
  - `geometricKallenLehmann_infiniteSupport`

## Universal law

Any moment ray whose Hankel matrix is positive definite at every finite depth can be adjoined to
the black-hole/reciprocal-continuum/prime--archimedean cone without changing its exact RH
classifier.  RH is equivalent to positive definiteness of every nonzero nonnegative four-ray
mixture.  The theorem quantifies over the adjoined strict ray, so it subsumes repeated one-off cone
extensions.

As a concrete cross-folder specialization, the self-similar geometric Källén--Lehmann response is
such a ray for every `0<a,b<1`.

## Paper proof

Hankel formation is linear.  Under RH the original three-ray mixture is positive definite whenever
one of its coefficients is positive.  Adding a nonnegative multiple of the fourth positive
semidefinite matrix preserves positive definiteness.  If the first three coefficients vanish, the
fourth coefficient is positive and its strictness supplies the result.  Conversely, set the fourth
coefficient to zero and recover the existing exact three-ray RH criterion.  The geometric
Källén--Lehmann specialization follows from its positive weights, summable moments, and nodes
escaping every finite set.

## Lean status

Source complete in
`formal/GaloisForLFunctions/RHTower/PrimeArchUniversalStrictHankelRayAdjoiningUniversalityLaw.lean`.

The imported three-ray parent source exact-check passed with
`lake env lean GaloisForLFunctions/RHTower/PrimeArchBlackHoleReciprocalSpectralConeUniversalityLaw.lean`.
Full child check is deferred because that parent currently has no cached `.olean`; no dependency
build was run before final audit.

## Novelty status

Pending post-discovery literature audit. Discovery used Lean statements only. Corpus search found
several concrete strict spectral rays and one fixed three-ray cone, but no theorem stated the
universal closure of the RH cone under adjoining an arbitrary all-depth strict Hankel ray.
