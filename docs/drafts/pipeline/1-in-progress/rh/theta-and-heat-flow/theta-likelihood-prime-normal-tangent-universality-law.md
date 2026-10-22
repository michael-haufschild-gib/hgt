# Theta-likelihood prime normal-tangent universality law

- **ID:** `theta-likelihood-prime-normal-tangent-universality-law`
- **Law:** LAW509
- **Stage:** 1-in-progress
- **Type:** THEOREM (dependency-closed paper proof)
- **Register:** `[UNIVERSAL-LAW] [CORPUS-SYNTHESIS]`
- **Target:** `formal/GaloisForLFunctions/RHTower/ThetaLikelihoodPrimeNormalTangentUniversalityLaw.lean`

## Theorem

For every prime shell, every nonzero point on the paired normal-crossing face gives exactly the
same normalized phase and spectral derivative as the one-sided tangent of the nonlinear scaled
likelihood shell at the zero-likelihood boundary.  This common normal tangent has strictly
negative Hermitian current throughout the upper half-plane.

The normal direction therefore has no projective modulus on prime shells: all nonzero secants,
the nonlinear boundary tangent, and their spectral derivatives collapse to one oriented prime
conormal.

## Theorem-generated derivation

Whole-corpus leaf comparison exposed two modules with a common target but no connector:

- `thetaCuspLikelihoodTwoFaceMassShellPhase_div_eq_primeConormal`;
- `thetaCuspLikelihoodTwoFaceMassShellPhaseDerivative_div_eq_primeConormal`;
- `tendsto_thetaCuspLikelihoodScaledPrimeMassShellPhase_div_nhdsGT_zero`;
- `tendsto_thetaCuspLikelihoodScaledPrimeMassShellPhaseDerivative_div_nhdsGT_zero`;
- `thetaCuspLikelihoodPrimeFirstBoundaryLayer_current_lt_zero`.

The normal-crossing module identifies each fixed nonzero face quotient with the ray-weighted
prime conormal.  The boundary-residue module identifies the nonlinear one-sided tangent with the
same conormal and proves its orientation.  Neither states the fixed-face/tangent equality or its
simultaneous phase/derivative/orientation form.

## Dependency-closed paper proof

Fix prime `k`, nonzero face coordinate `B₀`, and spectral point `z`.  Normal-crossing rigidity
gives

```text
B₀⁻¹ F_face(B₀,z)  = R_k F_k(z),
B₀⁻¹ ∂zF_face(B₀,z) = R_k ∂zF_k(z).
```

The first-boundary-layer theorems independently give, as `B → 0+`,

```text
B⁻¹ F_scaled(B,z)  → R_k F_k(z),
B⁻¹ ∂zF_scaled(B,z) → R_k ∂zF_k(z).
```

Substitution identifies both limits with the normalized face at arbitrary `B₀`.  The ray weight
`R_k` is positive; the existing first-boundary-layer current theorem then gives strict negative
Hermitian current for the common phase/derivative pair whenever `Im z > 0`.  No numerical
computation is used.

## Strict corpus delta

Existing files give a fixed normal-crossing section and an infinitesimal nonlinear boundary
section separately.  New law proves all nonzero normal sections equal the unique nonlinear
one-sided tangent, simultaneously at value and spectral-derivative level, and carries the strict
orientation through this identification.

## Lean result

`formal/GaloisForLFunctions/RHTower/ThetaLikelihoodPrimeNormalTangentUniversalityLaw.lean`
proves:

- `thetaCuspLikelihood_primeNormalTangentUniversality`.

Direct exact check passed without warnings:

`lake env lean GaloisForLFunctions/RHTower/ThetaLikelihoodPrimeNormalTangentUniversalityLaw.lean`

The module is imported by `GaloisForLFunctions/RHTower.lean`.

## Post-proof novelty audit

Performed only after dependency-closed Lean proof passed.  Targeted searches found standard
theta-function boundary methods, likelihood tangent-cone asymptotics, spectral-boundary residues,
and normal-crossing terminology.  They did not recover this theta-cusp likelihood shell, its
prime factor-pair conormal, an equality of every nonzero normal section with the nonlinear
one-sided tangent at both value and spectral-derivative level, or the inherited strict Hermitian
orientation.

Verdict: `[NOVELTY PLAUSIBLE — SEARCH NOT EXHAUSTIVE]`.  Novelty is claimed for the exact
prime-shell normal-tangent/orientation identity, not for generic differentiability at a boundary.

## Gates

- [x] Whole-corpus theorem-leaf discovery
- [x] Prior corpus and failed-route audit
- [x] Dependency-closed paper proof
- [x] Lean formalization; direct `lake env lean`
- [x] Post-proof literature audit
- [ ] Axiom and umbrella audit
