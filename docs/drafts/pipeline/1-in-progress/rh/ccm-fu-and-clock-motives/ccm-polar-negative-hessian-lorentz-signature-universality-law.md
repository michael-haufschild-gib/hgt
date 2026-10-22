# CCM polar negative-Hessian Lorentz-signature universality law

- **ID:** `ccm-polar-negative-hessian-lorentz-signature-universality-law`
- **Law:** LAW520
- **Stage:** 1-in-progress
- **Type:** THEOREM (dependency-closed paper proof)
- **Register:** `[UNIVERSAL-LAW] [CORPUS-SYNTHESIS]`
- **Target:** `formal/GaloisForLFunctions/RHTower/CCM/CCMPolarNegativeHessianLorentzSignatureUniversalityLaw.lean`

## Theorem

For every finite sample of logarithmic locations `x_i` and complex amplitudes `v_i`, the real
quadratic energy of the sampled negative Hessian of the local CCM polar potential is exactly

```text
2 |Σ cosh(x_i/2) v_i|² - 2 |Σ sinh(x_i/2) v_i|².
```

Thus the negative Hessian has a universal two-channel Lorentz factorization: one positive cosh
channel and one negative sinh channel, independently of sample size.

## Theorem-generated derivation

Module-pair clustering exposed:

- `neg_ccmPolarPotential_secondDerivative_eq_polarKernel`;
- `polarQuadraticForm_eq_rankTwo`;
- `polarEnergy_eq_signature`.

The first theorem identifies source curvature pointwise with the polar kernel.  The latter two
classify every finite polar quadratic form.  Corpus does not state the resulting finite sampled
Hessian law.

## Dependency-closed paper proof

Replace every sampled coefficient
`-(-2 cosh((x_i-x_j)/2))` by `polarKernel(x_i,x_j)` using the source-sign theorem.  The resulting
complex quadratic form is definitionally `polarQuadraticForm`.  Taking real parts gives
`polarEnergy`; its existing signature theorem produces the displayed difference of two squared
feature norms.  No numerical computation is used.

## Strict corpus delta

Existing source calculus proves only pointwise curvature sign, while the Mellin-defect module
classifies an abstract kernel energy.  LAW520 identifies the actual CCM source negative Hessian
with that rank-two Lorentz energy for arbitrary finite samples.

## Gates

- [x] Whole-corpus theorem-leaf discovery
- [x] Prior corpus and failed-route audit
- [x] Dependency-closed paper proof
- [x] Lean formalization; direct `lake env lean`
- [x] Post-proof literature audit
- [ ] Axiom and umbrella audit

## Lean result

`formal/GaloisForLFunctions/RHTower/CCM/CCMPolarNegativeHessianLorentzSignatureUniversalityLaw.lean`
defines the sampled quadratic form and energy and proves:

- `ccmPolarNegativeHessianQuadraticForm_eq_polarQuadraticForm`;
- `ccmPolarNegativeHessianEnergy_eq_lorentzSignature`.

Direct exact check passed without warnings:

`lake env lean GaloisForLFunctions/RHTower/CCM/CCMPolarNegativeHessianLorentzSignatureUniversalityLaw.lean`

The module is imported by `GaloisForLFunctions/RHTower.lean`.

## Post-proof novelty audit

Performed only after dependency-closed Lean proof passed.  Searches found generic Hessian-signature
criteria, unrelated effective polar potentials, polar Mellin transforms, and standard Lorentz
hyperbolic coordinates.  No source identified the local CCM polar source negative Hessian with
this sample-size-independent cosh/sinh rank-two quadratic energy.

Relevant comparisons:

- https://arxiv.org/abs/1505.01382
- https://arxiv.org/abs/1001.3693
- https://arxiv.org/abs/1307.8019

Verdict: `[NOVELTY PLAUSIBLE — SEARCH NOT EXHAUSTIVE]`.  Novelty is claimed for the exact CCM
negative-Hessian/polar-energy identification, not for the elementary hyperbolic subtraction
identity or generic Hessian inertia.

## Log

- 2026-07-26 — LAW520 generated from CCM polar source curvature and polar rank-two energy.
- 2026-07-26 — direct Lean check passed; wired into RHTower umbrella; post-proof audit plausible.
