# Mass-shifted Hermite derivative energy

- **ID:** `mass-shifted-hermite-derivative-energy`
- **Stage:** 3-formalized
- **Route:** U, mass-shifted reciprocal-Hankel propagation
- **Scientific status:** `[LEAN FORMALIZED] [UNCONDITIONAL] [SHARP] [NOVELTY UNVERIFIED]`
- **Paper source:** `mass-xi-finite-true-prime-cone`, C43-Y; `mass-shifted-parabolic-degree-horizon`, PDH.9
- **Lean module:** `GaloisForLFunctions.HTGeometry.HermitePolynomialDerivativeEnergy`

## Result

For every real polynomial `P`, Lean proves without analytic or RH premises

\[
 \left\|(P')e^{-\pi x^2}\right\|_2^2
 \le 4\pi\,\deg(P)\left\|Pe^{-\pi x^2}\right\|_2^2.
\]

Here zero polynomial is handled by `natDegree`; statement is closed for all `P`. Bound is sharp:
every self-dual Hermite polynomial `hermitePoly n` attains equality with constant `4*pi*n`.

This is exact coefficient-uniform oscillator estimate used in C43-Y's imaginary-translation
argument. It controls derivative generator on degree-truncated Gaussian polynomial space and is
load-bearing for prime Fourier aperture (PDH.9); it is not a computational certificate or an
abstract positivity assumption.

## Conjecture loop

**Conjecture.** Derivative norm on degree-`d` Gaussian polynomial space is governed exactly by top
Hermite number `4*pi*d`, uniformly over coefficients.

**Hostile tests.** Monomial coefficient estimates lose exponentially in degree. Unrestricted
Hermite completeness loses degree horizon. Existing angular Laguerre/Cayley modules concern a
different measure and cannot prove C43-Y. Required proof must keep finite Hermite span and identify
ordinary polynomial differentiation after Gaussian cancellation.

**Proof.** Triangular Hermite leading coefficients place `P` in first `d+1` Hermite modes. Number
operator is diagonal there with eigenvalues `4*pi*j`, so finite Pythagoras bounds its norm by
`4*pi*d`. Annihilation identity

\[
 (2\pi x+\partial_x)(P(x)e^{-\pi x^2})=P'(x)e^{-\pi x^2}
\]

then converts oscillator estimate to derivative energy. Existing creation/annihilation adjointness
proves exact equality for each Hermite mode.

## Formal capstones

- `mem_span_hermitePoly_fin_of_degree_lt`
- `polyGaussSchwartz_mem_hermite_span`
- `numberCLM_polyGauss_norm_le`
- `annihilationCLM_polyGaussSchwartz`
- `gaussianPolynomialDerivativeEnergy_le`
- `gaussianHermitePolynomialDerivativeEnergy_eq`

## Exact limit

This closes generator bound inside C43-Y, not full imaginary-translation exponential, Mehler
projector concentration, completed Xi explicit formula, prime-shell summation, or Gamma-tail
comparison. Route U parabolic horizon remains unformalized until those literal steps close.

## Literature audit

Krasikov gives explicit real-axis bounds for individual Hermite polynomials; Jeong--Lee--Ryu study
Hermite spectral projection estimates. Neither source states corpus's completed-Xi parabolic
horizon or its coefficient-uniform prime-aperture use. No priority claim is made without specialist
audit.

## Verification

- direct `lake env lean GaloisForLFunctions/HTGeometry/HermitePolynomialDerivativeEnergy.lean`
- forbidden-declaration scan: no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe`
- `#print axioms` for seven public capstones: only `propext`, `Classical.choice`, `Quot.sound`
- targeted `lake build GaloisForLFunctions.HTGeometry.HermitePolynomialDerivativeEnergy`:
  `Build completed successfully (3139 jobs).`
- imported by `GaloisForLFunctions.HTGeometry`
- full umbrella build is presently blocked by unrelated dirty
  `WeightedDiagonalMomentEdgeDetection.lean:197` signature mismatch; new module itself builds.
