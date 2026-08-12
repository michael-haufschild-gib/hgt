# Mass-shifted polynomial--Gaussian local concentration

- **ID:** `mass-shifted-polynomial-gaussian-local-concentration`
- **Stage:** 3-formalized
- **Route:** U, C43-Y `(24.135)`
- **Scientific status:** `[BRIDGE] [PAPER-PROVED] [LEAN-PROVED] [UNCONDITIONAL]`
- **Depends on:** `mass-shifted-hermite-derivative-energy`; `RHTower.LargeValues`;
  `mass-shifted-polynomial-gaussian-fourier-aperture`
- **Lean module:** `GaloisForLFunctions.RHTower.PolynomialGaussianLocalConcentration`

## Exact theorem PGLC.1

For every real polynomial `Q`, every positive heat time `t`, and every `R >= 0`, the native
Route-U density and mass satisfy

\[
 \int_{[-R,R]}\!\|Q(x^2)^2e^{-t x^2}\|\,dx
 \le 18R\sqrt{t(\deg Q+1)}\,M_Q(t).
 \tag{PGLC.1}
\]

No nonzero-polynomial, coefficient, parity, RH, or analytic premise is present.

## Proof and structural survivor

Let `f=P exp(-pi*x^2)` with `n=deg P`. Oscillator identities and the formal number-operator bound
give

\[
 \|f'\|_2^2\le 16(n+1)\|f\|_2^2.
\]

Indeed `2f'=Bf-Af`, with `||Bf||^2 <= 4 pi n ||f||^2` and
`||Af||^2 <= 4 pi(n+1)||f||^2`. Apply the one-dimensional Gallagher--Sobolev estimate on
`[x,x+1]` at `eta=1/(4 sqrt(n+1))`, bounding local squared masses by global ones. This yields

\[
 |f(x)|^2\le 9\sqrt{n+1}\|f\|_2^2.
\]

Integration over `[-R,R]` supplies `18R`. Native scaling uses
`P=routeURescaledEvenPolynomial Q t`, `deg P=2 deg Q`, and the exact mass dilation. The final
comparison squares to `2 deg Q+1 <= 2 pi(deg Q+1)`.

Strongest structural survivor: C43-Y `(24.135)` does not need a finite Mehler-projector
development. Existing finite oscillator energy plus one-dimensional Sobolev point evaluation
already gives the coefficient-uniform square-root degree law with an explicit native constant.

## Lean theorem inventory

- `RHTower.norm_deriv_polyGaussSchwartz_sq_le`
- `RHTower.norm_polyGaussSchwartz_sq_le`
- `RHTower.integral_Icc_norm_polynomialGaussianEnergy_le`
- `RHTower.integral_Icc_norm_routeUPolynomialGaussianDensity_le` — exact PGLC.1

## Hostile and novelty audit

- Degree zero and zero polynomial are covered; proof never divides by mass.
- No numerical computation or Mehler expansion is used.
- Gaussian weighted Bernstein--Markov and Hermite/Nikolskii inequalities are classical-adjacent;
  no standalone novelty is claimed. Li--Geng--Ling--Wang, arXiv:2411.16359, confirms exact
  Gaussian `L2` derivative factors. Route-U gain is structural dependency elimination.

## Verification

- Direct: `lake env lean GaloisForLFunctions/RHTower/PolynomialGaussianLocalConcentration.lean`
- Build: `lake build GaloisForLFunctions.RHTower.PolynomialGaussianLocalConcentration`
  (`8827/8827`, success)
- Axiom audit for derivative, pointwise, and native concentration theorems:
  `[propext, Classical.choice, Quot.sound]`
- Target banned-token audit: no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe`
- Umbrella import: `GaloisForLFunctions.RHTower`
- Global lint still reports unrelated pre-existing unreachable modules; this module is wired and is
  below the 700-line threshold.
