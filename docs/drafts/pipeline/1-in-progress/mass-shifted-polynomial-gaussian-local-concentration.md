# Mass-shifted polynomial--Gaussian local concentration

- **ID:** `mass-shifted-polynomial-gaussian-local-concentration`
- **Stage:** 1-in-progress
- **Route:** U, C43-Y `(24.135)`
- **Scientific status:** `[BRIDGE] [PAPER-PROVED] [LEAN-IN-PROGRESS] [UNCONDITIONAL]`
- **Depends on:** `mass-shifted-hermite-derivative-energy`; `RHTower.LargeValues`;
  `mass-shifted-polynomial-gaussian-fourier-aperture`

## Exact frozen theorem PGLC.1

For every real polynomial `Q`, every `t>0`, and every `R>=0`, with the native Route-U density and
mass from `PolynomialGaussianFourierAperture.lean`, prove

\[
 \int_{[-R,R]}\!\|Q(x^2)^2e^{-t x^2}\|\,dx
 \le 18R\sqrt{t(\deg Q+1)}\,M_Q(t).
 \tag{PGLC.1}
\]

No nonzero-polynomial, coefficient, parity, RH, or analytic premise may be added.

## Paper proof

Let `f=P exp(-pi*x^2)` with `n=deg P`. Oscillator identities give

\[
 \|f'\|_2^2\le 16(n+1)\|f\|_2^2.
\]

Indeed `2f'=Bf-Af`; the already-formal number-operator bound gives
`||Bf||^2 <= 4 pi n ||f||^2` and `||Af||^2 <= 4 pi(n+1)||f||^2`. Triangle and
`pi<4` yield the displayed estimate. Apply the already-formal one-dimensional Gallagher--Sobolev
bound on `[x,x+1]` with `eta=1/(4 sqrt(n+1))`; local squared masses are bounded by global ones.
This gives

\[
 |f(x)|^2\le 9\sqrt{n+1}\|f\|_2^2.
\]

Integrating over `[-R,R]` gives factor `18R`. For the native density take
`P=routeURescaledEvenPolynomial Q t`, whose degree is `2 deg Q`, and use the exact native mass
scaling. Squaring reduces the remaining scale comparison to
`2 deg Q+1 <= 2 pi(deg Q+1)`.

## Hostile and novelty audit

- Constants cover degree zero and zero polynomial; no division by mass occurs.
- The proof does not use numerical computation or a Mehler expansion.
- Gaussian weighted Bernstein--Markov and Hermite/Nikolskii inequalities are classical-adjacent;
  no standalone novelty is claimed. Li--Geng--Ling--Wang, arXiv:2411.16359, confirms exact
  Gaussian `L2` derivative factors. New Route-U information is structural: Mehler is not a
  load-bearing dependency for `(24.135)`; existing finite oscillator energy plus one-dimensional
  Sobolev evaluation closes it with an explicit native constant.

