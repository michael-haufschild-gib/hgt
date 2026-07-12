# XiC Taylor flux-bound RH gate

- **ID:** `xi-c-taylor-flux-bound-rh-gate`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** RH is equivalent to one uniform eventual upper bound for the imaginary logarithmic
  derivatives of the finite XiC Taylor polynomials at every pole-free Gaussian-rational point of
  the original left half-strip.

## Goal

Push the countable continued prime--Gamma lower-bound criterion backward to canonical finite
polynomial data while discharging the entire finite-to-limit interface.

## Finite objects

Let

\[
P_n(z)=\texttt{xiCTaylorApprox}(n,z)
\]

be the degree-`< n` Cauchy--Taylor polynomial of the entire centered Xi function at zero. Its
coefficients are canonical Taylor data, accessible through the formalized theta/moment corpus.

For an original-coordinate point `s`, put

\[
z(s)=(s-1/2)(-i).
\]

The finite observable is

\[
\operatorname{Im}\frac{P_n'(z(s))}{P_n(z(s))}.
\]

## Theorem

The canonical Taylor approximants and their derivatives converge locally uniformly:

\[
P_n\longrightarrow\Xi_C,
\qquad
P_n'\longrightarrow\Xi_C'.
\]

At every point where `XiC(z) != 0`, quotient convergence gives

\[
\frac{P_n'(z)}{P_n(z)}
\longrightarrow
\frac{\Xi_C'(z)}{\Xi_C(z)}.
\]

Consequently RH is equivalent to the following finite-polynomial statement:

\[
\exists C\in\mathbb R\quad
\forall q\in\mathbb Q(i),
\quad 0<\Re q<\frac12,
\quad \zeta(q)\ne0,
\]

\[
\operatorname{Im}
\frac{P_n'(z(q))}{P_n(z(q))}
\le C
\quad\text{for all sufficiently large }n.
\]

The threshold may depend on `q`; the bound `C` is common to every rational point. Under RH the
choice `C=1` works.

The formal chain is

\[
\text{uniform eventual finite-Taylor flux bound}
\Longrightarrow
\text{Gaussian-rational completed prime--Gamma lower bound}
\Longrightarrow
\mathrm{RH}.
\]

## Positive remaining theorem

Prove one common eventual upper bound for these explicit finite rational functions. No zero
localization of the Taylor polynomials is required beyond what is implicit in `logDeriv`; local
uniform convergence already ensures eventual nonvanishing at every fixed pole-free limit point.

Possible producers include:

- coefficient inequalities from the theta-cusp moment representation;
- a normal-family bound for the logarithmic derivatives of `P_n`;
- a finite Hermite--Biehler or one-sided Hardy estimate for the Taylor polynomials;
- a direct recurrence bound on `P_n'/P_n` at Gaussian-rational arguments.

## Lean certificate

Module:

- `formal/GaloisForLFunctions/RHTower/XiCTaylorFluxBoundGate.lean`

Main declarations:

- `xiCTaylorApprox_deriv_tendstoLocallyUniformly`
- `xiCTaylorApprox_logDeriv_tendsto`
- `XiCTaylorGaussianRatLeftHalfImEventuallyBoundedAbove`
- `completedPrimeGammaGaussianRatLeftHalfBoundedBelow_of_xiCTaylor`
- `riemannHypothesis_of_xiCTaylorGaussianRatLeftHalfImEventuallyBoundedAbove`
- `xiCTaylorGaussianRatLeftHalfImEventuallyBoundedAbove_iff_riemannHypothesis`

Verification:

- `lake build GaloisForLFunctions.RHTower.XiCTaylorFluxBoundGate` passes.
- Axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`.

## Gates

- [x] 0 → 1 in-progress: finite Taylor logarithmic-derivative observable isolated
- [x] 1 → 2 fully-proven: differentiated locally-uniform convergence and quotient transfer proved
- [x] 2 → 3 formalized: exact finite-Taylor criterion proved in Lean
- [ ] 3 → 4 publication-ready: prove the uniform finite-polynomial bound
