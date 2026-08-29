# Compact Weil deep-window discrimination experiment

## Status

Stage 1 computational experiment. Numerical evidence only; no computed value may be used as a
Lean premise or as a paper proof.

## Exact question

For the even compact-window Weil floor

\[
\lambda^*(L)=\inf_{0\ne f\in L^2(-L,L),\ f\ \mathrm{even}}
  \frac{Q(f)}{\lVert f\rVert_2^2},
\]

can explicit finite sine/cosine trials beyond the published range `L <= 2` discriminate between
the proposed Landau--Widom law

\[
-\log\lambda^*(L)\sim 2\pi^2\frac{N(2\pi e^{2L})}{\log N(2\pi e^{2L})}
\]

and the numerically entangled alternative proportional to `4*pi*exp(2L)`?

## Trial family

Use the orthonormal even Dirichlet modes

\[
\phi_j(x)=L^{-1/2}\cos((j+\tfrac12)\pi x/L),\qquad 0\le j<n.
\]

Their transforms have common cosine factor and a Cauchy denominator. Coefficients can therefore
be chosen explicitly so that the transform vanishes at the first `n-1` positive zeta ordinates:
the numerator of the resulting rational function is the product over those squared ordinates.
This avoids a dense, catastrophically ill-conditioned high-precision eigensolve.

## Hostile protocol

1. Derive coefficients independently from residues and from a direct linear residual check.
2. Reproduce published values at several `L <= 2` before accepting any new point.
3. Check normalization, annihilation residuals, tail convergence, precision doubling, and nearby
   mode counts.
4. Evaluate both the zeros-side exploratory quotient and, where cancellation cost is feasible,
   the geometric prime--Gamma formula as an independent check.
5. Treat disagreement, lack of stabilization, or dependence on truncation as a killed experiment,
   not evidence about RH.

## Possible outcomes

- Stable new points favor one scaling and sharpen the compact-Weil/Route O spectral picture.
- Persistent drift or a third scaling kills both simple extrapolations and opens a revised model.
- Numerical conditioning or tail instability blocks meaningful discrimination; this records a
  computational barrier and does not count as RH evidence.

## Lean consequence policy

Only exact algebraic identities exposed by the experiment may be formalized. Numerical values,
zero tables, fitted constants, and observed signs remain outside Lean proofs.
