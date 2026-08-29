# Compact Weil deep-window discrimination experiment

## Status

Structural experiment complete; deep-window asymptotic discrimination remains open. Numerical
evidence only; no computed value may be used as a Lean premise or as a paper proof. Full report:
`../2-fully-proven/computations/2026-08-29-compact-weil-ground-lock/REPORT.md`.

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

A second, more structural question is whether the Fourier transforms of the actual finite-window
ground vectors develop real zeros locked to the low Riemann-zero ordinates as `L` grows. This is
the unverified spectral mechanism needed by the Connes--Consani--Moscovici program after fixed
window simplicity: small energy alone does not imply zero-by-zero locking.

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
6. For ground-zero locking, separate genuine numerator zeros from the removable Dirichlet-basis
   poles/common cosine factor; report missing roots and gap-normalized offsets, not visual plots.

## Possible outcomes

- Stable new points favor one scaling and sharpen the compact-Weil/Route O spectral picture.
- Persistent drift or a third scaling kills both simple extrapolations and opens a revised model.
- Numerical conditioning or tail instability blocks meaningful discrimination; this records a
  computational barrier and does not count as RH evidence.

## Lean consequence policy

Only exact algebraic identities exposed by the experiment may be formalized. Numerical values,
zero tables, fitted constants, and observed signs remain outside Lean proofs.

## Outcome

Ground transforms lock every tested ordinate below saturation height through `L=1.8`, but a hostile
close-pair deformation exposes cubic conditioning and eventual two-root-to-one-root collapse while
the scalar floor barely moves. This kills the inference from tiny ground energy to
multiplicity-exact cofinal locking. The unconditional survivor—the exact average/difference split
and quadratic loss of the difference channel—was formalized in
`CompactWeilClosePairSamplingCollision.lean`. Route continuation should test a derivative/Hermite
sampling head, not add more scalar floor digits.
