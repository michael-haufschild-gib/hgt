# Route P: minimal wild-saddle depth for trace-class Xi relocation

Status: `[BRIDGE]` `[FORMALIZED]` `[NOVELTY-AUDITED]`

## Public statement

For the Lambert-W saddle underlying smooth Riemann--von Mangoldt inversion, one logarithmic
stationary-phase correction is Hilbert--Schmidt-grade but cannot relocate the reciprocal Xi
spectrum modulo trace class; two corrections do. Thus depth two is the sharp determinant-grade
wild asymptotic truncation.

## Exact theorem

Let

\[
  N_n=n+\tfrac18,\qquad L_n=\log(N_n/e),\qquad
  u_n+\log u_n=L_n,
\]

where `u_n = log(routeKRVMQuantile n / routeKRVMBase)`. Put

\[
  u_{1,n}=L_n-\log L_n,\qquad
  u_{2,n}=L_n-\log u_{1,n},
\]

and use `u_{j,n}/(2 pi N_n)` as reciprocal spectral coordinates, with the existing finite-head
regularization `max (exp 3) N_n`.

Then, unconditionally:

1. `sum_n |u_{1,n}/(2 pi N_n) - routeKRVMQuantile(n)^(-1)|` diverges;
2. the signed one-step source minus the signed RVM operator is not Schatten-1;
3. the actual reciprocal-Xi operator minus the signed one-step source is not Schatten-1;
4. the signed one-step source is Schatten-2;
5. the existing two-step source differs from both signed RVM and actual reciprocal Xi by
   Schatten-1 operators.

No premise, RH assumption, zero-free hypothesis, or target-fed datum enters the one-step or
two-step source.

## Dependency-closed paper proof

For `L >= 2`, let `u > 0` solve `u + log u = L` and set `u1 = L - log L`.
Existing fixed-point bounds give `L/2 <= u1 <= u <= L`. Moreover `u >= 4/3`: otherwise
`log u <= u - 1` gives `L = u + log u <= 5/3`, contradicting `L >= 2`. Hence

\[
  \log u \ge 1-u^{-1}\ge \tfrac14.
\]

Since `L-u=log u`, the reflected logarithm inequality gives

\[
\begin{aligned}
  u-u_1
    &= \log L-\log u
     = \log(L/u) \\
    &\ge 1-u/L
     = (L-u)/L
     = \log u/L
     \ge 1/(4L).
\end{aligned}
\]

Thus the one-step reciprocal defect is at least `1/(8 pi N L)`, hence at least
`1/(32 N L)` because `pi < 4`.

The prime number theorem in ordered-prime form gives eventually
`p_n >= (n log n)/2`. For `n >= 2`, `N <= 2n` and
`L = log N - 1 <= 2 log n`, so `N L <= 4 n log n <= 8 p_n`. Therefore eventually

\[
  \left|\frac{u_1}{2\pi N}-\frac{u}{2\pi N}\right|
  \ge \frac1{256p_n}.
\]

Euler divergence of `sum 1/p_n` proves item 1 by comparison. Transport through the canonical
prime enumeration proves the same statement on prime labels. If the signed one-step/RVM
difference were Schatten-1, its diagonal in the signed prime coordinate basis would be absolutely
summable, contradicting item 1; this proves item 2. Existing Xi--RVM Schatten-1 relocation and
closure of Schatten-1 under subtraction turn a hypothetical Xi--one-step Schatten-1 difference
into an RVM--one-step Schatten-1 difference, proving item 3.

For item 4, the one-step phase lies pointwise between zero and the two-step phase. The two-step
operator is Schatten-2 because it is the sum of the signed RVM Schatten-2 operator and its
Schatten-1 correction. The diagonal Hilbert--Schmidt criterion and pointwise comparison then put
the one-step source in Schatten-2. Item 5 is the previously proved two-step relocation theorem.

Finite-head regularization changes no convergence or Schatten conclusion.

## Hostile audit

- Sign checked: `u1 <= u`, so absolute one-step defect is `u-u1` divided by the positive
  denominator.
- Boundary checked: lower bound is prime harmonic, so one step fails exactly at Schatten-1;
  pointwise domination by the two-step Hilbert--Schmidt source keeps it in Schatten-2.
- Finite-head plateau checked: all divergence arguments are eventual.
- No determinant equality inferred from trace-class proximity. Relative det2 still carries the
  multiplicative anomaly/cross-trace obligation.
- No claim of RH, spectral equality, or source determination of the trace-class correction.

## Corpus and literature audit

Corpus search found the two-step sufficiency theorem, Euler prime-harmonic divergence, ordered-prime
PNT asymptotics, diagonal Schatten criteria, and trace-class closure, but no one-step lower bound or
minimal-depth theorem.

Primary-source audit:

- Corless--Gonnet--Hare--Jeffrey--Knuth develops Lambert W and its logarithmic asymptotic
  expansion, but not this trace-ideal threshold.
- Franca--LeClair uses Lambert W to invert the smooth Riemann--von Mangoldt equation, but does not
  classify fixed logarithmic truncations by Schatten ideals.
- Bertola identifies Riemann--Hilbert tau functions with Fredholm determinants and exposes
  determinant transition factors, but does not give this Riemann-zero saddle threshold.
- Hartmann--Lesch relate regularized Fredholm and zeta determinants for self-adjoint operators, but
  do not address this truncation problem.

No matching theorem was found in the audited primary literature. Novelty claim is restricted to
the sharp one-step/two-step trace-ideal classification above.

## RH value and remaining obligation

This result fixes the minimum irregular stationary-phase information needed before an ordinary
relative Fredholm determinant can even be posed: first wild correction is insufficient; second is
sufficient. It removes truncation depth as an ambiguity. Remaining RH-bearing problem is source-side
identification of the trace-class correction, equivalently control of the relative determinant's
multiplicative anomaly and higher trace coordinates.

## Lean realization

`formal/GaloisForLFunctions/RHTower/RoutePWildSaddleMinimalTraceClassDepth.lean`

Direct `lake env lean` verification passed. Axiom audit of every new theorem reports only
`propext`, `Classical.choice`, and `Quot.sound`. Module is wired into the RHTower umbrella; umbrella
build was intentionally not run.
