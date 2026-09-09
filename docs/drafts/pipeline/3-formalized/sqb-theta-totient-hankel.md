# Full theta totient-Hankel transform and mean-pole cancellation

The actual reflected theta kernel now has a dependency-closed Lean transform,
with absolute convergence of the full denominator sum. At every actual Xi
copy, its transform has an explicit holomorphic continuation through the mean
pole, a zero mean value, and an exact first jet. RH and normalized native
occurrence remain unproved.

## Actual source and full transform

Use `g = SelbergThetaDilationTransform.profile rho`, and

    J(v) = integral conj(g(t)) g(v-t) dt,
    H(v) = sum_{q>=1} totient(q)/q * integral
             J(v-2 log(q)-log(1+x^2))/sqrt(1+x^2) dx.

The module defines every row by its original integral and H by the sum of
those rows. `row_eq_totient_integral` identifies the exponential half-density
weight with the displayed square-root weight.

For Re(s)>1/2, Lean proves

    integral exp(-s v) H(v) dv
      = Lambda(2s)/Lambda(2s+1) * hat J(-is).               (1)

The Lean parameter is `P : D4BMEisensteinAbsoluteConvergenceParameter`, with
`s=P.s-1/2`. Its `Re(P.s)>1` field specifies the domain of absolute convergence;
no occurrence or zero-location premise is used.

## Absolute analytical mechanism

Write `a_q(x)=2 log(q)+log(1+x^2)`. Multiplication by `exp(-s v)` transforms
a row into

    totient(q) q^(-2P.s) * integral
      (1+x^2)^(-P.s) [exp(-s (v-a_q(x))) J(v-a_q(x))] dx.

All complex exponential twists of J are already integrable. Translation
invariance gives the exact inner integral and its absolute norm bound.
Fubini therefore applies to each full row. The arithmetic coefficient is
exactly the zero Ramanujan coefficient. Its Dirichlet series is absolutely
summable, so the integrated row norms are summable and the infinite sum can
be exchanged with the integral. The existing completed Cauchy zero-Fourier
identity then evaluates the archimedean and arithmetic factors together.

## Positive cancellation at an actual Xi source

For an actual Xi copy rho, set

    d_s = 2-exp((s-1/2)log(2)),
    B_rho(s) = d_s dslope(xi,rho)(rho+1-2s).

`dslope` is the derivative-filled divided difference. It is entire. Since
xi(rho)=xi(conj(rho))=0, each factor of the reflected source satisfies

    d_s xi(rho+1-2s) = (1-2s) B_rho(s).

Thus the full transform has the continuation

    C_rho(s) = (2s-1)(2s+1) xi(2s)/xi(2s+1)
                 * B_conj(rho)(s) B_rho(s).                (2)

Its denominator is nonzero on Re(s)>0 by the proved Euler-side nonvanishing
of Xi. Lean proves holomorphy there, equality with (1) on Re(s)>1/2, and

    C_rho(1/2) = 0,
    C_rho'(1/2) = 2 |xi'(rho)|^2 / xi(2).                 (3)

These statements allow multiple zeros. Continuity of (2), together with its
proved equality to the actual full integrals on the convergence side, gives

    limit_{sigma down to 1/2} integral exp(-sigma v) H(v) dv = 0.

This is an Abel limit of the original full kernel.

## Lean surface and audit

Module: `formal/GaloisForLFunctions/RHTower/SelbergThetaTotientHankel.lean`.
It is wired once into `GaloisForLFunctions/RHTower.lean`.

The public declarations are `row`, `row_eq_totient_integral`, `kernel`,
`row_integrable`, `row_norm_summable`, `kernel_integrable`,
`transform_kernel_completed`, `transform_kernel`, `continuation`,
`continuation_mean`, `continuation_analytic`,
`transform_kernel_eq_continuation`, `hasDerivAt_continuation_mean`, and
`kernel_mean_abel_limit`.

Verification completed:

- `lake env lean /tmp/sqb34_kernel.lean`: pass, no warnings.
- `lake env lean GaloisForLFunctions/RHTower/SelbergThetaTotientHankel.lean`:
  pass, no warnings.
- Named preflight found only the new leaf stale. `lake --old build
  GaloisForLFunctions.RHTower.SelbergThetaTotientHankel` passed; only that
  module was rebuilt (32 seconds). No full or umbrella build was run.
- `/tmp/sqb34_axioms.lean`: all 14 public declarations audited. Every
  dependency list contains only `propext`, `Classical.choice`, `Quot.sound`.
- Corpus index refreshed; scoped whitespace and read-only frontier checks pass.
- Repository lint ran and found one separate, concurrently added module
  unreachable from its umbrella:
  `GaloisForLFunctions.HTGeometry.GomesDilatonDensityShape`. The new SQB
  module has no reported lint error and is wired exactly once. The separate
  integration issue was left to its ongoing work; global lint is not recorded
  as passing.

Audit logs: `/tmp/sqb34_source_check.log`, `/tmp/sqb34_build_preflight.log`,
`/tmp/sqb34_leaf_build.log`, `/tmp/sqb34_axioms.log`, `/tmp/sqb34_index.log`,
and `/tmp/sqb34_lint.log`. All owned Lean/Lake processes exited.

## Remaining mathematical obstacle

The exact full modular Gram identity, its real-frequency boundary integral,
and the resulting normalized native residual estimate still require proof.
Holomorphic continuation of (1) does not assert convergence of the original
integral outside its proved half-plane. The continuation and mean Abel limit
supply the actual arithmetic cancellation for that next analytical step.
The frontier map was kept read-only. No numerical computation was used.
