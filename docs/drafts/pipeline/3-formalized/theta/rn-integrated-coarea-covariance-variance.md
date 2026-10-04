# RN-P-7af: exact integrated coarea covariance loss

2026-10-04. Formalized in ThetaGaussianAmplitudeQuadratic,
ThetaGaussianCovarianceMeasure and ThetaGaussianCovarianceLimit.
Parent: ../../1-in-progress/rn-finite-current-integrated-compensation.md.

For the actual center coarea probability measure mu with density
rho(u)/Z=density(0,0,u)/integral density(0,0), put

  A_x(u)=exp(V(0,0,u)-V(0,x,u)),
  B_x(u)=A_x(u)-x*partial_x A_x(u),
  C(x)=Cov_mu(A_x,B_x).

Write u=t^2, q=c(0), and

  a(t)=(c(t)+p(t)/t-2*q)/4, t>0.

The complete half-line covariance satisfies

  C(x)/x^4 -> -Var_mu(a)<0 as x->0+.

Here a is evaluated in the time chart t=sqrt(u). Consequently C(x)<0 for
every sufficiently small positive x. This refutes a favorable integrated
covariance shortcut in the actual diagonal finite-pair regime. It neither
refutes the full coupled RN inequality nor proves or falsifies RH.

## Exact positive survivor

The lost contribution is exactly a strictly positive, finite variance of the
actual quadratic source profile. The mean and second moment are integrable;
the centered square has positive integral. The proof identifies the measure:

  J=coareaMass=H(0,0)=integral_0^infinity 2*t*k(t)^2 dt,
  integral rho(u)*f(u) du
    =(1/k(0)^2)*integral 2*t*k(t)^2*f(t^2) dt,
  Z=J/k(0)^2.

Thus the covariance is the literal original coarea covariance, not a surrogate
measure or a definition chosen to enforce the asymptotic identity.

## Dependency-closed paper proof

At fixed t>0 the endpoint potential derivative vanishes at x=0 and its
node derivative equals 2*a(t). Differentiating A_x and applying the quadratic
limit lemma gives

  D_x(t)=(1-A_x(t^2))/x^2 -> a(t),
  E_x(t)=(B_x(t^2)-1)/x^2 -> a(t).

For 0<x<=1 and every t>0, the actual slope chords give
|D_x(t)|<=c(t+1) and |E_x(t)|<=2*c(t+1). The audited source law c'<2*c
implies c(t)<=c(0)*exp(2*t) on the positive ray. Actual k is positive,
k(t)<=k(0), and has every real exponential moment. Hence
2*t*k(t)^2*(1+c(t+1)^2) is integrable on the whole half-line.
Dominated convergence applies to D_x, E_x and their product.

Exact integral algebra, with integrability discharged, gives

  C(x)/x^4=-E_mu[D_x*E_x]+E_mu[D_x]*E_mu[E_x].

The limit is -E_mu[a^2]+E_mu[a]^2=-Var_mu(a). No derivative of an improper
integral is assumed. The corpus's strict curvature increase makes a strictly
increasing on t>0. If its centered-square integral vanished, continuity and
strict positivity of 2*t*k(t)^2 would make a constant on that open half-line,
a contradiction. This proves the strict positive survivor.

## Validation

All three leaves export successfully. Final sequence3029 exited0: direct
`lake --old env lean` checks of all three actual source files, with the Limit
check also exporting its current olean, followed by all36 public theorem
`#print axioms` queries in /tmp. Every closure is exactly propext,
Classical.choice, Quot.sound. No source errors or warnings remain; informational
ring-normalization suggestions remain. All three imports are wired into
RHTower.lean. No umbrella/full build, numerical experiment, additional axiom,
unproved source premise, heartbeat increase or subagent was used.

Lint22123 exited1 with18 unrelated unreachable modules and no own-leaf or
forbidden-declaration error; exact names are in the working log. Targeted
whitespace validation passed.

The surviving hard problem is the complete coupled score integral, where
potential variation must pay this actual covariance loss. Global finite-pair
compensation, general anchors, arbitrary rank and arithmetic RH transfer
remain open. RN-P-7ag records a corrected full diagonal compensation target.
