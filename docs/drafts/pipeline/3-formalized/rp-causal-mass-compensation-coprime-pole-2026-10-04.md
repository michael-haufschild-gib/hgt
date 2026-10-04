# RP72 — Exact coprime source pole of causal native mass compensation

- **ID:** rp72-causal-mass-compensation-coprime-pole
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Route RP; rp-joint-coprime-native-coercivity-2026-10-04 in 1-in-progress.
- **Statement:** In the literal causal mass-compensation family, the complete critical coprime source is admitted at damping in [0,1] exactly when the compensation coefficient is zero. Every nonzero coefficient produces an explicit positive exponential leading term.

## Exact carrier and theorems

Let `a(t)=criticalAbelLogProfile t`, `m(T)=integral_0^T a`, and `D=divisorHarmonicBoundary>0`. For real lambda define

`g_lambda(t)=exp(t)*(a(t)+lambda*m(t))`,

`S_lambda(t)=exp(-t)*logarithmicCoprimeEnergy g_lambda t`.

The coefficient-zero carrier is exactly `routePCoprimeNativeProfile`; every coprime pair and original physical cutoff is retained.

The new exact asymptotic is

`exp(-T)*S_lambda(T) -> (lambda*D/3)^2*(6/pi^2)`.

For every `0<=eta<=1`,

`IntegrableOn (exp(-eta*t)*S_lambda(t)) (Ioi 0) iff lambda=0`.

The causal residual also satisfies the exact finite-window energy identity. For `lambda=1-epsilon`,

`integral_0^T exp(lambda*t)*(a(t)+lambda*m(t))^2`

`= integral_0^T exp(-epsilon*t)*routePNativeCriticalProfile(t)^2`

`  + lambda*exp(lambda*T)*m(T)^2`.

Thus its terminal square is nonnegative for epsilon at most one. Its zero-damping square is unconditionally nonintegrable.

## Dependency-closed paper proof

1. The existing absolute quadratic moment of a and its exact zero mass give `m(T)=-integral_T^infinity a` and `(1+T^2)*|m(T)|<=integral_0^infinity (1+t^2)*|a(t)|` for nonnegative T. Consequently m is integrable and `T*m(T)->0`. Finite integration by parts and the existing signed first moment `integral t*a(t)=-D/3` give `integral m=D/3`.
2. The actual right derivative of g_lambda, including all arithmetic jumps, is `exp(t)*w_lambda(t)`, where `w_lambda=(1+lambda)*a+criticalAbelLogVelocity+lambda*m`. This weighted force is absolutely integrable, with exact total mass `lambda*D/3`. The every-point right-derivative FTC identifies g_lambda with its finite primitive.
3. Exact finite logarithmic dilation quadrature gives `exp(-T)*Dg_lambda(T)=integral_0^infinity w_lambda(t)*K(T-t)dt`, where `K(u)=exp(-u)*floor(exp(u))`. The kernel is measurable, lies in [0,1], vanishes for u<0, and tends to one. Dominated convergence proves the normalized dilation-source limit `lambda*D/3`; the same representation gives a bound at every physical clock.
4. The existing exact coprime identity is `CoprimeEnergy(g)=MobiusInverse((Dg)^2)`. After division by exp(2T), its n-th active term is `mu(n)/n^2` times the squared normalized dilation source at `T-log(n)`. The bound from step 3 supplies a summable inverse-square majorant. Dominated convergence of the entire finite-cutoff sum gives the coefficient `(lambda*D/3)^2*sum mu(n)/n^2`. The actual reciprocal-square identity is `sum mu(n)/n^2=1/zeta(2)=6/pi^2>0`.
5. For lambda nonzero and eta at most one, the damped source eventually dominates a strictly positive constant. Absolute admission on an infinite ray is therefore impossible. For lambda zero, the existing native combined balance is admitted at zero damping, and multiplication by any nonnegative damping preserves admission. This proves the classification.
6. Separately, differentiating `lambda*exp(lambda*T)*m(T)^2` proves the finite energy identity. The terminal value at zero is retained and vanishes because m(0)=0. The existing cofinal native square-energy escape then proves the zero-damping compensated square obstruction.

## Lean certificates

All final commands were `lake --old env lean <leaf> -o <olean>`, from formal. No full or umbrella build was run.

- RoutePNativeMassCompensation — audit88214, exit0.
- RoutePNativeMassPrefixMoments — audit77570, exit0.
- RoutePNativeMassDilation — audit37084, exit0.
- RoutePNativeMassCoprimeAsymptotic — audit80287, exit0.
- RoutePNativeMassCoprimeAdmission — audit48568, exit0.

All five leaves are explicitly wired into RHTower.lean. Combined /tmp audit37812 exited0, including all repaired API probes, the exact reciprocal-square identity, and #print axioms for all16 new public theorems. Every theorem uses only propext, Classical.choice and Quot.sound. No added axioms, numerical experiments or heartbeat increases.

Authoritative global lint18348 exited1 with unrelated unreachable-module diagnostics. Its stderr exceeded the tool output budget; no global lint pass or exhaustive list of unrelated failures is claimed. The five owned modules are explicitly wired and their individual kernel audits passed.

## Scope and remaining frontier

This closes the attempt to replace the native carrier by a nonzero causal mass residual while retaining the admitted complete coprime source. Its positive survivor is the exact source coefficient and sharp zero-coefficient admission boundary.

The separately chosen zero-total-mass continuation at each terminal cutoff is a different family. Uniform estimates for that family remain open. No positive-damping native square payment, signed high-LCM payment or physical history floor has been proved here. RH remains unproved and unfalsified.

## Log

- 2026-10-04 — RP72 paper proof and five leaf audits completed; 16 public axiom checks passed. Failed-method record: rp-causal-mass-compensation-budget-2026-10-04 in 5-failed.
