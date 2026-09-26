# Uniform squared-Cauchy repair of the logarithmic kernel

- **ID:** RH-LOG-CAUCHY-UNIFORM-REPAIR-ROOT-20260926
- **Stage:** 3-formalized
- **Type:** [BRIDGE]; RH remains open
- **Owner:** root
- **Parent:** `../1-in-progress/rh-nonlocal-tail-root-2026-09-26.md`

## Exact theorem

For every positive c and real L satisfying L+log(c)>=2, the kernel

`H(u,v)=[L+(log u+log v)/2]/(u+v)+c/(u+v)^2`

is positive semidefinite on every finite family of positive real nodes. There
is no dependence on rank, spacing, or a lower bound for the nodes. The initial
restriction c<=1 was removed by the exact scaling law. No optimality claim
for constant 2.

For the literal-source first-correction model, L=2r and
c=7r*exp(-2r)/pi. The condition holds whenever r>=pi*exp(2)/7.

## Dependency-closed paper proof

Fix arbitrary real coefficients a_i and positive nodes u_i. Put
f(s)=sum_i a_i exp(-u_i*s), E=integral_(s>0) f(s)^2,
M=integral_(s>0) s*f(s)^2 and C(t)=integral_(s>0) f(s+t)*f(s).
Every integrability and exchange is a finite sum of exponential integrals;
M uses integral s*exp(-v*s)=1/v^2 for v>0. Thus E and M are exactly the
Cauchy and squared-Cauchy quadratic forms and are nonnegative.

Frullani, applied before splitting the cancelled numerator, gives

`Q_log=L*E+integral_(t>0) [exp(-t)*E-C(t)]/t`.

Indeed integral [exp(-t)-exp(-u_i*t)]/t=log(u_i), and symmetry replaces
log(u_i) by the average of the two node logarithms. Every cancelled summand
is absolutely integrable. Neither divergent term at zero is integrated alone.

Write T(t)=integral_(s>t) f(s)^2. Then T(t)<=E and t*T(t)<=M for t>=0.
Integrating the pointwise square [f(s)-b*f(s+t)]^2 yields
`2b*C(t)<=E+b^2*T(t)`. Choosing b=1 gives C(t)<=E. Choosing b=sqrt(t)
gives, for t>0, `C(t)/t<=(E+M)*t^(-3/2)/2`.

On 0<t<=1, exp(-t)>=1-t gives the cancelled integrand >=-E. On t>1,
discarding the nonnegative exponential term gives a lower bound
`-(E+M)*t^(-3/2)/2`. Its integral is -(E+M). Therefore

`Q_log+M >= (L-2)*E`.

This proves the c=1 assertion. Set u=c*v. The exact identity
`H_(L,c)(u,w)=c^(-1)*H_(L+log c,1)(u/c,w/c)` proves the result for every
c>0. In particular no c<=1 condition is needed.

## Quantitative survivor exposed by the proof

Subtracting the level 2-log(c) form gives the stronger bound
`Q_H >= [L+log(c)-2]*E`. At the theta first-correction scale this is
`Q_H >= [log(7r/pi)-2]*E`. This strengthening is Lean-closed; it follows by exact finite algebra from the proved
PSD threshold. It supplies a concrete uniform budget for a signed remainder.

## Whole-route audit

The uncorrected model fails at growing rank; the first positive correction
repairs it at every rank once the displayed condition holds. This is stronger
than rescuing one alternating coefficient vector. It does not prove the full
theta kernel PSD: its omitted terms must be controlled in a compatible
quadratic form, not by entrywise asymptotics. No exchange of limits or RH
conclusion is claimed.

Deep/method retrieval found Frullani, finite Cauchy Gram integrals, exponential
moments, and general analytic-kernel negative-index locality. The latter still
requires an applicable literal kernel realization; it is not assumed here.
The new repair statement was checked against these exact source dependencies.
No global novelty claim.

## Lean status

`formal/GaloisForLFunctions/RHTower/LogarithmicCauchyUniformRepair.lean`,
namespace `RHTower.LogCauchyRepair`. The lower logarithmic-form bound, exact
scaling, all-rank PSD theorem, and symbolic theta-model threshold pass scratch
and the named leaf build, including both quantitative lower bounds. Leaf wired.
All 9 public theorem axiom reports contain only `propext`, `Classical.choice`,
`Quot.sound`. Index refreshed; final `scripts/formal_tools.py lint --check-generated` passes
with existing large-file warnings. All owned jobs exited.
