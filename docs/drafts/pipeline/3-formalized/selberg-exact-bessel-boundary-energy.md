# Exact critical Bessel slope and cusp boundary energy

- **ID:** SELBERG-EXACT-BESSEL-BOUNDARY-ENERGY
- **Stage:** 3-formalized
- **Parent:** [Constructive Selberg loop](../1-in-progress/selberg-quarter-conjecturing-loop.md), cycle 14.
- **Scope:** Actual source-defined Bessel functions and compact real C¹ cusp profiles. No general Maass Fourier expansion or core positivity is assumed.

## Exact positive survivor

For the Schlaefli-integral Bessel functions, put `q(s)=s*K_1(s)/K_0(s)` and `Q(t)=q(exp(t))`. The range of `Q` is exactly `(0,infinity)`, and `Q` is strictly increasing. There is a unique `tau` with `Q(tau)=1/2`, and `0<exp(tau)<1/2`.

For `G(a,t)=exp(t/2)*K_0(exp(a+t))`, the actual outgoing logarithmic-height boundary coefficient is

`B(a,t)=-G'(a,t)/(exp(t)*G(a,t))=(Q(a+t)-1/2)/exp(t)`.

It is negative, zero, or positive exactly when `a+t` is less than, equal to, or greater than `tau`. For every compact real C¹ profile `f`, the actual integrals satisfy

`integral_(t>T) exp(-t)*(f'^2+(exp(a+t)^2-1/4)*f^2)`

`= integral_(t>T) exp(-t)*(f'-(1/2-Q(a+t))*f)^2 + B(a,T)*f(T)^2`.

Consequently one quarter of weighted mass is at most kinetic plus horizontal energy whenever `T>=tau-a`. In height/frequency variables this sufficient condition is `k*Y>=exp(tau)`, strictly improving the earlier sufficient condition `k*Y>=1/2`.

## Dependency-closed paper proof

The inspected source integral gives `K_0>0`, `K_1>K_0`. Its argument derivative and order recurrence give `K_0'=-K_1` and `K_1'=-(K_0+K_1/s)`. Quotient differentiation yields `q'=(q^2-s^2)/s`; since `q>s>0`, this derivative is positive. Hence `Q'=Q^2-exp(t)^2` and `Q` is positive and strictly increasing.

To prove small values without assuming an asymptotic expansion, suppose `Q>=d>0` everywhere. Set `T=log(d/2)` and `c=d^2/2`. For `t<=T`, the differential equation gives `Q'(t)>=c`. The function `Q(t)-c*t` is therefore nondecreasing on that left interval. Comparing `T` with `t=T-(Q(T)+1)/c` gives `Q(t)<=-1`, contradicting positivity. Thus `Q` has values below every positive target. The bound `q(s)>s` gives values above every target. Continuity and strict monotonicity prove the exact range and uniqueness. At the half-value point, `q(s)>s` gives the strict argument bound.

Differentiating `G` gives `G'=(1/2-Q(a+t))*G` and `G''-G'=(exp(a+t)^2-1/4)*G`, proving the outgoing formula and sign classification. Put `r=1/2-Q(a+t)` and `J=exp(-t)*r*f^2`. Expand the square and use the Riccati law to obtain `excess=square+J'`. All fields are continuous with compact support, as is the flux derivative. The compact-support fundamental theorem gives `integral_(T,infinity) J'=-J(T)`. The square is nonnegative, yielding the lower boundary estimate and sufficient tail inequality.

## Lean implementation and audit

- `GaloisForLFunctions.RHTower.SelbergBesselBoundarySlope`: actual derivatives, range, unique transition, critical mode equation, and outgoing sign classification.
- `GaloisForLFunctions.RHTower.SelbergBesselBoundaryEnergy`: integrability, `critical_boundary_identity`, `exact_boundary_lower_bound`, `cusp_tail_quarter`, and `range_tail_cutoff`.
- Existing argument-derivative and strict-comparison proofs were extracted unchanged into `HTGeometry.BesselArgumentDerivative` and `HTGeometry.BesselOrderPositiveComparison`. Existing public names and compatibility imports are preserved; source-text equality of the moved proof bodies was checked.

All four modules passed scratch/direct checks and targeted final builds. Both compatibility modules passed direct compilation. The fifteen-capstone scratch audit `/tmp/selberg_bessel_boundary_axioms.lean` also imports both compatibility modules and reports only `propext`, `Classical.choice`, and `Quot.sound`. All new modules are wired into their umbrellas. An initial broad-dependency targeted build was stopped after it spawned parallel workers; the build correction and cleanup are documented on the parent card. Only the subsequent serialized builds count as passing audits. Final lint and process results are recorded on the parent card.

## Scope of the boundary

The coefficient sign transition is exact. Cycle 14 itself proves sufficiency only: a negative seam term alone does not construct a negative-energy test. Cycle 16 subsequently proves the [exact trace-energy infimum and necessity of the isolated-tail cutoff](selberg-sharp-cusp-trace-infimum.md) using explicit compact approximants. General Maass nonzero-mode identification, energy closure, all-cusp covariance, and congruence-uniform core coupling remain obligations for Selberg.
