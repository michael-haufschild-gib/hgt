# Complete theta admits no positive uniform Cauchy reserve

- **ID:** RH-FULL-THETA-POSITIVE-CAUCHY-RESERVE-ROOT-20260926
- **Stage:** 5-failed
- **Type:** [BRIDGE] falsified strict-coercivity mechanism; RH unresolved
- **Owner:** root
- **Parent:** `../1-in-progress/rh-full-theta-coercivity-audit-root-2026-09-26.md`

## Exact statement

Let Phi be the complete theta source, K its literal first-moment tail kernel,
and `C(x,y)=Phi(x)*Phi(y)/(exp(2x)+exp(2y))`.
For every real a and every c>0 there exist finite real nodes x_i>a and real
coefficients b_i such that

`sum_ij b_i*b_j*[K(x_i,x_j)-c*C(x_i,x_j)] < 0`.

No strictly positive multiple of C is a quadratic-form lower bound for K on
any real tail, uniformly in rank. This does not claim K has a negative packet.
It excludes strict relative coercivity, a stronger assertion than PSD.

## Dependency-closed paper proof

1. The proved exact complete-source asymptotic gives
   `K(r,r)/[r*exp(-2r)*Phi(r)^2] -> 1/(2*pi)`.
   Therefore `K(r,r)/Phi(r)^2 -> 0`. Exact reflection of Phi and K transfers
   this limit to r->-infinity and retains the full normalized asymptotic.
2. Set `h(z)=Phi(z)/(exp(2z)+1)`. The denominator has positive real part
   on |Im z|<pi/4, so h is holomorphic there and real on the real axis.
   Since exp(2x)->0 as x->-infinity,
   `K(x,x)/h(x)^2 -> 0`. For every d>0, K-d*h*h thus has a negative diagonal.
3. Add h as one scalar component to the complete-source analytic L2 section.
   Its bounded Hermitian form is the old two-channel form plus scalar -2d.
   Closed-span compression realizes exactly `2*(K-d*h*h)`. Analytic density
   transports its negative direction to finite real packets in every tail.
4. For positive u_i, the Cauchy Gram matrix augmented by node 1 is PSD.
   Test coefficients `(-2S,b_1,...,b_n)`, S=sum b_i/(u_i+1), to obtain
   `sum_ij b_i*b_j/(u_i+u_j) >= 2*S^2`.
   The coefficient 2 is attained by the one-node test u=1.
5. Substitute u_i=exp(2x_i) and weights b_i*Phi(x_i). Hence C>=2*h*h as
   quadratic forms. The packet negative for K-2c*h*h is also negative for
   K-c*C. Every step is checked in Lean scratch.

## Positive survivors

- Exact incoming diagonal law:
  `K(-r,-r)/[r*exp(-2r)*Phi(-r)^2] -> 1/(2*pi)`.
- Exact obstruction already for one analytic reference feature h, transported
  to all tails through an actual augmented Hilbert realization.
- Sharp Cauchy projection bound `Q_C>=2*S^2`, proved by its finite Gram form.

The boundary law identifies the failed input: a reference norm must respect
both ends of the completed source. Its dominance cannot be inferred from
matching the outgoing diagonal or each fixed finite asymptotic section.
These positive statements have dependency-closed paper and Lean proofs.

## Whole route and pivot

C6's repaired logarithmic-Cauchy model is still positive in every rank.
A comparison transferring any strictly positive part of its Cauchy reserve
to the literal complete kernel is impossible. A bound that consumes the
whole reserve and leaves zero remains outside this obstruction. Likewise,
a reference norm with different incoming behavior is not excluded.

The sign producer must establish a sharp semidefinite cancellation or use
source-specific comparison geometry compatible with reflection. Refining a
strict positive Cauchy-margin estimate would work on a false target.

## Verification and novelty

Leaf: `formal/GaloisForLFunctions/RHTower/ThetaTailCauchyCoercivityObstruction.lean`.
Scratch and named leaf build pass. All 17 public theorem axiom reports
contain only propext, Classical.choice, and Quot.sound, with none missing.
Leaf wired; index refreshed; final lint --check-generated passes with existing
large-file warnings. All owned proof/search/index/lint jobs exited.
Corpus hybrid/deep/method queries found the exact analytic-locality and
Cauchy Gram ingredients; the dedicated novelty query reported partial
coverage and no applicable duplicate. No global priority claim. No numerical
experiment, Xi-zero premise, or RH hypothesis is used.
