# Geometric tail comparison: boundary tangent test

- **ID:** RH-GEOMETRIC-TAIL-RESERVE-ROOT-20260926
- **Owner:** root
- **Stage:** 1-in-progress
- **Type:** [BRIDGE] obstruction candidate; proof mechanism visible before freezing
- **Parents:** full theta tail kernel, exact geometric-deficit split, analytic locality, C10

## Frozen C11

Let K be the literal complete-theta tail first-moment kernel and G its
existing geometric kernel, with K=2G+D on positive nodes.

For every real a and every epsilon>0, some finite nodes x_i>max(a,0)
and real b_i satisfy sum b_i*b_j*(K(x_i,x_j)-epsilon*G(x_i,x_j))<0.

This is a conjectured obstruction to a strict geometric reserve, not a
conjecture that K is indefinite and not an RH conclusion. G is a natural
remaining comparison because it retains the complete integrated source;
C10's charged point-value test alone does not exclude it.

## Interrogation / route relevance

- Irritant: G is positive by a square root, while K itself has holomorphic
  continuation through x=0. Keep the square root's boundary singularity.
- Where is theta used? Phi(0)>0, differentiability, global decay, and the
  actual analytic K realization. No first-atom approximation.
- Change of viewpoint: test the tangent energy of the positive feature
  family, instead of comparing values or far-tail asymptotics.
- Why [BRIDGE]? The exact feature derivative exposes a proof route. This is
  not presented as a distant universal conjecture.
- Whole route: if true, the exact K=2G+D strategy can only reach the sharp
  boundary D>=-2G. Any fixed positive relative margin is impossible.
- Right problem gate: only finish this work if it yields the actual all-tail
  obstruction and the sharp positive tangent invariant. A toy square-root
  singularity by itself is insufficient.

## Paper attack

For x>0 the geometric feature derivative is

    v'_x(s)=Phi(x+s)/(2*sqrt(x+s))+sqrt(x+s)*Phi'(x+s).

Its squared norm equals

    G_11(x,x)=1/4*integral_x^infinity Phi(t)^2/t dt
              -1/2*Phi(x)^2+integral_x^infinity t*Phi'(t)^2 dt.

The actual K mixed derivative equals

    K_11(x,x)=-Phi(x)^2+2*integral_x^infinity t*Phi'(t)^2 dt.

Hence the exact tangent identity is

    G_11(x,x)=K_11(x,x)/2+1/4*integral_x^infinity Phi(t)^2/t dt.

Phi(0)>0 forces logarithmic divergence of the last integral as x decreases
to zero, while K_11 stays finite. Thus K-epsilon*G has a negative confluent
two-point form near zero. A strict finite two-point witness follows from
finite differences. Analytic negative-index transport on the right half
strip then carries the witness to every real tail. All interchanges,
regularity, source derivatives, integrability, and transport remain to audit.

## Strongest positive survivor to extract

Exact tangent decomposition above and the sharp logarithmic law

    G_11(x,x)/log(1/x) -> Phi(0)^2/4  as x->0+.

This quantifies the artificial tangent energy introduced by the square-root
factorization. It separates analytic K from its positive geometric part.
No no-go retirement before this survivor is paper-closed and formalized.

## Plan / current evidence

1. Corpus and novelty search (including method/deep search); inspect actual APIs.
2. Dependency-closed paper proof or explicit falsifier; retain C11 unchanged.
3. Scratch Lean for exact tangent identity and logarithmic source law.
4. Derive finite negative packet near zero and analytic all-tail transport.
5. Named leaves only, standard axiom audit, umbrella wiring, formal lint.

No numerical mathematical experiments, git commands, heartbeat overrides,
or full/umbrella builds. Current C11 status: frozen, not proved.

## Derived positive survivor: finite part

Paper-closed refinement of the logarithmic claim (a derived bridge, not a
new primary conjecture): for f=Phi²,

    integral_(t>x) f(t)/t - f(0)*log(1/x)
      -> integral_0^1 dslope(f,0,t) dt + integral_(t>1) f(t)/t.

Reason: differentiability at zero makes dslope(f,0) continuous; its compact
primitive absorbs the complete local remainder. The exact identity holds
for every x>0, not merely asymptotically. Schwartz decay handles the retained
infinite tail. Scratch proof of the generic identity passes its algebra and
integrability steps; endpoint-limit typing is still being checked.

Whole-route meaning: identify the exact divergent geometric term and finite
source remainder, then compare with the analytic K tangent. This alone is
not the all-tail no-go or a sign result for K.

Scratch verification now closes the generic inverse-tail finite-part identity
and limit, actual source/derivative weighted integrability, improper source
integration by parts, exact geometric tangent energy decomposition, and both
actual-source finite-part and sharp logarithmic limits. Artifact:
`/tmp/rh-c11-energy.lean` (exit 0; one proof-style warning being removed).
These are not yet promoted leaves. The geometric kernel mixed derivative
identification and finite-packet/all-tail C11 conclusion are still open.
