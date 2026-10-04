# MC squarefree discrepancy: absolute derivative-envelope contraction

- **ID:** MC-C12.93-absolute
- **Stage:** 5-failed
- **Type:** FALSIFIED CONSTRUCTION; unconditional Lean audit complete,2026-10-04,1005k.
- **Source:** `../3-formalized/mc-squarefree-discrepancy-response.md`.

## Failed proposal

For exponents a approaching one half from below, estimate the derivative in the exact
signed squarefree-discrepancy equation by its absolute power envelope, replace E by |E|,
and obtain contraction from

    b(a)=a/rho*integral_1^infinity |E(x)|*x^(a-2) dx < 1.

Here E(x)=sum_(n<=floor(x))mu(n)^2-rho*x and rho=6/pi^2. These are the literal full objects.

## Exact killing theorem

`RHTower.SquarefreeDiscrepancy.eventually_one_lt_absoluteResponse` proves b(a)>1 throughout
some left neighborhood of1/2. A fixed negative counting interval inside(1/rho,2) supplies
a uniform positive gap b(a)-q(a)>=eta>0, while the signed response q(a) tends to1.

This closes only the displayed absolute comparison. It does not assert the norm of every
possible dilation operator, falsify the source sign, retire route MC, or falsify RH.

## Strongest positive survivor

The literal discrepancy has a holomorphic absolutely convergent Mellin moment on Re(s)>1/2,
with its exact pole-cleared zeta identity. The complex response is

    q(a)=1+a*zeta(1-a)/(rho*(1-a)*zeta(2-2a)),
    q(a)=1 iff zeta(1-a)=0, for0<Re(a)<1/2.

On the real axis q(a)<1 and q(a)->1 at the critical left endpoint. The uniform positive
absolute-minus-signed gap is also formalized. Thus the failure has an exact positive
classification and boundary law, rather than only a negated contraction statement.

## New insight and status

Discarding the discrepancy sign costs a fixed positive amount precisely where the real
signed deficit vanishes. Real-mode dissipation does not control oscillatory modes: unit
response there is exactly the reflected zeta-zero condition. The actual signed Liouville
correlation still needs a new lower estimate.

Dependency-closed paper proof and complete source/freshness audit are in the survivor card.
Leaves: `SquarefreeDiscrepancyMellin.lean` and `SquarefreeDiscrepancyCriticalGap.lean`.
Both targeted builds and both required final `lake --old env lean` checks passed; all23
public theorem axiom checks report only propext/Classical.choice/Quot.sound. Both imports
wired; no umbrella build. Global lint retains13 unrelated reachability failures, no error
for either leaf. No new axiom, placeholder, numerical mathematical experiment, heartbeat
increase, subagent or commit. One accidental audit-process overlap was stopped and corrected
before the final sequential successful audits; exact details are retained in the survivor card.
