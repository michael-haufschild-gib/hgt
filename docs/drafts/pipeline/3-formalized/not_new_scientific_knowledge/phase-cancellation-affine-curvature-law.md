# Affine noncollision and off-line quartet curvature law

- **ID:** `phase-cancellation-affine-curvature-law`
- **Stage:** 3-formalized/not_new_scientific_knowledge
- **Type:** THEOREM (Lean), `[POSITIVE SURVIVOR] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Source:** `phase-cancellation-crux.md` §§3 and 7
- **Statement:** Positive-slope affine root deformations preserve strict order and cannot create
  collisions; the functional-equation quartet reciprocal-square contribution has the exact sharp
  positive window `|tau|<a`.

## Goal

Retain the strongest dependency-closed algebra exposed by the failed universal phase-method
diagnosis, without asserting RH, a global Xi zero expansion, or completeness of any proof-method
class.

## Theorem

For real `a,b,x,y,delta_a,delta_b`:

```text
(a*y+b)-(a*x+b) = a*(y-x),
0<a -> (a*x+b<a*y+b <-> x<y),
0<a -> (a*x+b=a*y+b <-> x=y),
x≠y -> ((delta_a*x+delta_b)-(delta_a*y+delta_b))/(y-x) = -delta_a.
```

For real horizontal displacement `a` and vertical displacement `tau`, the reflected pair and
full quartet satisfy

```text
(-a+i*tau)^(-2) + (a+i*tau)^(-2)
  = 2*(a^2-tau^2)/(a^2+tau^2)^2,

quartetCurvature(a,tau)
  = 4*(a^2-tau^2)/(a^2+tau^2)^2,

0<a -> (0<quartetCurvature(a,tau) <-> |tau|<a).
```

All denominators carry their exact nonzero condition. These statements are elementary field and
order identities; no numerical certificate is used.

## Gates

- [x] 0 → 1 in-progress: exact survivor isolated from overclaimed diagnosis
- [x] 1 → 2 fully-proven: field algebra and real-order proof dependency-closed
- [x] 2 → 3 formalized: theorem
  `GaloisForLFunctions.RHTower.phaseCancellationAffineCurvatureLaw`; exact leaf build green;
  axiom audit standard only
- [ ] 3 → 4 publication-ready: standalone exposition not needed for current internal bridge

## Lean certificate

Module: `formal/GaloisForLFunctions/RHTower/PhaseCancellationAffineCurvature.lean`.

The capstone theorem packages exact affine gap scaling, normalized displacement, noncollision,
quartet reciprocal-square formula, and sharp positivity window. Module is wired into
`GaloisForLFunctions.RHTower`; umbrella was not built.

## No-go provenance

Original card is retired because its universal assertions about all flow/positivity/Laguerre
methods are inconsistent and unquantified. This survivor does not inherit those claims.

## Log

- 2026-08-24 — positive survivor formalized, exact leaf built, axiom-audited, and promoted to
  stage 3; original overclaimed diagnosis sent to stage 5.
