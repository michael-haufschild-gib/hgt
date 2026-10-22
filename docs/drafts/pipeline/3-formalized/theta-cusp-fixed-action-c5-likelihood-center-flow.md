# Theta cusp fixed-action C5 likelihood centre flow

- **ID:** TC-C5-LIKE-CENTER
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Lean module:** `GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFixedActionC5LikelihoodCenterFlow`
- **Main theorem:** `c5LikelihoodCenterFlowJets_pos`

## Result

For `0<t<=u`, all three centre-flow jets contributed by the literal higher-atom likelihood action
are strictly positive:

```text
S(u,t) = 2F'(u)-F'(u+t)-F'(u-t) > 0,
M(u,t) = F''(u-t)-F''(u+t) > 0,
N(u,t) = -F'''(u+t)-F'''(u-t) > 0.
```

Lean identifies these respectively with the centre derivative of likelihood action and the centre
derivatives of its first two displacement jets.

## Boundary exposed by hostile computation

These three signs do not make nonlinear C5 compensation monotone under likelihood addition.  The
exact interpolation derivative has both signs.  The surviving route candidate is interpolation
convexity plus the atom-tangent reserve `M_C5'(0) >= -M_C5(0)/5`; see
`../2-fully-proven/computations/2026-08-29-c5-likelihood-interpolation/REPORT.md` and
`../2-fully-proven/computations/2026-08-29-c5-likelihood-tangent-reserve/REPORT.md`.

## Audit

- `lake env lean GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspFixedActionC5LikelihoodCenterFlow.lean`
- `lake build GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFixedActionC5LikelihoodCenterFlow`
- Axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`.
- Wired in `GaloisForLFunctions.RHTower`.

## RH passport

likelihood centre-flow signs + first-atom compensation
→ convex tangent control of literal full-theta far tail
→ compact-middle direct-C5 orientation
→ rank-four packet wall and cofinal no-escape
→ CLG/TTF Weil nonnegativity
→ RH.
