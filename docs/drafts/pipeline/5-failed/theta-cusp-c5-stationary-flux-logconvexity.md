# Theta C5 stationary local flux-log-convexity no-go

- **ID:** `C5-FLC1-NOGO`
- **Stage:** 5-failed
- **Type:** ROUTE KILLED; POSITIVE SURVIVOR FORMALIZED
- **Source:** `theta-c5-cofinal-functional-absorption.md`, conjectures `C5-RB1` and `C5-FLC1`
- **Statement:** At every hypothetical negative local minimum of intrinsic modular-center C5, the
  logarithm of normalized positive source flux `D(sqrt x)/sqrt x` has strictly negative second
  derivative. Therefore stationary/projective local algebra cannot supply the nonnegative local
  flux curvature needed to exclude the witness; it forces the opposite sign.

## RH chain tested

The attempted chain was

`local normalized-flux log-convexity on negative intrinsic minima`
`-> modular-center C5 -> off-center direct-J/rank-four -> higher packets/no escape`
`-> CLG/TTF or Weil positivity -> RH`.

This card kills the first arrow when its input is meant to follow only from the corpus local
projective chamber and intrinsic stationarity. Later joins were never claimed closed.

## Exact obstruction

Write `A` for accumulated drop, `D=A'`, `J=D'`, `K=J'`, and normalize

```text
x = t*D/A,  y = t*J/D,  z = t^2*K/D.
```

Corpus projective decrease gives `0 < x <= 2`. At a negative local minimum of `C5/A^2`, put

```text
d = -(24 - 9*x + 5*x*y - 4*x^2) > 0.
```

Intrinsic stationarity gives the exact certificate

```text
125*x^2*(z-y^2-y+2)
  = -20*(x-2)^2*(x^2+36)
    -5*d*(5*x^2-24*x+48) - 5*d^2 < 0.
```

The quadratic `5*x^2-24*x+48` is strictly positive on `x <= 2`. Moreover,

```text
z-y^2-y+2
  = (t^2*(D*K-J^2) - t*D*J + 2*D^2)/D^2,
```

and Lean differentiates the genuine normalized flux twice to prove

```text
(log (D(sqrt x)/sqrt x))'' at x=t^2
  = (t^2*(D*K-J^2)-t*D*J+2*D^2)/(4*t^4*D^2) < 0.
```

No numerical computation enters any identity or sign proof.

## No-go closure

- **Killing theorem:**
  `not_exists_thetaCuspReflectedSource_intrinsicBalance_localMin_neg_and_normalizedFluxLogCurvature_nonneg`.
- **Failure classification:**
  `thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_failure_forces_normalizedFluxLogCurvature_neg`.
- **Exact burden equivalence:**
  `thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_nonneg_all_iff_intrinsicMin_normalizedFluxLogCurvature_nonneg`.
- **Strongest positive survivor:** any proof must use genuinely nonlocal earlier-flux, likelihood,
  or modular-source information to exclude the quantified strict log-concavity chamber. A local
  nonnegative-curvature conclusion at those minima is already equivalent to global center C5.
- **New insight:** local squared-flux log-concavity is not a defect of a loose estimate; it is an
  exact stationary law with a sum-of-negative-terms certificate.

## Gates

- [x] corpus-derived target and explicit RH proof chain
- [x] exact paper proof and hostile algebra audit
- [x] Lean derivatives, certificate, source instantiation, no-go, and survivor equivalence
- [x] targeted module build and standard-axiom audit
- [ ] publication-ready standalone note

## Novelty audit

Corpus search used `scripts/formal_tools.py research`. The corpus contained global normalized-flux
log-convexity and Bernstein no-gos, intrinsic C5 stationarity, and projective decrease separately;
it contained no stationary fifth-root/log-curvature certificate or failure classification. August
2026 searches found reverse-hazard elasticity and generic log-concavity results but no theta-source
analogue of this exact certificate. Novelty claim is limited to this exact C5 obstruction and its
formal consequence.

## Log

- 2026-08-29 — Route killed on paper and in Lean; exact strict-log-concavity survivor retained.
