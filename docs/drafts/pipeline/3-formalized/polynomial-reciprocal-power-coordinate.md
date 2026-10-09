# Analytic polynomial power coordinate at infinity and exact root-phase paths

- **ID:** POLYNOMIAL-RECIPROCAL-POWER-COORDINATE-20261009
- **Stage:** 3-formalized
- **Type:** BRIDGE; external novelty unverified; corpus only
- **Parent:** `polynomial-exterior-cycle.md`

## Exact result and paper proof [PROVED HERE]

For a monic complex polynomial P, let d=natDegree P and Q=P.reverse. The inspected coefficient reversal identity gives Q(0)=1. Thus f(w)=w^d/Q(w) is analytic near zero, with exact analytic order d because 1/Q is an analytic unit. For w≠0, the inspected reverse-evaluation identity gives f(w)=1/P(1/w), including the totalized inverse conventions at other polynomial zeros. For d>0, the audited finite-order coordinate theorem supplies an analytic open partial homeomorphism φ around zero with analytic inverse, φ(0)=0, nonzero derivative throughout its source, and φ(w)^d=1/P(1/w) for every nonzero source point. Its source can lie inside any prescribed neighborhood of zero.

The continuous phase q_d(t)=exp(2πit/d) has initial value one, norm one and no zeros. For d>0, its d-th power is exactly the positive unit circle, and its endpoint is exp(2πi/d). These are exact symbolic path identities. The primitive-root status of that endpoint is supplied by the separately inspected installed `Complex.isPrimitiveRoot_exp` theorem.

## Corpus audit

Source inspection covered `Polynomial.Reverse.coeff_zero_reverse`, `eval₂_reverse_mul_pow`, installed analytic-polynomial composition and analytic inverse constructions, and `circleMap_zero_pow`. The prior power-circle search and exact coordinate-rigidity search are recorded on the parent card. No external sources or numerical computations were used; public novelty is not certified.

## Formal certificate — 2026-10-09

`HTGeometry/PolynomialReciprocalPowerCoordinate.lean` contains 5 public declarations and `HTGeometry/PowerRootCirclePaths.lean` contains 6. Both production leaf builds, all 11 standard-only axiom audits and both final actual-source `lake env lean` checks pass; final logs are empty. Audit log: `/tmp/hgt-reciprocal-power-phase-axioms.log`. Final logs: `/tmp/hgt-PolynomialReciprocalPowerCoordinate-final.log` and `/tmp/hgt-PowerRootCirclePaths-final.log`. Both modules are wired into the HTGeometry umbrella. The index/lint refresh now running also includes the previously audited primitive-coordinate rigidity module.

The subsequent index refresh passed (`/tmp/hgt-reciprocal-coordinate-index.log`). Authoritative global lint reports only the unrelated unreachable module `RHTower.PaperMaassFourierReconstruction`; no error concerns these modules (`/tmp/hgt-reciprocal-coordinate-lint.log`).

The actual large-circle capture and explicit exterior polynomial root lift remain in progress. This card proves their analytic coordinate and path ingredients, not the full exterior monodromy, prescribed polynomial realization or RH.
