# Mass-shifted arcsine-vacuum source-charge flow

- **ID:** `mass-shifted-arcsine-vacuum-source-charge-flow`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/mass-shifted-spectral-trace-route.md` §9.3 exact open core
- **Statement:** Pole-free completed source charge has exact mixed mass derivative and secant budget; every occupied strict frontier forces strictly positive native source-charge density at a later mass.

## Goal

Convert finite positive strict-frontier source charge into actual mass action without newborn-norm
division, fixed reporter, or fixed-mass admission holonomy.

## Exact flow

Let

\[
 C_n(y)=Q_n(y)-32V_nN_{n+1}(y),\qquad V_n=n+\frac38.
\]

Here `Q_n` is actual moving canonical completed source.  Define

\[
 \rho_n(y)=A_n(y)-K_n(y)+32V_n\Phi_{n+1}(y),                 \tag{1}
\]

where `A_n` is next completed arithmetic source layer, `K_n` is bilinear inverse-Hankel admission
connection source, and `Phi_(n+1)=N'_(n+1)` is division-free newborn norm flux.  Exact derivative:

\[
 \boxed{C_n'(y)=-\rho_n(y).}                               \tag{2}
\]

At square mass, `Q_n` is literal adaptive mixed rational--Gamma-minus-von-Mangoldt source, so
(2) is source-native.

For every positive chamber `[a,b]`, mean value theorem gives `c in (a,b)` with

\[
 \boxed{(b-a)\rho_n(c)=C_n(a)-C_n(b).}                      \tag{3}
\]

No pointwise sign is assumed.

## New recession law

Completed Gauss-edge split gives

\[
 0\le N_{n+1}(y)\le {Q_n(y)\over2(n+1)}
\]

eventually at fixed degree. Existing `Q_n(y)→0` therefore forces

\[
 \boxed{N_{n+1}(y)\to0,\qquad C_n(y)\to0.}                 \tag{4}
\]

This uses source as dominating function, not moment computation.

## Strict-frontier discharge

At occupied strict frontier `y=tau_(n+1)`, degree `d=n+1` charge is positive. By (4), choose
`b>y` with `C_d(b)<C_d(y)`. Charge is continuous at singular endpoint and differentiable in
positive open chamber. Applying (3) with endpoint continuity gives `c in (y,b)` such that

\[
 \boxed{ho_d(c)>0,\qquad (b-y)\rho_d(c)=C_d(y)-C_d(b)>0.} \tag{5}
\]

Every false-RH strict contact thus forces one later positive mixed mass-density event.

## Conjecture → proof/fail loop

1. **Fixed-mass admission curvature drives discharge. Failed:** transport is exact endpoint
   cocycle with zero curvature.
2. **Centered source itself is positive action. Failed:** adjacent-degree innovation is signed.
3. **Pole prevents mass transport. Failed:** pole-free charge is continuous at frontier.
4. **Newborn vacuum may survive at infinity. Failed:** completed source squeezes newborn norm to
   zero.
5. **Positive survivor:** exact native density (1), derivative (2), finite mass payment (3), and
   forced positive discharge event (5).

## Lean certificate

Module:

`formal/GaloisForLFunctions/RHTower/XiShiftedArcsineVacuumCompletedSourceChargeFlow.lean`

Principal declarations:

- `xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceMass_eq_two_mul_adaptiveShear`
- `xiShiftedCanonicalAdmissionArcsineVacuumCompletedSourceChargeMass_sq_eq_literal`
- `hasDerivAt_xiShiftedCanonicalAdmissionArcsineVacuumCompletedSourceChargeMass`
- `tendsto_xiShiftedCanonicalAdmissionNorm_succ_zero`
- `tendsto_xiShiftedCanonicalAdmissionArcsineVacuumCompletedSourceChargeMass_zero`
- `exists_xiShiftedCanonicalAdmissionArcsineVacuumCompletedSourceCharge_secant`
- `exists_pos_xiShiftedCanonicalAdmissionArcsineVacuumCompletedSourceChargeDensity_after_strict_frontier`

Verification:

- direct `lake env lean` passes;
- targeted module build passes;
- seven principal axiom checks report only `propext`, `Classical.choice`, `Quot.sound`;
- no forbidden declaration occurs;
- imported by `RHTower.lean`.

## Novelty audit

Corpus search found source-flow and defect-energy budgets, but no full arcsine-vacuum charge
density or strict-frontier discharge theorem (5). Classical Jacobi flow/sum-rule literature does
not contain this shifted-Xi admission-selected rational--Gamma/von-Mangoldt density. Novelty
remains `[NOVELTY UNVERIFIED]`.

## RH impact

RH is not proved. Local source, pole removal, mass discharge, and one-event positivity are closed.
Remaining theorem is genuinely global and degree-uniform:

> Exclude cofinally many positive density events (5) migrating to increasing degrees and disjoint
> mass intervals by proving a common finite budget or cross-degree cancellation/coercivity law for
> `rho_n`.

This is exact effectivity/nonproperness location; finite-level source formation is no longer open.

## Log

- 2026-08-13 — exact density conjectured, derivative/secant/recession/frontier discharge proved and formalized

