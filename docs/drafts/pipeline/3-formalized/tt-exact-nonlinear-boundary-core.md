# Exact nonlinear-boundary source core

- **ID:** tt-exact-nonlinear-boundary-core
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** ../1-in-progress/tt-third-slope-nonlinear-cone.md · Route TT
- **Statement:** Every admissible exact nonlinear-boundary state has a bounded polynomial parameter, and the complete source slope satisfies `h^16*S=nonlinearBoundaryCore(h,s)` for nonzero clock.

## Goal

Replace the quadratic-root boundary sign problem by the sign of one complete polynomial on its physical parameter domain. This proves no slope positivity and assumes no source-sign or RH premise.

## Gates

- [x] 0 → 1: exact source slope, existing nonlinear barrier and selected branch.
- [x] 1 → 2: dependency-closed algebraic proof below, using the previously formalized cubic normal form and small-branch theorem.
- [x] 2 → 3: both production leaves passed direct `lake --old env lean` audits; imported axiom audit recorded in the working log.
- [ ] 3 → 4: no standalone publication prepared.

## Paper proof [PROVED HERE]

Put `b(h)=1/12-7h/72`, `T(h,s)=b(h)*s` and
`R(h,s)=s*(1-h^2*b(h)*s)`. Then
`T-h^2*T^2=R*b(h)` identically. Conversely, if `b(h)≠0`, every
solution is recovered by `s=t/b(h)`.

For an admissible real state, `0<h≤4/5`, `0<r≤361/25`,
`V=9-r*h^2>0`, `t>0`, `h*t<1`, and equality in the nonlinear barrier,
apply `failure_small_branch` with `q=t/r`. It gives `h^2*t<1/6`.
Since `b(h)>0`, the recovered `s>0` satisfies
`r=s*(1-h^2*t)>(5/6)*s`, hence `s<(6/5)*(361/25)`.

Let `B(h,r)=r*b(h)+r^2*h^2/144-7*r^2*h^3/432` be the existing cubic
comparison sheet. The exact gap is

`T(h,s)-B(h,R(h,s))=h^4*J(h,s)`,

where

`J=b(h)*s^3*(2-h^2*b(h)*s)*(1/144-7*h/432)+49*s^2/5184`.

Write `A` for the existing full transverse core and `L` for the cubic
core. Their established identity is
`Q(h,r,B(h,r)+u)=u*A(h,r,u)+h^3*L(h,r)`.
Substituting the exact gap gives, at every complex `h,s`,

`Q(h,R,T)=h^3*C(h,s)`,
`C(h,s)=L(h,R)+h*J(h,s)*A(h,R,h^4*J(h,s))`.

The already-established full source incidence `h^19*S=Q` therefore
gives `h^16*S=C` for `h≠0`. The source point is exactly
`V=9-R*h^2`, `K=h⁻¹`, `Z=(1-h*T)/3`. No derivative of a
boundary-substituted minor is used: `S` is the original complete slope.
Finally, `C(0,s)=1944*axisMinorMass-63*principalMass*s^2` follows from
the existing cubic-core identity.

## Lean

- `ThetaCuspRatioNonlinearBoundaryParameter.lean`: polynomial curve,
  inverse reconstruction and complete admissible-state coverage.
- `ThetaCuspRatioNonlinearBoundaryCore.lean`: exact fourth-order gap,
  full scaled-slope identity, full source incidence and exact clock-face value.
- Both leaves are imported by `GaloisForLFunctions/RHTower.lean`.
- No full build or umbrella build performed.

## Open hard problem

Prove `(nonlinearBoundaryCore (h:ℂ) (s:ℂ)).re>0` throughout the physical domain, or falsify this
boundary positivity conjecture exactly. Since the complete source has
its already-proved `V` factor, `C` vanishes on the physical seam; a
positive certificate on a larger closed rectangle must first retain
or remove this factor correctly. Interior/transverse positivity,
full source-quadratic positivity, fourth Schur gap, join, all-rank
closure and RH remain open.

## Log

- 2026-10-04 — Exact curve, coverage and complete source core formalized.
