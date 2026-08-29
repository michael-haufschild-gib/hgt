# Theta C5 center velocity: likelihood Bregman cone and transfer no-go

Status: formalized in Lean 4  
Route: CLG/TTF, modular-center direct velocity (`C5-VP1` / `C5-VP2`)  
Date: 2026-08-29

## Result

For `t > 0`, write literal modular-center action and slope as

`A = Q - D`, `a = p - E`,

where `(Q,p)` is first-atom action/slope centered at exact likelihood seam tangent and `(D,E)` is
higher-atom likelihood Bregman displacement. Lean proves, unconditionally,

- exact decomposition of action, slope, and C5 first-atom-curvature core;
- strict cone `0 < D < tE`;
- source-specific anti-collapse `E < 1` and hence `D < t`;
- first-atom strong convexity `38t <= p` and `19t^2 <= Q`;
- literal-source barriers `38t - 1 < a` and `19t^2 - t < A`.

Generic cone transfer is false. Even the strict Bregman cone, both strong-convexity floors, positive
second jet, positive third jet, positive actual action/slope, and `A <= a` admit a negative C5
velocity core. This kills every source-independent proof of `C5-VP1` using only those inequalities.

## Strongest positive survivor

Define

`drive = 39q1 + t(q2-q1^2) + 5t^2(q3-3q1q2+q1^3)`,

`tax = 17tq1^2 + 3t^2q1(q2-q1^2)`.

In curvature-dominant chamber `q1^2 < q2`, with positive action, time, and slope, Lean proves sharp
classification

`core >= 0 <-> 0 < drive and tax / drive <= exp(A) - 1`.

Thus surviving theta-specific burden is exact action-barrier coupling. Convex/Bregman geometry alone
cannot close it. Higher likelihood cannot manufacture generic near-zero collapse because its actual
slope deficit is uniformly below one.

## RH proof-chain consequence

Proving source-specific drive positivity and action reserve
`-> thetaCuspCenterFifthRootVelocityFirstAtomCurvatureCore >= 0`
`-> strict literal modular-center velocity`
`-> modular-center C5 by seam anchoring/radial monotonicity`
`-> off-center transport + higher packets + source-to-Weil no-escape`
`-> RH`.

This result does not prove RH or full modular-center C5. It kills generic `C5-VP2` cone transfer and
replaces it with exact source-specific action barrier.

## Lean certificate

Module:
`GaloisForLFunctions.RHTower.ThetaCuspFifthRootCurvatureVelocityLikelihoodBregmanCone`

Key theorems:

- `thetaCuspCenterLikelihoodBregmanAction_lt_mul_slope`
- `thetaCuspCenterLikelihoodBregmanSlope_lt_one`
- `nineteen_mul_sq_sub_self_lt_thetaCuspReflectedLogAction_zero`
- `exists_c5VelocityActionCore_neg_of_positive_curvatureGap`
- `not_C5VelocityStrongTangentBregmanConeTransfer`
- `c5VelocityActionCore_nonneg_iff_drive_pos_and_reserve`
- `thetaCuspCenterFifthRootVelocityFirstAtomCurvatureCore_eq_bregmanCone`

Verification:

- `lake env lean GaloisForLFunctions/RHTower/ThetaCuspFifthRootCurvatureVelocityLikelihoodBregmanCone.lean`
- `lake build GaloisForLFunctions.RHTower.ThetaCuspFifthRootCurvatureVelocityLikelihoodBregmanCone`
- selected `#print axioms`: only `propext`, `Classical.choice`, `Quot.sound`
- no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` in module
- umbrella import added to `GaloisForLFunctions/RHTower.lean`

Repository-wide formal lint still reports unrelated unreachable concurrent modules and an existing
`sorry` in `RHTower/Sieve/KubalalikaPowerEnvelope.lean`; no reported debt is in this module.
