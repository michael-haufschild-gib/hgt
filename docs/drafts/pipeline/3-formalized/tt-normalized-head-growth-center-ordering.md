# Global normalized odd-head growth and source center ordering

- **ID:** tt-normalized-head-growth-center-ordering (C97)
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** docs/reports/rh-current-frontier-map.md, Route TT
- **Statement:** The actual normalized odd head is strictly increasing on the nonnegative ray. For every positive load, the complete source quadratic decreases in its explicit center coordinate. The C94 upper-center endpoint is therefore the worst endpoint.

## Goal
Remove one open endpoint sign from the complete-source compact quadratic problem.
This is a source theorem, with no RH or missing source-sign premise. Global upper
endpoint positivity, the compact transported gap, join/flux decay, integrated
and all-rank positivity, and RH remain open.

## Gates
- [x] 0 → 1: actual source, precise derivative target, corpus-derived mechanism.
- [x] 1 → 2: dependency-closed paper proof below.
- [x] 2 → 3: both direct leaf audits and 17 imported axiom checks passed; no umbrella build.
- [ ] 3 → 4: standalone publication audit.

## Paper proof [PROVED HERE]
Write L_j for the actual j-th logarithmic source derivative, c=-L_2,
v=-L_3, B=-L_4, C=-L_5, E=-L_6, F=-L_7. The exact Bell transfer identifies
H/Phi^4=4T, where T=cE-B²-18c²B+24c^4. The established positive native
head gives T>0. Put b=B-4c, H_d=4v-C, beta=factorCurvature(q), and
R=F-4C+beta H_d.

The current corpus proves c>18, v>0, b>0, H_d>0, B<9c, and R>0 on x>0.
Moreover factorLogSlope(q)=-4-15/q-3/(q+3)<-4 for q>0.
The source seam reserve 18c+4+6factorLogSlope(q)-beta>0 then gives beta<18c.
Differentiate T. An exact polynomial identity is

    c T' = v T + c² R
      + v [b² + 18c²(5c-b) + c³(72c-234)]
      + c H_d [c(18c-beta)+4c+2b].

Every displayed term is positive on x>0. Hence T'>0. Continuity and the
mean-value theorem give strict growth of H/Phi^4 on [0,infinity).
The source log-slope L_1 is negative on x>0 and L_2<0 everywhere.
Thus for every load a>0, the actual coefficient
J_a=2a(H/Phi^4)L_1 has derivative

    J_a'=2a [4T' L_1+(H/Phi^4)L_2] < 0.

Exact native/source incidence gives J_a=eval(loadedLinear a)/p^6 and
J_a'=Re(eval(slopeLinear a)/p^7), p=k-1/6>0. The existing weighted
chart identities give

    eval(centerSlopeCoefficient a)=6^30 u^26 eval(slopeLinear a).

Since u>0, its real part is negative. The C94 source quadratic is affine
in X=x/u, with this coefficient; the proved actual bound
0<X<=Xmax=(k-2/3-J/u)/4 therefore implies
Qupper<=Qactual and Qupper<Qlower, for every real direction eta.
No endpoint determinant sign is inserted into this proof.

## Corpus dependencies
- ThetaCuspC5ClockSourceOrientation: source_projective_upper.
- ThetaCuspCurvatureDefectGrowthSeamOrientation: sourceCurvature_gt_eighteen,
  sourceDefect_curvature_upper, sourceSeamReserve_pos.
- ThetaCuspCurvatureProjectiveGlobal: curvatureDefect_pos.
- ThetaCuspCurvatureDefectSource: source_defect_pos.
- ThetaCuspFullReflectionSixthBellTransfer: complete Bell identity.
- ThetaCuspNativeOddSchurCompensation: native head positivity.
- C92-C94 complete source incidence, weighted chart, and center endpoints.

## Log
- 2026-10-06: older growth-source open-status comment superseded by actual
  later source theorems. Complete corpus search led to the positive identity.
- Production leaves ThetaCuspNativeOddHeadGrowth and ThetaCuspRatioCenterOrdering
  passed direct `lake --old env lean` audits. All 17 public imported capstones
  in /tmp/TTC97ProductionAudit.lean use only propext, Classical.choice, Quot.sound.
  Both modules wired exactly once into RHTower. No numerical experiment,
  added axiom, placeholder, or raised proof limit used.
- Formal lint7639 exit1: 12 unrelated umbrella omissions; no new TT error.
  Scoped whitespace check passed. Full lint is not green.
