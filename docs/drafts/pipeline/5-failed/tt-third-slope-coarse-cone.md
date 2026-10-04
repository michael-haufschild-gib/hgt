# TT third-slope coarse cone and expanding-mode survivor

- **ID:** tt-third-slope-coarse-cone (C65)
- **Stage:** 5-failed
- **Type:** FALSIFIED, with formalized positive survivor
- **Source:** ../1-in-progress/tt-actual-odd-border-primitive.md
- **Statement:** The known strict pointwise source inequalities do not force a positive third-minor slope.

## Exact scope

Write V=u², K=k, Z=J/u and let S be the exact squared-chart integer third-slope polynomial. The conjectured cone was

    0<V<9, K>5/4, 0<Z<1/3,
    K²(9−V)<361/25,
    F=K²(9−V)−6K−4+2V(K+2/3)Z>0.

There exists a strict interior cone point with S<0. This does not identify a point of the actual modular source orbit and does not falsify RH or actual-source third-slope positivity.

## Dependency-closed paper proof and positive survivor

Set h=1/K, r=K²(9−V), t=K(1−3Z). Thus V=9−rh² and Z=(1−th)/3. The exact source derivation, multiplied by h, extends to a polynomial vector field H. Its boundary action is

    Hh=0, Hr=−108r, Ht=−18r+108t, H(r−12t)=108(r−12t).

Exact regularization of all five reflected moments gives polynomials s2,s4,s6,s8,s10 equal to h³M2,h⁴M4,h⁵M6,h⁷M8,h⁹M10 for h≠0. Their boundary values are

    −6⁴·24,
    6⁶·1728,
    6⁸(−207360+1296(r−12t)),
    6¹⁰·46656(r−12t),
    6¹²·1679616(r−12t).

Substitution in the complete cubic determinant gives h¹⁷p=P and

    P(0,r,t)=−C(r−12t), C=6²⁴·1990656·1679616>0.

The quadratic mode terms cancel. Applying the full vector field H through the exact Jacobian, not a derivative along fixed r,t, gives h¹⁹S=Q and

    Q(0,r,t)=−648C(r−12t).

Polynomial continuity proves the positive survivor: for every fixed real r,t, S is eventually strictly positive as h→0+ if r<12t, and eventually strictly negative if r>12t. The equality case has no asserted sign.

Take r=1,t=1/24. For every 0<h<1/2 all strict cone inequalities hold. In particular K²(9−V)=1 and

    F=3/4−5h/6−5h²/12+h³/54>0.

The negative-tail theorem supplies a sufficiently small h and hence the cone counterexample. No finite sampling or external mathematical computation is used.

## No-go closure

- **Exact killing theorem:** `HTGeometry.ThetaRatioInfinity.exists_coarseCone_negative_slope`.
- **Strongest positive survivor:** full-flow polynomial regularization and strict boundary-mode sign classification, `scaledSlope_eq`, `scaledSlope_zero`, `slopeValue_eventually_neg`, `slopeValue_eventually_pos`.
- **New insight:** the cone omits trajectory selection of an expanding mode. Actual-orbit control near r−12t=0 is a new precise mathematical obligation; fixed nonzero boundary slices do not settle it.
- **Lean status:** all eleven scratch leaves passed direct `lake env lean` audits; all printed capstones use only `propext`, `Classical.choice`, `Quot.sound`. Production copies `ThetaCuspRatioInfinity{Flow,Moment2,Moment4,Moment6,Moment8,Moment10,Minor,Curve,Slope,Sign,Cone}` are undergoing direct leaf audits. Integration status will be recorded below. Route TT remains active.

## Log

- 2026-10-04 — Exact coarse-cone obstruction and sign-classification survivor proved and checked. Actual-orbit critical-direction selection opened as C66.

- 2026-10-04 — Production integration complete: all eleven leaves passed direct audits; imported capstones standard3; umbrella wired and index refreshed. Lint reports thirteen unrelated umbrella omissions, no errors in these leaves. Superseded scratch sources and caches removed.
