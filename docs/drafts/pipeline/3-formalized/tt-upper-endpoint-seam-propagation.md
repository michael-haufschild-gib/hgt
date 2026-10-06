# Actual upper-endpoint positivity on a common seam neighborhood

- **ID:** tt-upper-endpoint-seam-propagation (C111–C113)
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** docs/reports/rh-current-frontier-map.md, Route TT
- **Statement:** At load 10^13, one neighborhood of zero makes the complete actual upper-center quadratic strictly positive at every positive center in that neighborhood, simultaneously for all real directions.

## Goal and remaining frontier
Close the actual seam end of the compact source-quadratic problem. The exact
upper-center ordering already puts this endpoint below the actual source
quadratic. The intervening compact region, global last-entry positivity,
compact gap propagation, controlled joining, integrated/all-rank positivity,
and RH remain open. This theorem is about the actual source, with no RH or
missing source-sign premise. It does not assert a global sign.

## Gates
- [x] 0 → 1: full actual source, precise endpoint target, corpus-derived mechanism.
- [x] 1 → 2: dependency-closed proof below.
- [x] 2 → 3: three direct leaf audits and all24 imported public axiom checks passed.
- [ ] 3 → 4: standalone publication audit.

## Proof [PROVED HERE]
Let a=normalizedBase(10^13), b=normalizedB, d=normalizedD, and
L=centerDrive(10^13). Retain the exact actual shear gap

    e(x)=w(x)-2u(x)/3-4x
        =u(x)(k(x)-2/3)-J(x)-4x.

The full modular source ODE gives e'=2uw/3. Since u(0)=w(0)=0,
e(0)=e'(0)=0. At every positive center, the gap between the actual and
upper endpoint center coordinates is exactly e/(4u).

The complete affine center identity and source incidence now give

    Re Qupper(x,t)=N(x)*[a'(x)+e(x)L'(x)/4+2b'(x)t+d'(x)t^2],
    N(x)=6^30*u(x)^25*(k(x)-1/6)^7>0.

All source moments, cofactor terms, and the border are retained. The identity
holds for arbitrary real load before specialization to 10^13.

The complete source is smooth and nonzero; its reflected moments give
smooth a,b,d,L and a'(0)=b'(0)=d'(0)=0. Introduce removable divided slopes

    A(x)=dslope(a',0,x)+dslope(e,0,x)*L'(x)/4,
    B(x)=dslope(b',0,x),
    D(x)=dslope(d',0,x).

These are continuous at zero. The zero first jet of e gives
A(0)=a''(0), B(0)=b''(0), D(0)=d''(0). The previously formalized exact
seam moment model proves A(0)>0 and A(0)D(0)-B(0)^2>0. Continuity therefore
preserves both strict inequalities on one common neighborhood.

For every real t, the exact identity

    A*(A+2B*t+D*t^2)=(A+B*t)^2+(A*D-B^2)*t^2

proves A+2B*t+D*t^2>0 on that neighborhood: use A>0 when t=0,
and the positive second term when t is nonzero. The neighborhood is fixed
before quantifying over t. Finally, the divided-slope identities give

    Re Qupper(x,t)=N(x)*x*(A(x)+2B(x)*t+D(x)*t^2).

Both external factors are positive for x>0, proving the theorem.

## Formal capstones
Namespace RHTower.ThetaCuspUpperSeam:

- actual_upper_center_real_identity: full exact upper/source correction identity.
- normalizedBase_regular, normalizedB_regular, normalizedD_regular: smoothness and zero first seam derivative.
- centerDrive_smooth, hasDerivAt_shearGap: the actual correction's regularity and exact derivative.
- scaled_seam_signs: strictly positive first entry and determinant at zero.
- actual_upper_quadratic_positive_near_seam: unconditional common-neighborhood, all-direction sign.

Production modules:
ThetaCuspRatioUpperCenterRealIdentity, ThetaCuspOddSeamRegularity,
ThetaCuspRatioUpperCenterSeamPositive. All three are wired into RHTower.

## Validation
Direct `lake --old env lean -o <module.olean> <module.lean>` audits passed
serially. Final imported audit:
`lake --old env lean /tmp/TTC113UpperSeamProductionAudit.lean`.
All24 public declarations use only subsets of propext, Classical.choice,
Quot.sound. No new axiom, placeholder, source premise, numerical experiment,
or raised proof limit. No umbrella build.

Logs: /tmp/tt_c113_seam_production_audits/. Detailed conjecture and repair
history: docs/drafts/pipeline/1-in-progress/tt-kinetic-contraction-source.md.
Lint status is appended by the guarded finalizer from the completed lint log.

Latest repository lint: 11 unrelated umbrella omissions; no new seam module error. Full repository lint remains non-green. Scoped whitespace check passed.
