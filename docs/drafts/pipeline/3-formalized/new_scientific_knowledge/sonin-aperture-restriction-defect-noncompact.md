# Noncompact Sonin aperture-restriction defect

- **ID:** `sonin-aperture-restriction-defect-noncompact`
- **Stage:** 3-formalized
- **Type:** THEOREM / FRONTIER NO-GO WITH POSITIVE SURVIVOR
- **Scientific status:** `[FORMALIZED] [CORPUS-NEW] [NOVELTY PROVISIONAL] [NOT RH]`
- **Paper source:**
  `sonin/sonin-aperture-area-rigidity-and-restriction-defect.md`
- **Lean endpoint:**
  `formal/GaloisForLFunctions/RHTower/SoninApertureRestrictionDefect.lean`

## Result

For nested apertures `a<=b`, the exact even Sonin projections satisfy

```text
Q_b Q_a=Q_a Q_b=Q_b.
```

For `D_r=U_r+U_r^*`,

```text
G_a(p,q)=Q_aD_p(1-Q_a)D_qQ_a,
X_(a,b,r)=(Q_a-Q_b)D_rQ_b,
```

the restriction defect is exact:

```text
G_b(p,q)-Q_bG_a(p,q)Q_b
  =Q_bD_p(Q_a-Q_b)D_qQ_b,

G_b(r,r)-Q_bG_a(r,r)Q_b=X_(a,b,r)^*X_(a,b,r).
```

If `0<a<b<r a`, then for every compact `K`,

```text
1<=||X_(a,b,r)-K||.
```

Consequently both `X_(a,b,r)` and the positive restriction defect `X^*X` are noncompact. Since
the project relative ideal is Schatten-1, aperture restriction cannot be implemented inside that
relative ideal.

## Frontier effect

Fixed-aperture principal-relative splitting remains valid. Further exact-relative analysis shows
the positive defect class is the canonical scale-one shell `S(ra,rb)`, already represented by a
live state at aperture `b`. Canonical state multiplication closes modulo the same exact relative
ideal, and the shell reader gives `log(b)-log(a)`. Remaining RH chain is

```text
Connes finite prime--Gamma source
  -> fixed-aperture principal-relative finite part
  -> noncompact positive aperture defect
  -> canonical additive principal shell cocycle [CLOSED]
  -> trace-class aperture curvature
  -> [OPEN] exact Burnol scalar cancellation and completed finite lower floor
  -> RH.
```

This is a falsification result with a positive survivor, not an RH proof. It removes the previous
trace-class compatibility target as mathematically impossible.

## Formal endpoints

- `centralSoninCarrier_antitone`
- `evenCentralSoninProjection_mul_of_le`
- `evenCentralSoninQuadraticCorner_restrictionDefect`
- `evenCentralSoninQuadraticCorner_restrictionDefect_eq_adjoint_mul`
- `evenSoninApertureLostTransition_pairedShell_tendsto`
- `one_le_norm_evenSoninApertureLostTransition_sub_compact`
- `evenSoninApertureLostTransition_not_isCompactOperator`
- `evenCentralSoninQuadraticCorner_restrictionDefect_not_isCompactOperator`
- `evenCentralSoninQuadraticCorner_restrictionDefect_principalRelativeEq_shell`
- `soninWindowState_operator_mul_principalRelativeEq`
- `soninLiveWindowCyclicLogWeight_apertureLostLayer`
- `evenSoninApertureRestrictionDefect_compressed_cocycle`
- `evenSoninApertureRestrictionDefect_principalRelative_cocycle`
- `evenSoninApertureRestrictionCurvature_memSchattenClass_one`
- `soninApertureTotalLayerWindow_operator_eq_retained_add_lost`
- `soninAperture_cyclicMass_conservation`

Module is imported by `RHTower.lean`. Direct `lake env lean` check passes. Final module build,
axiom print, and lint are pending final audit.

## Priority audit

Targeted primary-source search checked Connes--Consani's quasi-inner/Sonin carrier construction,
Connes--Moscovici's prolate/Sonin operator, and Connes--Consani--Moscovici's semilocal prolate wave
operators. Those sources establish adjacent scaling, carrier, and semilocal stability results; no
exact nested-aperture Gram factorization or compact-distance obstruction matching this theorem was
found. This supports only provisional novelty, not a priority claim.

## Gates

- [x] prior project aperture, mixed-shell, Calkin, and failed-route corpus audited
- [x] exact nested projection law
- [x] positive restriction-defect factorization
- [x] shell certificate and sharp compact-distance lower bound
- [x] positive defect proved noncompact
- [x] exact relative shell normal form and canonical state-algebra closure
- [x] scale-free logarithmic aperture character
- [x] exact compressed cocycle and trace-class curvature reduction
- [x] imported by `RHTower.lean`
- [ ] final cached module build
- [ ] axiom audit and formal lint
- [ ] independent specialist priority audit
