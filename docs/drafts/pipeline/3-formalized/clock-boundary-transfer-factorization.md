# Forward-flat shadows have curvature only on the new boundary layer

- **ID:** `clock-boundary-transfer-factorization`
- **Stage:** 3-formalized
- **Type:** GENERAL SPLIT-CLOCK COLLIGATION / POSITIVE NO-GO
- **Scientific status:** `[LEAN-FORMALIZED] [BRIDGE] [CURVATURE-ONLY RECONSTRUCTION KILLED] [EXACT COLLIGATION RECONSTRUCTION]`
- **Parent:** `../1-in-progress/ind-flat-pro-curved-boundary-transfer.md`
- **Statement:** If finite shadows commute with forward clock extension, every backward-truncation
  curvature factors through the complementary boundary projection and vanishes on all previously
  assembled clock directions.

## The theorem

Let `i:O_0->O_1`, `p:O_1->O_0`, and `p i=1`. If

```text
T_1 i=i T_0,                                               (1)
```

then for

```text
kappa=p T_1-T_0 p                                         (2)
```

one has

```text
kappa=p T_1(1-i p),                                       (3)
kappa i=0.                                                 (4)
```

The image of `1-i p` is the newly exposed split boundary. Thus `(3)` is an exact transfer
factorization from that layer into retained observations.

Curvature also has an intrinsic split-independent descent

```text
bar_kappa:O_1/range(i)->O_0,                              (5)
bar_kappa q=kappa,                                        (6)
```

where `q` is the quotient map. A chosen complement identifies `(5)` with the boundary block in
`(3)`, but the quotient transfer itself is canonical.

## Curvature-only reconstruction no-go

Put `b=1-i p`. The higher action has the exact Lean-formalized decomposition

```text
T_1=i T_0 p+i kappa+b T_1 b.                              (7)
```

The third term is invisible to curvature. For every endomorphism `g`, replacing `T_1` by

```text
T'_1=T_1+b g b                                             (8)
```

preserves both `T'_1 i=T_1 i` and `kappa(T')=kappa(T)`. Thus lower action, forward compatibility,
and complete curvature do not reconstruct the higher action.

The positive exact replacement is the boundary colligation

```text
(T_0,kappa,delta),       delta=b T_1 b.                    (9)
```

Two forward-compatible higher actions having the same three entries in `(9)` are equal. This
colligation uniqueness is Lean-formalized.

## Lean declarations

`GaloisForLFunctions.HTGeometry.ClockDescentAnomaly` contains:

- `clockShadowCurvature_eq_boundaryTransfer`;
- `clockShadowCurvature_comp_extend_eq_zero`;
- `clockBoundaryTransferQuotient`;
- `clockBoundaryTransferQuotient_comp_mkQ`;
- `clockBoundaryProjector`;
- `clockBoundaryCompression`;
- `clockShadow_eq_boundaryColligation`;
- `clockShadowCurvature_add_boundaryCompression`;
- `add_clockBoundaryCompression_comp_extend`;
- `clockShadow_eq_of_curvature_eq_of_boundaryCompression_eq`.

The existing module cache was reused and the touched source passed direct Lean verification. No
build was run.

## Scientific boundary

The factorization is elementary split linear algebra. Its main scientific effect is a no-go:
uniform rank one is automatic when one clock slot is added per level, so rank alone cannot define a
new HT invariant.

The positive finite object is the boundary colligation: the transfer morphism
`p T_1|ker(p)` together with the boundary self-symbol `b T_1 b`. Even this is generic operator
block algebra. The proposed new theory must recover and compare the complete source-derived
colligation plus its descent anomaly, not rebrand a rank bound or a standard colligation.

## Gates

- [x] exact boundary factorization formalized
- [x] curvature zero on forward-assembled directions formalized
- [x] intrinsic quotient factorization through `O_1/range(i)` formalized
- [x] curvature-only reconstruction no-go formalized
- [x] exact boundary-colligation reconstruction formalized
- [x] colligation uniqueness formalized
- [ ] finite-rank consequence packaged
- [ ] source presentation invariance proved
