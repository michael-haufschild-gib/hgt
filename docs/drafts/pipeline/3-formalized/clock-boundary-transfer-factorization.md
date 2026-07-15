# Forward-flat shadows have curvature only on the new boundary layer

- **ID:** `clock-boundary-transfer-factorization`
- **Stage:** 3-formalized
- **Type:** GENERAL SPLIT-CLOCK FACTORIZATION / POSITIVE NO-GO
- **Scientific status:** `[LEAN-FORMALIZED] [BRIDGE] [STRUCTURAL NO-GO WITH POSITIVE TRANSFER]`
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

## Lean declarations

`GaloisForLFunctions.HTGeometry.ClockDescentAnomaly` contains:

- `clockShadowCurvature_eq_boundaryTransfer`;
- `clockShadowCurvature_comp_extend_eq_zero`;
- `clockBoundaryTransferQuotient`;
- `clockBoundaryTransferQuotient_comp_mkQ`.

The existing module cache was reused and the touched source passed direct Lean verification. No
build was run.

## Scientific boundary

The factorization is elementary split linear algebra. Its main scientific effect is a no-go:
uniform rank one is automatic when one clock slot is added per level, so rank alone cannot define a
new HT invariant.

The positive object is the boundary-transfer morphism `p T_1|ker(p)`. The proposed new theory must
recover and compare the complete source-derived sequence of these transfers, not rebrand its
generic rank bound.

## Gates

- [x] exact boundary factorization formalized
- [x] curvature zero on forward-assembled directions formalized
- [x] intrinsic quotient factorization through `O_1/range(i)` formalized
- [ ] finite-rank consequence packaged
- [ ] source presentation invariance proved
