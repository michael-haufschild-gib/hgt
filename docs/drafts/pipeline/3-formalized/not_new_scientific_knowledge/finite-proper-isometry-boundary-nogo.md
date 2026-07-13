# Finite proper-isometry boundary no-go

- **ID:** `finite-proper-isometry-boundary-nogo`
- **Stage:** 3-formalized / not-new
- **Type:** THEOREM (paper + Lean), `[PROVED]`, `[BRIDGE]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/FiniteIsometryBoundaryNoGo.lean`
- **Route:** `../../1-in-progress/dyadic-weld-weyl-multiplicity-route.md`

## Theorem

For every finite square complex matrix `U`,

```text
U* U = I  implies  U U* = I
```

and `det U != 0`.  Hence no finite matrix is a proper unilateral isometry:

```text
not (U* U = I and U U* != I).
```

## Proof

Finite matrix rings over `C` are stably finite, so a left inverse is a right inverse.  Equivalently,
taking determinants in `U*U=I` makes `|det U|^2=1`, hence `U` is invertible and its adjoint is its
two-sided inverse.

## Positive statement from the Bost--Connes/Toeplitz no-go

The `2`-isometry in Bost--Connes and the unilateral Toeplitz shift carry a genuine range-projection
boundary defect only because their carrier is infinite-dimensional.  That proper-isometry defect
cannot descend unchanged to an actual finite SEM hole space.

The positive finite replacement is not another isometry theorem.  It is a cyclic boundary closure:

> replace the missing range by one source-derived top-to-bottom arrow, then prove that its holonomy
> preserves the dyadic Weyl phase.

This returns exactly to the scalar anomaly `h(1-zeta_k^d)`.  A unitary dilation on a larger Hilbert
space is external enlargement and does not constrain `d`.

## Formal surface

- `finiteMatrix_isometry_is_unitary`
- `finiteMatrix_isometry_det_ne_zero`
- `no_finiteMatrix_proper_isometry`

## Verification

`lake env lean GaloisForLFunctions/RHTower/FiniteIsometryBoundaryNoGo.lean` passes on the repository
toolchain.

## Novelty and significance gate

This is standard finite linear algebra.  No claim of new scientific knowledge is made.  It closes
the direct proper-isometry descent and identifies cyclic source closure as the only finite successor.

## Gates

- [x] 0 -> 1: proper-isometry descent stated
- [x] 1 -> 2: finite isometry/unitary equivalence proved
- [x] 2 -> 3: formalized and checked
- [ ] 3 -> 4: not promoted; source cyclic closure remains open
