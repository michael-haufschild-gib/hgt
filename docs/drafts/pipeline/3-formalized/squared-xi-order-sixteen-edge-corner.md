# Squared-Xi order sixteen reduces to a compact edge corner

- **ID:** `squared-xi-order-sixteen-edge-corner`
- **Stage:** 3-formalized
- **Type:** THEOREM / RH-disproof route discriminator
- **Scientific status:** `[LEAN-VERIFIED] [UNCONDITIONAL] [NOT AN RH DISPROOF]`
- **Depends on:** `squared-xi-order-fourteen-corner-source-exclusion.md`

## Statement

At every absolute-Euler squared coordinate `y > 1/4`, failure of the order-seventeen sector
certificate can only come from an off-critical Xi zero in the compact edge corner

```text
9/50 < (Re rho - 1/2)^2 < 1/4,
85 < (Im rho)^2 < 118.
```

## Exact reduction

For centered squared coordinates

```text
u = (Re rho - 1/2)^2,
v = (Im rho)^2,
A = v - u + y,
B = 2*(Re rho - 1/2)*(Im rho),
```

the rational sector certificate is

```text
118*B^2 < A^2.                                           (1)
```

From `(1)` one obtains `|B|/A < 923/10000`. Hence for `mu=1/(A-iB)`,

```text
17*|arg mu| < 17*923/10000 < pi/2,
```

and therefore `Re(mu^17)>0`.

If `u<=9/50`, then `118*B^2 <= (2124/25)*v < v^2 < A^2`, using the unconditional
off-line height floor `v>85`. If `v>=118`, then `118*B^2<118*v<=v^2<A^2`. Thus failure of
`(1)` forces exactly the displayed corner.

The former `u<=1/5` split cannot be reused: coefficient `118` would require
`(472/5)*v<v^2`, which does not follow from `v>85`. The smaller protected band is therefore
mathematically necessary, not a proof artifact.

## Lean theorem surface

`XiOrderSixteenEdgeCorner.lean` proves:

```text
orderSeventeenReciprocalPower_re_pos_of_sectorRatio
xiOrderSeventeenSectorRatio_of_offLine_inner
xiOrderSeventeenSectorRatio_of_oneHundredEighteen_le_im_sq
xiOrderSeventeenSectorFailure_mem_edgeCorner
xiOrderSeventeenReciprocalPower_nonpos_mem_edgeCorner
```

## Anti-theatre gate

This reduction is useful only because the completed source independently excludes its compact
corner. By itself it is not a negative source value and is not evidence that RH is false.

## Gates

- [x] Exact rational sector implication proved in Lean.
- [x] Corrected central and high regions protected in Lean.
- [x] Nonpositive reciprocal-power atom reduced to the compact corner in Lean.
- [x] No zero table, zero computation, or RH assumption used.

## Formalization

- `formal/GaloisForLFunctions/RHTower/XiOrderSixteenEdgeCorner.lean`
