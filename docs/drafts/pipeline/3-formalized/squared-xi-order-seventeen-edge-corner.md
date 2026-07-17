# Squared-Xi order seventeen reduces to a compact edge corner

- **ID:** `squared-xi-order-seventeen-edge-corner`
- **Stage:** 3-formalized
- **Type:** THEOREM / RH-disproof route discriminator
- **Scientific status:** `[LEAN-VERIFIED] [UNCONDITIONAL] [NOT AN RH DISPROOF]`
- **Depends on:** `squared-xi-order-sixteen-corner-source-exclusion.md`

## Statement

At every absolute-Euler squared coordinate `y > 1/4`, failure of the order-eighteen sector
certificate can only come from an off-critical Xi zero in the compact edge corner

```text
4/25 < (Re rho - 1/2)^2 < 1/4,
85 < (Im rho)^2 < 132.
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
132*B^2 < A^2.                                           (1)
```

From `(1)` one obtains `|B|/A < 872/10000`. Hence for `mu=1/(A-iB)`,

```text
18*|arg mu| < 18*872/10000 < pi/2,
```

and therefore `Re(mu^18)>0`.

If `u<=4/25`, then `132*B^2 <= (2112/25)*v < v^2 < A^2`, using the unconditional
off-line height floor `v>85`. If `v>=132`, then `132*B^2<132*v<=v^2<A^2`. Thus failure of
`(1)` forces exactly the displayed corner.

## Lean theorem surface

`XiOrderSeventeenEdgeCorner.lean` proves:

```text
orderEighteenReciprocalPower_re_pos_of_sectorRatio
xiOrderEighteenSectorRatio_of_offLine_inner
xiOrderEighteenSectorRatio_of_oneHundredThirtyTwo_le_im_sq
xiOrderEighteenSectorFailure_mem_edgeCorner
xiOrderEighteenReciprocalPower_nonpos_mem_edgeCorner
```

## Anti-theatre gate

This reduction matters only because an independent completed-source trace bound excludes the
remaining corner. It is not a negative source value and is not evidence that RH is false.

## Gates

- [x] Exact rational sector implication proved in Lean.
- [x] Central and high regions protected in Lean.
- [x] Nonpositive reciprocal-power atom reduced to the compact corner in Lean.
- [x] No zero table, zero computation, or RH assumption used.

## Formalization

- `formal/GaloisForLFunctions/RHTower/XiOrderSeventeenEdgeCorner.lean`
