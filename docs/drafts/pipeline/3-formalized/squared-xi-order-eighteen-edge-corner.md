# Squared-Xi order eighteen reduces to a compact edge corner

- **ID:** `squared-xi-order-eighteen-edge-corner`
- **Stage:** 3-formalized
- **Type:** THEOREM / RH-disproof route discriminator
- **Scientific status:** `[LEAN-VERIFIED] [UNCONDITIONAL] [NOT AN RH DISPROOF]`
- **Depends on:** `squared-xi-order-seventeen-corner-source-exclusion.md`

## Statement

At every absolute-Euler squared coordinate `y > 1/4`, failure of the order-nineteen sector
certificate can only come from an off-critical Xi zero in the compact edge corner

```text
7/50 < (Re rho - 1/2)^2 < 1/4,
85 < (Im rho)^2 < 147.
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
147*B^2 < A^2.                                           (1)
```

From `(1)` one obtains `|B|/A < 826/10000`. Hence for `mu=1/(A-iB)`,

```text
19*|arg mu| < 19*826/10000 < pi/2,
```

and therefore `Re(mu^19)>0`.

If `u<=7/50`, then `147*B^2 <= (2058/25)*v < v^2 < A^2`, using the unconditional
off-line height floor `v>85`. If `v>=147`, then `147*B^2<147*v<=v^2<A^2`. Thus failure of
`(1)` forces exactly the displayed corner.

## Lean theorem surface

`XiOrderEighteenEdgeCorner.lean` proves:

```text
orderNineteenReciprocalPower_re_pos_of_sectorRatio
xiOrderNineteenSectorRatio_of_offLine_inner
xiOrderNineteenSectorRatio_of_oneHundredFortySeven_le_im_sq
xiOrderNineteenSectorFailure_mem_edgeCorner
xiOrderNineteenReciprocalPower_nonpos_mem_edgeCorner
```

## Anti-theatre gate

This reduction matters only because the completed source independently excludes the residual
corner. It is not a negative source value and is not evidence that RH is false.

## Gates

- [x] Exact rational sector implication proved in Lean.
- [x] Central and high regions protected in Lean.
- [x] Nonpositive reciprocal-power atom reduced to the compact corner in Lean.
- [x] No zero table, zero computation, or RH assumption used.

## Formalization

- `formal/GaloisForLFunctions/RHTower/XiOrderEighteenEdgeCorner.lean`
