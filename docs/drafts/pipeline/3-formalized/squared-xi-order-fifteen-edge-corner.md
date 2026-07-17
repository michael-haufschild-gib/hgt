# Squared-Xi order fifteen reduces to a compact edge corner

- **ID:** `squared-xi-order-fifteen-edge-corner`
- **Stage:** 3-formalized
- **Type:** THEOREM / RH-disproof route discriminator
- **Scientific status:** `[LEAN-VERIFIED] [UNCONDITIONAL] [NOT AN RH DISPROOF]`
- **Depends on:** `squared-xi-order-fourteen-corner-source-exclusion.md`

## Statement

At every absolute-Euler squared coordinate `y > 1/4`, failure of the order-sixteen sector
certificate can only come from an off-critical Xi zero in the compact edge corner

```text
1/5 < (Re rho - 1/2)^2 < 1/4,
85 < (Im rho)^2 < 104.
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
104*B^2 < A^2.                                           (1)
```

From `(1)` one obtains `|B|/A < 981/10000`.  Hence for `mu=1/(A-iB)`,

```text
16*|arg mu| < 16*981/10000 < pi/2,
```

and therefore `Re(mu^16)>0`.

If `u<=1/5`, then `104*B^2 <= (416/5)*v < v^2 < A^2`, using the unconditional off-line height
floor `v>85`.  If `v>=104`, then `104*B^2<104*v<=v^2<A^2`.  Thus failure of `(1)` forces exactly
the displayed corner.

## Lean theorem surface

`XiOrderFifteenEdgeCorner.lean` proves:

```text
orderSixteenReciprocalPower_re_pos_of_sectorRatio
xiOrderSixteenSectorRatio_of_offLine_inner
xiOrderSixteenSectorRatio_of_oneHundredFour_le_im_sq
xiOrderSixteenSectorFailure_mem_edgeCorner
xiOrderSixteenReciprocalPower_nonpos_mem_edgeCorner
```

## Anti-theatre gate

This reduction is useful only because the completed source independently excludes its compact
corner.  By itself it is not a negative source value and is not evidence that RH is false.

## Gates

- [x] Exact rational sector implication proved in Lean.
- [x] Central and high regions protected in Lean.
- [x] Nonpositive reciprocal-power atom reduced to the compact corner in Lean.
- [x] No zero table, zero computation, or RH assumption used.

## Formalization

- `formal/GaloisForLFunctions/RHTower/XiOrderFifteenEdgeCorner.lean`
