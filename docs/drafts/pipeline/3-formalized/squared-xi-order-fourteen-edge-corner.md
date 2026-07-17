# Squared-Xi order fourteen reduces to a compact edge corner

- **ID:** squared-xi-order-fourteen-edge-corner
- **Stage:** 3-formalized
- **Type:** THEOREM / RH-disproof route discriminator
- **Scientific status:** `[PROVED HERE] [LEAN-FORMALIZED] [SOURCE SIGN CLOSED POSITIVELY]`
- **Depends on:** `XiEndpointOffLineQuartetHeightGap.lean`; `squared-xi-order-fourteen-compact-witness-window.md`
- **Statement:** At every absolute-Euler squared coordinate `y > 1/4`, failure of the elementary order-fifteen sector certificate can only come from an off-critical zero in the compact edge corner

  ```text
  1/5 < (Re rho - 1/2)^2 < 1/4,
  85 < (Im rho)^2 < 100.
  ```

## Exact reduction

For a Xi zero `rho = beta + i*gamma`, set

```text
u = (beta - 1/2)^2,
v = gamma^2,
A = v - u + y,
B = 2*(beta - 1/2)*gamma.
```

The open critical strip gives `u < 1/4`.  If the zero is off the critical line, the formal
four-copy endpoint budget gives `85 < v`.  Since `y > 1/4`, one also has `A > v > 0`.

The rational sector certificate is

```text
100*B^2 < A^2.                                           (1)
```

When `(1)` holds, `|B|/A < 1/10`.  Thus, for
`mu = 1/(A-i*B)`,

```text
15*|arg mu| < 3/2 < pi/2,
```

and hence `Re(mu^15) > 0`.  Therefore an order-fourteen negative atom must fail `(1)`.

### Central part is protected

Assume `u <= 1/5`.  Then

```text
B^2 = 4*u*v <= (4/5)*v,
A > v - 1/5 + 1/4 = v + 1/20.
```

Because `v > 85 > 80`,

```text
100*B^2 <= 80*v < v^2 < (v+1/20)^2 < A^2.
```

Thus `(1)` holds.  Failure of `(1)` forces `u > 1/5`.

### High part is protected

Assume `100 <= v`.  Since `u < 1/4` and `y > 1/4`,

```text
100*B^2 = 400*u*v < 100*v <= v^2 < A^2.
```

Thus `(1)` also holds.  Failure of `(1)` forces `v < 100`.

Combining these implications with the strict-strip and endpoint bounds gives exactly the stated
compact edge corner.

## Lean theorem surface

`XiOrderFourteenEdgeCorner.lean` proves the complete unconditional chain:

```text
orderFifteenReciprocalPower_re_pos_of_sectorRatio
xiOrderFifteenSectorRatio_of_offLine_inner
xiOrderFifteenSectorRatio_of_hundred_le_im_sq
xiOrderFifteenSectorFailure_mem_edgeCorner
xiOrderFifteenReciprocalPower_nonpos_mem_edgeCorner
```

The last theorem states the actual nonpositive reciprocal-power implication, not merely its
rational proxy.

## Source closure

`squared-xi-order-fourteen-corner-source-exclusion.md` proves from the completed theta source that
the displayed corner is empty.  Consequently the order-fifteen reciprocal-power atom is strictly
positive for every Xi multiplicity copy and every `y>1/4`.  Order fourteen cannot produce the
required RH-false source sign.

## Anti-theatre gate

This theorem does not prove a negative source value.  The completed follow-up closes its compact
corner positively, so this fixed order is a route kill rather than an RH disproof.

## Gates

- [x] No numerical zero data or computation used.
- [x] Exact endpoint height theorem already Lean-formalized.
- [x] Rational corner reduction proved on paper.
- [x] Rational corner reduction Lean-formalized.
- [x] Order-fifteen complex-sector implication Lean-formalized.
- [x] Corner zero-freeness proved from the completed source and Lean-formalized.
