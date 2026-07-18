# Sharp reflected-fibre and aggregate Abel selection

- **ID:** `sharp-reflected-fibre-aggregate-abel-selection`
- **Stage:** 3-formalized result, retained here only as the completed strengthening log
- **Type:** MASTER THEOREM STRENGTHENING / COLLISION CLASSIFICATION / SOURCE QUOTIENT
- **Scientific status:** `[LEAN-PROVED] [NOVELTY UNVERIFIED] [NOT AN RH PROOF]`
- **Consolidated card:**
  [scale-covariant-bernstein-abel-tomography.md](../3-formalized/scale-covariant-bernstein-abel-tomography.md)

## Completed positive theorem

The scale-covariant Bernstein--Abel selector is intrinsic to the nonzero aggregate support of an
arbitrarily indexed absolutely summable atomic source. Its quadratic half-order law and
square-root Abel boundary hold at the sharp uniform scale threshold

```text
R > M,
```

where `M` bounds the raw source radius. No raw injectivity or pointwise nonvanishing assumption
is required.

## Complete reflected-fibre law

For distinct nonreal equal-amplitude nodes `u,v`, equal Bernstein ellipse phase forces

```text
v = 1 - conj(u).
```

On this sole nontrivial fibre the Hermitian cross row is exactly

```text
cross_n(u, 1-conj(u)) = choose(2n,n) * (u(1-u))^n.
```

Consequently

```text
|cross_n| <= (4|u||1-u|)^n,

(|u|+|1-u|)^2 - 4|u||1-u|
  = (|u|-|1-u|)^2 > 0.
```

The last inequality is strict because equality of the two focal distances would fix `u` under
reflected complementation. Different phase fibres have the pre-existing compact mixed-mode gap.
Thus every pair of distinct maximal nodes has one uniform exponential quadratic cross gap.

The scale threshold is sharp for the stated source class. If `R>M`, every normalized node lies in
the open unit disk, so a superunit maximal-amplitude node is nonreal and the classification
applies. If `R<M`, the allowed positive real node `z=M` has amplitude `2M/R-1>1`, so transverse
selection cannot be inferred uniformly from amplitude alone. Equality `R=M` is the boundary at
which the normalized endpoint `u=1` enters.

## Intrinsic aggregate source

For a raw source `(c_i,z_i)`, define

```text
cHat(u) = sum_{i : z_i=u} c_i,
J = {u : C | cHat(u) != 0}.
```

Fibrewise absolute convergence gives

```text
sum_u |cHat(u)| <= sum_i |c_i|,
sum_i c_i z_i^n = sum_{u in J} cHat(u) u^n.
```

Every occupied aggregate fibre contains a raw representative. Hence boundedness, cofinite
convergence to zero, and the nonnegative orientation of real nodes descend to `J`. The node map
`J -> C` is injective and every aggregate coefficient is nonzero by construction. A positive
zeroth moment forces `J` to be nonempty. Applying the master theorem to this canonical source
removes all raw indexing conditions.

## Additional completed laws

The same theorem batch supplies:

1. the exact finite-scale identity
   ```text
   R (B(R)^2 - 1) = 2 D(R) + D(R)^2 / R;
   ```
2. the quantitative collar
   ```text
   0 <= R(B(R)^2-1)-2 Delta
      <= M^2/(R-M) + 4M^2/R;
   ```
3. the exact Abel transport
   ```text
   R(1-A(R))
     = (2D(R)+D(R)^2/R)/(1+D(R)/R)^2;
   ```
4. the universal reciprocal-square transverse-charge law
   ```text
   defect(-w^(-2)) = 2(Re w)^2 / |w|^4;
   ```
5. the unconditional Xi envelope bound
   ```text
   0 <= Delta_Xi <= 2/1681,
   0 <= 2 Delta_Xi <= 4/1681.
   ```

The Xi interval uses only the open critical strip and the independently established
source-derived height inequality `(Im rho)^2 > 41/2`. It is an estimate on the selected
transverse invariant, but it does not force its vanishing.

## Formal theorem ledger

- `RHTower/BernsteinEllipseReflectedFiberGap.lean`
  - `reflectedBernsteinCrossMoment_one_sub_conj`
  - `exists_reflectedBernsteinCrossMoment_gap_of_distinct_equalAmplitude`
- `RHTower/ScaleCovariantBernsteinAggregateSource.lean`
  - `atomicPowerMoment_eq_atomicAggregatePowerMoment`
  - `scaleCovariantBernsteinAbel_tomography_of_aggregate`
- `HTGeometry/ConfocalAbelQuantitativeStability.lean`
  - `mul_confocalAmplitudeEnvelope_sq_sub_one_error_bounds`
  - `mul_one_sub_confocalAbelRadius_eq`
- `HTGeometry/ReciprocalSquareTransverseDefectLaw.lean`
  - `transverseDefect_reflectedReciprocalSquare`
  - `transverseDefectEnvelope_reflectedReciprocalSquare_le`
- `RHTower/ScaleCovariantXiTransverseDefectBound.lean`
  - `xiScaleCovariantTransverseDefect_mem_explicitInterval`
  - `two_mul_xiScaleCovariantTransverseDefect_mem_explicitInterval`
- `RHTower/ScaleCovariantBernsteinAbelTomography.lean`
  - `scaleCovariantBernsteinAbel_tomography`

All new theorem leaves named above were checked directly. The master source was also checked
directly after its quantitative fields were added. A later broad cache build was deliberately
abandoned because an unrelated concurrently edited module failed; it is not evidence against
these leaf checks and will not be repeated as part of this paper pass.

## Remaining open core

```text
Delta_Xi = 0.
```

The theorem now controls the carrier quantitatively and identifies its exact radical. It does not
produce the arithmetic vanishing required for RH.

## Log

- 2026-07-18 — Complete reflected collision theorem proved and formalized.
- 2026-07-18 — Canonical nonzero aggregate source and raw-source wrapper proved and formalized.
- 2026-07-18 — Quantitative confocal/Abel stability identities proved and formalized.
- 2026-07-18 — Universal reciprocal-square charge law and unconditional Xi envelope bound proved
  and formalized.
