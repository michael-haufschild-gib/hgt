# Three-point correlation-angle subadditivity

- **ID:** `three-point-correlation-angle-subadditivity`
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Date:** 2026-07-23
- **Scientific status:** `[KNOWN] [CASTANO-PAKSOY-ZHANG] [NO COMPUTATION]`
- **Statement:** A nonnegative radially ordered three-point correlation packet is positive
  semidefinite whenever its long-gap arccos angle is at most the sum of its adjacent angles.

## Exact statement

For `0<=p<1`, `0<=q<=1`, `0<=r`, `r<=p`, and `r<=q`, assume

```text
arccos(r) <= arccos(p)+arccos(q).                     (A)
```

Then

```text
threePointCorrelationMatrix(1,p,q,r) is PSD.          (P)
```

## Gates

- [x] 0 → 1 in-progress: exact RHTower consumer and corpus audit
- [x] 1 → 2 fully-proven: dependency-complete trigonometric proof
- [x] 2 → 3 formalized: exact HilbertMetric theorem, HTGeometry mixture consumer, RHTower wall
  discharge connector, umbrella wiring, axiom audit, and lint green

## Proof

Put `alpha=arccos(p)`, `beta=arccos(q)`, and `gamma=arccos(r)`. All lie in `[0,pi/2]`.
Radial ordering gives `alpha<=gamma` and `beta<=gamma`, hence the two triangle inequalities not
displayed in `(A)`. Therefore

```text
|alpha-beta| <= gamma <= alpha+beta.
```

Cosine is decreasing on `[0,pi]`, so

```text
cos(alpha+beta) <= r <= cos(alpha-beta).
```

The addition formulas give

```text
-sin(alpha)sin(beta) <= r-pq <= sin(alpha)sin(beta).
```

Squaring and using `sin(alpha)^2=1-p^2`, `sin(beta)^2=1-q^2` yields

```text
(r-pq)^2 <= (1-p^2)(1-q^2).
```

The right-minus-left side is exactly

```text
1+2pqr-p^2-q^2-r^2,
```

the normalized three-point determinant. Existing HilbertMetric `LDL*` criterion then gives `(P)`.

## Boundary

This is the order-three correlation-angle criterion of Castano--Paksoy--Zhang
(arXiv:1407.2800), specialized to the strict first-adjacent correlation chamber already proved
for the theta center-mixed density. It is a missing formal connector, not a novelty claim.

## Lean realization

`HilbertMetric/ThreePointCorrelationAngle.lean` proves the normalized criterion.
`RHTower/HedenmalmCenterMixedCorrelationAngle.lean` then:

- applies it to every reflected completed-source fibre;
- uses `HTGeometry.integralMatrixKernel_posSemidef` to pass fibre positivity through Hedenmalm's
  positive center mixture;
- proves
  `thetaCuspCenterMixedNearCenterThreePointWall_of_sourceAngle_subadditive`, the direct source-angle
  discharge of the named proposition interface.

Both modules are wired into their respective umbrellas.
