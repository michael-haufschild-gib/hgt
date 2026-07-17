# Geometric CDD contractive boundary selection

- **ID:** `geometric-cdd-boundary-selection`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / SCALE-CONSTRAINT UNIQUENESS CORE
- **Scientific status:** `[PROVED] [FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lean:** `formal/GaloisForLFunctions/HTGeometry/GeometricCDDBoundarySelection.lean`
- **Parent:** `../../1-in-progress/hypertranscendental-scattering-elliptic-uv-boundary.md`
- **Statement:** The infinite one-sided CDD delay converges, obeys its exact one-shell constraint,
  and is the unique continuous solution with zero value at the contracting endpoint.

## Exact theorem

Lean defines the finite logarithmic-energy CDD delay

```text
T_(q,N)(x) = 4 sum_(k=0)^(N-1) q^k x/(1+q^(2k)x^2)        (1)
```

and proves the exact finite shell constraint

```text
T_(q,N+1)(x) = 4x/(1+x^2) + T_(q,N)(qx).                  (2)
```

Every nonempty finite delay is strictly positive when `q>0` and `x>0`.

For `|q|<1`, Lean constructs the infinite delay

```text
T_q(x) = sum_(k>=0) 4 q^k x/(1+q^(2k)x^2)                 (3)
```

as an absolutely summable series.  The formal estimate

```text
|T_q(x)| <= 4 |x|/(1-|q|)                                 (4)
```

proves continuity and `T_q(0)=0`.  Reindexing the convergent series proves

```text
T_q(x)=4x/(1+x^2)+T_q(qx).                                (5)
```

For `0<=q<1`, suppose a continuous defect satisfies

```text
Y(x)=Y(qx),       Y(0)=0.                                  (6)
```

Iteration gives `Y(x)=Y(q^n x)`, while `q^n x -> 0`.  Continuity at the endpoint therefore forces
`Y(x)=0` for every real `x`.  Subtracting two affine solutions yields `(6)`, so Lean proves:

```text
F(x)=B(x)+F(qx),   G(x)=B(x)+G(qx),
F and G continuous at 0,   F(0)=G(0)
  => F=G.                                                   (7)
```

Taking `B(x)=4x/(1+x^2)` and `G=T_q` proves that `(3)` is the unique continuous response satisfying
`(5)` and the zero infrared boundary condition.  This is the formal mechanism distinguishing the
physical one-sided solution from unrestricted bilateral scale-invariant additions.

## Exact boundary

The module proves the real infinite sum, its geometric majorant, endpoint continuity, exact scale
constraint, and uniqueness.  It does not prove hypertranscendence, identify the ultraviolet
Jacobi-elliptic limit, establish regular-strip bounds for the scattering product, or reconstruct a
QFT.

The result is elementary contraction plus continuity.  Its role in the research program is
structural, not a novelty claim.

## Lean surface

- `geometricCDDLogShellDelay`
- `geometricCDDLogPhaseSlope`
- `geometricCDDLogPhaseSlope_succ_constraint`
- `geometricCDDLogPhaseSlope_pos`
- `geometricCDDLogPhaseDelay`
- `summable_geometricCDDLogPhaseDelay`
- `geometricCDDLogPhaseDelay_constraint`
- `norm_geometricCDDLogPhaseDelay_le`
- `continuousAt_geometricCDDLogPhaseDelay_zero`
- `contractiveScaleInvariant_eq_zero`
- `contractiveScaleAffineBoundary_unique`
- `geometricCDDLogPhaseDelay_unique`

## Verification

- [x] direct touched-file Lean check passed
- [x] exact cached module build passed in one foreground process
- [x] axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`
- [x] no numerical computation used
- [x] imported by the HTGeometry umbrella
