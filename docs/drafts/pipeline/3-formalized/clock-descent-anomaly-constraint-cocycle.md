# The clock-descent anomaly is a constraint-algebra cocycle

- **ID:** `clock-descent-anomaly-constraint-cocycle`
- **Stage:** 3-formalized
- **Type:** GENERAL HT COMPARISON LAW / AFFINE COLLIGATION SKELETON
- **Scientific status:** `[LEAN-FORMALIZED] [BRIDGE] [SOURCE-ALGEBRA LAW]`
- **Parent:** `../1-in-progress/source-anomaly-boundary-colligation-field.md`
- **Statement:** Composition of source operations and proposed clock shadows makes the descent
  anomaly into the off-diagonal cocycle of an upper-triangular comparison representation.

## The theorem

For source operations `S,T`, shadows `A,B`, and observation `q`, define

```text
alpha(S,A)=A q-q S.                                       (1)
```

Then

```text
alpha(S T,A B)=A alpha(T,B)+alpha(S,A)T.                  (2)
```

Consequently the augmented comparison matrices

```text
C(S,A)=[ A  alpha(S,A)
          0      S      ]                                 (3)
```

obey

```text
C(S,A) C(T,B)=C(S T,A B).                                 (4)
```

Thus the anomaly is not a list of unrelated finite errors. It is the extension cocycle coupling
the source algebra to its observable shadows.

## Lean declaration

`GaloisForLFunctions.HTGeometry.ClockDescentAnomaly` contains
`clockDescentAnomaly_comp_constraint`.

The existing object cache was reused and the touched source passed direct Lean verification. No
build was run.

## Scientific boundary and positive role

Equation `(2)` is elementary block-matrix algebra and is not new by itself. Its nontrivial positive
role is to rule out arbitrary assembly of obstruction data: every proposed source field must carry
one simultaneous constraint-algebra cocycle, and every claimed realization must preserve it. This
is strictly stronger than matching curvature rank, a scalar spectrum, or a determinant.

The candidate-new theorem must combine `(2)` with maximal finite anomaly range, uniformly thin
inter-resolution variation, source-topological completion, and comparison across genuinely
different analytic realization categories.

## Gates

- [x] constraint-algebra cocycle formalized
- [x] axiom-clean direct Lean verification
- [ ] augmented representation packaged as a reusable structure
- [ ] source-canonical completion constructed
- [ ] cross-realization preservation theorem proved
