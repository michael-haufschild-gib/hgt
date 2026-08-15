# Real-Axis Kernel Positivity Is Not A Selector

- **ID:** real-axis-kernel-positivity-nonselector
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / proof-route guardrail
- **Formalized companion:** `real-axis-kernel-positivity-nonselector-formalized.md`
- **Source:** `docs/consolidated/revision01/bridge-theorem.md`;
  `seam-log-markov-pick-rh-equivalence.md`;
  `rank-one-scalar-shadow-needs-kernel-exhaustion.md`
- **Statement:** Positivity of the scalar reproducing-kernel function
  `K(y)=e(y)^*H^{-1}e(y)` on the real moment curve does not imply positivity of
  the underlying Hermitian form `H`. Negative directions can live off the
  evaluation curve.

## Setup

Let `V=R[y]_{<=2}` and write

`e(t)=(1,t,t^2)^T`.

For an invertible real symmetric matrix `H`, the scalar kernel visible on the
real evaluation curve is

`K_H(t)=e(t)^T H^{-1} e(t)`.

In the boundary-Weyl/Christoffel language this is a real-axis scalar shadow of
the inverse form. It is not the same datum as positivity of `H`.

## Theorem

There exists an invertible real symmetric form `H` with negative index `2` such
that

`K_H(t)>0`

for every real `t`.

## Proof

Define

```text
G =
[ 1   0   2 ]
[ 0  -3   0 ]
[ 2   0   1 ].
```

The matrix `G` is invertible. Its `span(e_0,e_2)` block has eigenvalues `3` and
`-1`, and the middle entry is `-3`. Hence `G` has inertia `(1,2)`.

Let

`H=G^{-1}`.

Then `H` has the same inertia `(1,2)`, so `H` is indefinite.

However, along the real evaluation curve,

```text
K_H(t) = e(t)^T H^{-1} e(t)
       = e(t)^T G e(t)
       = 1 + t^2 + t^4.
```

Since `1+t^2+t^4>0` for every real `t`, the scalar kernel is positive on the
entire real axis although the underlying form has two negative squares.

This proves the claim.

## Consequence For The RH Route

The boundary-Weyl and Christoffel coordinates are useful only when their scalar
kernel is tied to the full moment form or to a complete Pick/Nevanlinna
condition. A check such as

`K(y,y)>0 for every real y`

does not certify

`H>=0`.

For the reciprocal-seam route, the faithful target remains the full square-test
cone

`Q_0[p]>=0 for every real polynomial p`,

or the equivalent source-built Markov/Stieltjes theorem. Real-axis kernel
positivity can miss polynomial directions that are not point evaluations.

## Source Boundary

This theorem is finite-dimensional linear algebra. It proves no statement about
zeta and no zero localization. Its role is to block a scalar-shadow route:
testing a reproducing kernel only on the real moment curve is weaker than
testing the full form.

## Gates

- [x] 0 -> 1 in-progress: real-axis scalar-kernel shortcut isolated.
- [x] 1 -> 2 fully-proven: explicit indefinite matrix with positive real-axis
  kernel written.
- [x] 2 -> 3 formalized: `GaloisForLFunctions.HTGeometry`
  `RealAxisKernelPositivityNonselector.lean` gives the displayed inverse pair,
  real Hermitian symmetry, exact inertia `2`, exact scalar polynomial
  `1+t^2+t^4`, its strict real-axis positivity, and an explicit negative
  off-curve direction. Direct source and targeted leaf build pass; the axiom
  audit contains only `propext`, `Classical.choice`, and `Quot.sound`.

## Log

- 2026-06-24 -- Codex: created under the private RH continuation after reading
  the bridge-theorem caveat that real-axis Christoffel positivity can survive an
  off-curve defect. The card gives an exact finite model of that failure.

- 2026-08-15 -- Lean certificate completed in
  `formal/GaloisForLFunctions/HTGeometry/RealAxisKernelPositivityNonselector.lean`.
  It retains the literal three-by-three inverse form and the full real moment
  curve, rather than weakening the counterexample to a sampled kernel test.
