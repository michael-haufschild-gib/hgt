# Primitive Gram interior arity equals complex rank

- **ID:** `primitive-gram-interior-arity`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper + Lean)
- **Status:** `[FULLY-LEAN-PROVED] [REDISCOVERED] [BRIDGE]`
- **Parent:**
  `primitive-pair-interior-dimension.md`
- **Statement:** In \(H_q(\mathbb C)_+\), a sum of \(k\) primitive rank-one Gram records is
  interior exactly when their root family has no common annihilator. Consequently fewer than
  \(q\) primitive records never reach the interior, while \(q\) coordinate records sum to the
  identity. The primitive interior arity is exactly \(q\).

## Exact theorem

Let \(q,k\in\mathbb N\), let
\[
u=(u_a)_{a\in\operatorname{Fin}k},
\qquad
u_a\in\mathbb C^q,
\]
and define
\[
R_u=\sum_{a\in\operatorname{Fin}k}u_a^\dagger u_a
\in H_q(\mathbb C)_+.
\tag{1}
\]
Regard each \(u_a\) as a row covector and define
\[
T_u:\mathbb C^q\longrightarrow\mathbb C^k,
\qquad
(T_ux)_a=u_a\mathbin{\boldsymbol\cdot}x.
\tag{2}
\]
Then
\[
\boxed{
R_u>0
\iff
T_u\text{ is injective}.
}
\tag{3}
\]
Therefore:

1. if \(k<q\), then \(R_u\) is never positive definite;
2. for the \(q\) coordinate roots \(e_0,\ldots,e_{q-1}\),
   \[
   \sum_{a<q}e_a^\dagger e_a=I_q>0;
   \tag{4}
   \]
3. the least number of primitive Gram records that can produce an interior point is exactly
   \(q\).

## Dependency-closed proof

For every \(x\in\mathbb C^q\),
\[
x^\dagger R_u x
=
\sum_{a<k}x^\dagger u_a^\dagger u_a x
=
\sum_{a<k}|u_a\mathbin{\boldsymbol\cdot}x|^2.
\tag{5}
\]
Every term in `(5)` is nonnegative. Hence the sum vanishes exactly when
\(u_a\boldsymbol\cdot x=0\) for every \(a\), equivalently \(T_ux=0\). Thus `(1)` is positive
definite exactly when \(\ker T_u=\{0\}\), proving `(3)`.

If \(k<q\), rank--nullity gives
\[
\dim_{\mathbb C}\ker T_u
=q-\operatorname{rank}T_u
\ge q-k>0,
\]
so \(T_u\) is not injective and `(3)` rules out positive definiteness.

For the coordinate family, direct entrywise summation gives
\[
\left(\sum_{a<q}e_a^\dagger e_a\right)_{ij}
=\sum_{a<q}\delta_{ai}\delta_{aj}
=\delta_{ij},
\]
which is `(4)`. The lower and upper bounds coincide, proving primitive interior arity \(q\).

## Novelty and physical boundary

This is standard finite-dimensional Gram/rank mathematics. The new corpus value is an exact
invariant that generalizes the already formalized pair theorem:
\[
\text{primitive interior arity of }H_q(\mathbb C)_+=q.
\]

It does not prove that physical actualization has arity two, that causalization preserves arity,
that the cone is physical spacetime, or that \(q=2\). Those are separate conjectural premises.

Relevant parent boundaries include purification theory, where mixed states have reversible
purifications unique up to transformations on the purifying system
([Chiribella--D'Ariano--Perinotti](https://arxiv.org/abs/0908.1583)), and the order-theoretic
characterization of strictly convex symmetric cones as spin factors
([Lemmens--Roelands--van Imhoff](https://arxiv.org/abs/1609.08304)).

## Gates

- [x] exact statement frozen
- [x] dependency-closed paper proof
- [x] novelty downgraded to classical bridge
- [x] physical antecedent excluded from theorem
- [x] exact theorem formalized unconditionally in Lean
- [x] direct check, axiom audit, lint, and target build

## Lean realization

Module:
`formal/GaloisForLFunctions/HTGeometry/PrimitiveInteriorArity.lean`.

Main declarations:

- `primitiveRootGramSum_posDef_iff_mulVec_injective`;
- `primitiveRootGramSum_not_posDef_of_lt`;
- `primitiveCoordinateRootGramSum_posDef`; and
- `primitiveInteriorArity_exact`.

Verification:

- direct source check:
  `lake env lean GaloisForLFunctions/HTGeometry/PrimitiveInteriorArity.lean`;
- axiom audit of main theorems: only `propext`, `Classical.choice`, and `Quot.sound`;
- repository formal lint: passed; and
- final target build:
  `lake build GaloisForLFunctions.HTGeometry.PrimitiveInteriorArity`
  (`3238/3238`, successful).

## Log

- 2026-07-30 — extracted primitive interior arity after exact-recovery/no-spectator failed to
  imply pairwise causal closure.
- 2026-07-30 — formalized exact arity theorem unconditionally in Lean and passed final module
  audit.
