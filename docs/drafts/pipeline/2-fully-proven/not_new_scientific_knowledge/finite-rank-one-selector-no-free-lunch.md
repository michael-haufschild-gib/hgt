# Finite Rank-One Selector No-Free-Lunch

- **ID:** finite-rank-one-selector-no-free-lunch
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / proof-route guardrail
- **Source:** `rh-landscape-proof-gate.md`, `no-boundary-selection-of-zeta.md`,
  `docs/consolidated/revision01/formulas.md`
- **Statement:** In a finite rank-one Krein repair family, the side of the
  positive/negative index crossing is exactly the Schur-Weyl scalar. Therefore any
  finite selector that uses only the rank-one family data and decides the repaired
  `N_0` side is a rephrasing of that scalar sign. A non-mirror RH proof must import
  additional source data before the finite rank-one chart, not another name for the
  threshold side inside the chart.

## Goal

Make the circularity warning in the `L_src` cards precise at the finite linear-algebra
level.

The RH-bearing scaffold repeatedly reaches a finite family

`H(t)=A+t vv^*`

where `A` has one negative square and `t>0` is the Gamma boundary parameter. The desired
statement is that the source-selected `t=a_*` lies on the `N_0` side for every degree.
This card proves that the finite family itself contains no second hidden selector: the
crossing side is the Schur scalar and nothing else.

## Theorem

Let `V` be a finite-dimensional complex vector space. Let `A` be an invertible Hermitian
form on `V` with inertia `(n,1)`, let `v in V` be nonzero, and let `t>0`.

Set

`m = v^* A^{-1} v`,

and define

`H(t)=A+t vv^*`.

Assume `m<0`, so a positive rank-one repair can cross the one-negative-square threshold.
Then

`H(t)` is positive definite if and only if

`S_A,v(t) := -1/t - m > 0`.

Equivalently, with the threshold `t_c=-1/m`,

`H(t) > 0  iff  t>t_c`.

For `0<t<t_c`, the inertia of `H(t)` remains `(n,1)`. At `t=t_c`, `H(t)` is singular
with one-dimensional kernel. Thus the entire finite threshold-side datum is the sign of
`S_A,v(t)`.

## Proof

Use the Schur-complement inertia identity for a rank-one update. The block Hermitian
matrix

```text
[ A   v ]
[ v* -1/t ]
```

has two Schur complements. Since `A` is invertible, it is congruent to

```text
A  direct_sum  (-1/t - v^* A^{-1} v).
```

Since `-1/t` is invertible, it is also congruent to

```text
H(t)  direct_sum  (-1/t).
```

By Sylvester inertia,

`inertia(H(t)) = inertia(A) + inertia(S_A,v(t)) - inertia(-1/t)`.

Here `inertia(A)=(n,1)` and `inertia(-1/t)=(0,1)`.

If `S_A,v(t)>0`, then `inertia(S_A,v(t))=(1,0)`, so

`inertia(H(t))=(n+1,0)`.

If `S_A,v(t)<0`, then `inertia(S_A,v(t))=(0,1)`, so

`inertia(H(t))=(n,1)`.

If `S_A,v(t)=0`, the same block congruence gives a one-dimensional null direction,
so `H(t)` is singular at the unique crossing. Since `m<0`,

`S_A,v(t)>0  iff  -1/t > m  iff  t > -1/m`.

This proves the theorem.

## Consequence for the RH Route

This theorem does not touch RH directly. It removes one false local move.

Inside the finite family `(A,v,t)`, the assertion "the Gamma repair lies on the `N_0`
side" is exactly the assertion `S_A,v(t)>0`. Therefore a proposed source-orientation
axiom is circular if, after stripping the source language, it only selects the sign of
`S_A,v(t)`.

The noncircular theorem must occur before this finite chart:

1. construct `A=R^P_d+M_triv,rest_d` and the boundary functional from Euler/Gamma/FE
   source data without zero feeding;
2. prove from that source construction, not from the Schur sign definition, that
   `S_A,v(a_*)>0` for all `d`;
3. separate Davenport-Heilbronn or sign-reversed prime fakes by the source construction
   itself, not by observing that they land on the wrong side of the threshold.

Thus the finite rank-one Krein chart is a faithful coordinate, not a proof engine.

## Source Boundary

The inertia identity is classical Schur-complement / Sylvester inertia algebra, and the
rank-one perturbation language belongs to standard Krein-Langer / Uvarov / Sherman-Morrison
machinery. The card claims no novelty for the algebra. Its value is a proof-route guardrail:
it states exactly where a source-built RH proof must supply new content.

## Gates

- [x] 0 -> 1 in-progress: circularity question isolated in `L_src`.
- [x] 1 -> 2 fully-proven: finite rank-one inertia proof written.
- [ ] 2 -> 3 formalized: Lean finite-dimensional Hermitian inertia theorem, if useful.

## Log

- 2026-06-24 — Professor: created after the stricter RH-only goal reset. Entropy draw
  `change-representation` / `river-meanders`: represent the repair as a one-parameter
  crossing, then identify the only finite crossing coordinate.

## 2026-06-24 finite-rank quotient warning

`finite-rank-counterterm-kernel-visibility.md` supplies the all-order visibility version of the finite rank-one warning. A rank-one repair is a faithful Schur/Krein coordinate only after the boundary functional is source-built. If the boundary functional evaluates a bad reciprocal atom, the quotient can cancel that atom by construction; the kernel theorem sees only the atoms invisible to the boundary map.

## 2026-06-24 non-atomic rank-one repairs

`non-atomic-finite-rank-counterterms-rh-strength.md` gives the source-facing rank-one test. A rank-one boundary functional that is non-atomic on the reciprocal support cannot hide an off-line atom; positivity of the repaired all-order form remains RH-strength. To weaken the target, the boundary functional must see atom-isolators, which demands a source theorem for that quotient data.

## 2026-06-24 matrix boundary generalization

`finite-rank-boundary-schur-index.md` is the finite-rank version of this rank-one selector theorem. Replacing one channel by `V:C^r->E` and an invertible boundary form `C`, the crossing side is the inertia of the boundary Schur matrix `S=-C^{-1}-V*B^{-1}V`.

Thus the rank-one scalar is only a one-channel compression of the matrix boundary gate. A semilocal proof must prove the full boundary Schur index from source data, not only the first-trivial-zero scalar.

## 2026-06-24 scalar-shadow kernel condition

`rank-one-scalar-shadow-needs-kernel-exhaustion.md` records the complementary failure mode. This card says the finite rank-one chart has no second threshold-side selector; the scalar-shadow card says even a positive scalar is not a full-index certificate unless the boundary kernel has already been proved nonnegative.

Together they isolate the source residue: construct the finite chart from source data, then prove the kernel/omitted-channel exhaustion and Schur sign from source orientation rather than by naming the threshold side.
