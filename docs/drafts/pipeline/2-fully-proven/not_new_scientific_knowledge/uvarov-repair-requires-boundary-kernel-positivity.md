# Uvarov Repair Requires Boundary-Kernel Positivity

- **ID:** uvarov-repair-requires-boundary-kernel-positivity
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / proof-route guardrail
- **Source:** `finite-rank-one-selector-no-free-lunch.md`,
  `../../3-formalized/not_new_scientific_knowledge/pole-budget-does-not-imply-uvarov-repair.md`, and
  `no-boundary-selection-of-zeta.md`
- **Statement:** A positive rank-one repair at a boundary functional can only
  repair directions visible to that functional. Therefore first-trivial-zero
  Uvarov positivity requires the unrepaired form to be nonnegative on the full
  kernel `p(y_*)=0` before the scalar threshold is considered.

## Goal

State the local condition hidden behind the scalar Weyl gap. If

`H(t)=A+t beta^*beta`

is positive semidefinite, then every vector invisible to `beta` is already judged
by `A` alone. Thus the `y_*`-repair problem has a codimension-one positivity
pre-gate on `ker e_{y_*}`.

## Theorem

Let `V` be a finite-dimensional complex vector space, let `A` be a Hermitian form
on `V`, let `beta: V -> C` be a nonzero linear functional, and let `t>0`.

If

`A + t beta^* beta >= 0`,

then

`A|_{ker beta} >= 0`.

If `A` is invertible with inertia `(n,1)` and `A+t beta^*beta` is positive
definite, then `A|_{ker beta}` is positive definite.

Conversely, if `A|_{ker beta}` is positive definite, then after choosing any
`q` with `beta(q)=1` and writing

`V = ker beta direct_sum C q`,

the positivity of `A+t beta^*beta` is exactly the one scalar Schur condition

`a+t-l^*B^{-1}l > 0`,

where `B=A|_{ker beta}`, `l(k)=A(k,q)`, and `a=A(q,q)`.

## Proof

If `k in ker beta`, then

`(A+t beta^*beta)(k)=A(k)`.

Hence positive semidefiniteness of the repaired form immediately gives
`A(k)>=0` for every `k in ker beta`. If the repaired form is positive definite,
then the same equality gives `A(k)>0` for every nonzero `k in ker beta`.

For the converse scalar reduction, write the matrix of `A+t beta^*beta` in the
decomposition `V=ker beta direct_sum Cq`:

```text
[ B       l ]
[ l^*   a+t ]
```

When `B>0`, Schur complement gives positive definiteness exactly when

`a+t-l^*B^{-1}l > 0`.

This proves the theorem.

## Consequence for the RH Route

For the first-trivial-zero Uvarov chart, `beta=e_{y_*}` with

`y_*=-4/25`.

Therefore any source-built proof that

`H^-_d + a_* e_{y_*}^*e_{y_*} >= 0`

must first prove

`H^-_d[p] >= 0` for every polynomial `p` of degree at most `d` with `p(y_*)=0`.

Only after this boundary-kernel positivity holds does the scalar Weyl threshold
become the remaining finite datum. Pole-channel positivity on `p(-4)=0` is not
this pre-gate; the two kernels differ by `two-boundary-rank-one-nontransfer.md`.

This isolates a sharper source theorem than "prove the scalar sign":

`source-built H^-_d is nonnegative on ker e_{-4/25}, and the Schur scalar is on the positive side`.

The first clause is already a large codimension-one positivity statement. It
cannot be supplied by the pole budget alone, by
`../../3-formalized/not_new_scientific_knowledge/pole-budget-does-not-imply-uvarov-repair.md`.

## Source Boundary

The theorem is finite-dimensional Schur-complement algebra. It does not prove RH.
It identifies a necessary local condition for the source-built Uvarov route and
separates that condition from the pole-channel archimedean split.

## Gates

- [x] 0 -> 1 in-progress: hidden kernel pre-gate isolated.
- [x] 1 -> 2 fully-proven: finite proof written.
- [ ] 2 -> 3 formalized: optional Schur-complement / principal-subspace lemma.

## Log

- 2026-06-24 -- Codex: created after the pole-budget countermodel. The theorem
  names the codimension-one positivity condition on `p(-4/25)=0` that any
  first-trivial-zero repair proof must establish before the scalar Weyl gap can
  carry the remaining sign.

## 2026-06-24 all-order pre-gate strength

`uvarov-kernel-pregate-rh-equivalence.md` records the all-order consequence of this finite necessary condition. For the actual reciprocal divisor, positivity on the full first-trivial-zero kernel `p(-4/25)=0` is already equivalent to RH, because multiplication by `(y+4/25)^2` does not hide any reciprocal atom.

Thus this card's kernel pre-gate is useful as a finite local decomposition of the Uvarov repair, but the all-order pre-gate must still be source-derived. It is not a weaker assumption than the shifted `Q_0` positivity wall.

## 2026-06-24 scalar-shadow card

`rank-one-scalar-shadow-needs-kernel-exhaustion.md` packages this card's necessary kernel condition into the scalar-shadow warning used by the semilocal route. The scalar Weyl sign decides the rank-one repair only after `A|_{ker beta}` has been proved nonnegative.

Therefore a first-trivial-zero scalar certificate must be read as a two-part theorem: kernel positivity on `p(y_*)=0`, then the scalar Schur sign. Omitting the first clause is exactly the scalar-shadow failure.

## 2026-08-15 Lean partial formalization

The necessary kernel gates are now closed in
`HTGeometry/FiniteRankCountertermKernelVisibility.lean`: repaired
nonnegativity forces base nonnegativity on `ker L`
(`finiteRankCounterterm_nonneg_on_ker`), while strict repaired positivity
forces strict base positivity there
(`finiteRankCounterterm_pos_on_ker`). These are unconditional Lean proofs for
the real-quadratic-form abstraction of the first two displayed implications.

The full card remains Stage 2: the arbitrary complex-Hermitian boundary
functional to `ker beta ⊕ Cq` coordinate bridge, and its exact scalar Schur
reduction, have not yet been formalized.

## 2026-08-15 Lean split-coordinate Schur closure

`HTGeometry/RankOneScalarShadow.lean` now proves the exact Hermitian Schur
reduction once the boundary split has been supplied: a positive-definite
kernel block is equivalent to the single scalar condition for both
semidefinite and positive-definite repaired blocks. It also proves that a
positive repaired block has a positive kernel principal block, matching the
strict local pre-gate, and gives the explicit one-visible/one-invisible
countermodel.

The card remains Stage 2 because the theorem is stated for an arbitrary
complex-linear boundary functional. The Lean library still needs its
coordinate-free `ker beta ⊕ Cq` decomposition and congruence transport before
this exact card statement is closed.
