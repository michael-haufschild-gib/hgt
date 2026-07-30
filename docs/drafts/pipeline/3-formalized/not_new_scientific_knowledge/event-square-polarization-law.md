# A matrix-valued event square retains complete coherent comparison

- **ID:** `event-square-polarization-law`
- **Stage:** 3-formalized
- **Type:** EXACT MATRIX POLARIZATION THEOREM / UNIVERSAL-LAW BRIDGE
- **Scientific status:** `[PAPER-PROVED] [UNCONDITIONAL LEAN] [STANDARD ALGEBRA]`
  `[NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Parent conjecture:** `../../1-in-progress/universal-event-square-law.md`
- **Lean target:** `GaloisForLFunctions.HTGeometry.EventSquarePolarization`

## Statement

For finite complex matrices \(X,Y\in M_{m,n}(\mathbb C)\), define
\[
q(X)=X^\dagger X,\qquad \beta(X,Y)=X^\dagger Y.
\]
Then
\[
q(X+Y)-q(X-Y)
=2\bigl(\beta(X,Y)+\beta(Y,X)\bigr),
\tag{1}
\]
\[
q(X+iY)-q(X-iY)
=2i\bigl(\beta(X,Y)-\beta(Y,X)\bigr),
\tag{2}
\]
and therefore
\[
\boxed{
\beta(X,Y)=\frac14\left[
q(X+Y)-q(X-Y)
-i\bigl(q(X+iY)-q(X-iY)\bigr)
\right].
}
\tag{3}
\]

Thus the values of one matrix-valued quadratic map on four coherent superpositions recover the
complete ordered cross-Gram matrix.

## Dependency-closed proof

Expand:
\[
\begin{aligned}
q(X+Y)
&=X^\dagger X+X^\dagger Y+Y^\dagger X+Y^\dagger Y,\\
q(X-Y)
&=X^\dagger X-X^\dagger Y-Y^\dagger X+Y^\dagger Y.
\end{aligned}
\]
Subtraction gives `(1)`.

Since \((iY)^\dagger=-iY^\dagger\),
\[
\begin{aligned}
q(X+iY)
&=X^\dagger X+iX^\dagger Y-iY^\dagger X+Y^\dagger Y,\\
q(X-iY)
&=X^\dagger X-iX^\dagger Y+iY^\dagger X+Y^\dagger Y.
\end{aligned}
\]
Subtraction gives `(2)`. Multiplying `(2)` by \(-i\), adding `(1)`, and using
\(i^2=-1\) gives \(4X^\dagger Y\), proving `(3)`.

## Hostile audit

This is the standard complex polarization identity with a matrix-valued codomain. It is not new
mathematics and proves no physics.

It does **not** prove:

- that \(X\) is a physical quantum amplitude;
- that \(q(X)\) is a causal event or spacetime point;
- that a source generates complex scalars or a dagger;
- the Born rule;
- that root ambiguity is a physical gauge group;
- gravity or any gauge force;
- a composition law for event squares; or
- a prediction.

## Strongest positive survivor

The exact boundary is stronger than scalar norm recovery:

```text
matrix-valued positive square on coherent superpositions
  -> full ordered sesquilinear cross record
  -> positive and coherent reporters need not be separate primitive layers.
```

This licenses one sharply typed research question: can a physical source generate the quadratic
map itself, including its scalar orientation, positivity, target, and composition? It does not
license the physical identification.

## Lean certificate

Module:
`formal/GaloisForLFunctions/HTGeometry/EventSquarePolarization.lean`.

Declarations:

- `eventSquare`;
- `eventCrossGram`;
- `eventSquare_add_sub_polarization`;
- `eventSquare_i_add_sub_polarization`; and
- `eventCrossGram_eq_eventSquare_polarization`.

Direct foreground verification:

```text
lake env lean GaloisForLFunctions/HTGeometry/EventSquarePolarization.lean
```

completed with exit code zero and no warnings.

Focused final build and axiom audit are recorded after the repository audit below.

Focused final build:

```text
lake build GaloisForLFunctions.HTGeometry.EventSquarePolarization
✔ [1221/1221] Built GaloisForLFunctions.HTGeometry.EventSquarePolarization
Build completed successfully (1221 jobs).
```

`#print axioms` for all three theorems reports only `propext`, `Classical.choice`, and
`Quot.sound`. The repository formal lint passed with only pre-existing large-file warnings.
The module and the preceding bare-source composition module are reachable from the
`GaloisForLFunctions.HTGeometry` umbrella. No umbrella build claim is made.

## Gates

- [x] exact statement
- [x] dependency-closed proof
- [x] hostile novelty classification
- [x] strongest nontrivial positive survivor
- [x] unconditional Lean formalization
- [x] direct foreground source check
- [x] focused final build
- [x] axiom audit
- [x] formal lint

## Log

- 2026-07-30 — extracted as the exact algebraic core of the universal event-square conjecture.
- 2026-07-30 — classified as standard complex polarization, not new scientific knowledge.
- 2026-07-30 — formalized for arbitrary finite complex rectangular matrices.
- 2026-07-30 — focused `1221/1221` build, axiom audit, and formal lint passed.
