# A static event square cannot select the complex field

- **ID:** `static-event-square-selects-complex-field`
- **Stage:** 5-failed
- **Type:** UNIVERSAL-RIGIDITY ROUTE / PRESENTATION NO-GO
- **Scientific status:** `[FALSIFIED AS STATED] [POSITIVE SURVIVOR LEAN-FORMALIZED]`
- **Parent:** `../1-in-progress/universal-event-square-law.md`
- **Formal survivor:**
  `../3-formalized/not_new_scientific_knowledge/complex-event-square-realification-no-go.md`

## Failed route

The proposed first rigidity theorem asked a finite source-positive event-square axiom system to
force
\[
M_{3,2}(\mathbb C)\longrightarrow H_2(\mathbb C)_+,
\qquad X\longmapsto X^\dagger X,
\]
and in particular to exclude real competitors without using independent composition.

That target is false at the level of a static event square.

## Exact killing theorem

For every finite complex rectangular matrix,
\[
\rho(X)=
\begin{pmatrix}
\operatorname{Re}X&-\operatorname{Im}X\\
\operatorname{Im}X&\operatorname{Re}X
\end{pmatrix}
\]
is an injective doubled-real representation satisfying
\[
\rho(X+Y)=\rho(X)+\rho(Y),\qquad
\rho(XY)=\rho(X)\rho(Y),\qquad
\rho(X^\dagger)=\rho(X)^T.
\]
Hence
\[
\rho(X^\dagger X)=\rho(X)^T\rho(X),\qquad
\rho(X^\dagger Y)=\rho(X)^T\rho(Y).
\]

The complex event square and its complete matrix-valued polarization therefore have a faithful
real presentation. Any finite selector invariant under faithful presentation and using only these
operations accepts both descriptions.

The route cannot be repaired by adding more identities in the same static algebraic language.

## Strongest positive survivor

Realification does not erase complex structure. It relocates it to
\[
J_n=
\begin{pmatrix}0&-I_n\\I_n&0\end{pmatrix},
\qquad J_n^2=-I,
\]
with every admissible realified passage obeying
\[
J_m\rho(X)=\rho(X)J_n.
\]

Thus complex content is equivalently an **orientation plus an intertwining restriction**.
The corpus independently proves that an ordered pair of real source operations can generate such
a \(J\). The maximal positive chain is:

```text
source order can generate J;
complex passages are exactly represented by J-intertwiners;
static event squares cannot decide how independently generated J's are aligned;
therefore the first potentially physical invariant is the obstruction to sewing source-created
orientations across independent event-square composition.
```

This is not a restated negation: it identifies the exact surviving datum, its transport equation,
and the next composition-sensitive location where a non-representational distinction can occur.

## New insight

Three no-go theorems now form one boundary:

1. bare outcomes do not naturally compose at the same type;
2. event-square algebra does not select its complex presentation; and
3. one complex structure does not select connection or curvature.

Therefore none of `outcome`, `square`, `complex field`, `J`, or `curvature` is the universal
primitive. The smallest viable object must contain, in one typed cell:

```text
source-generated root
  -> positive quadratic fact
  + generated orientation
  + active sewing law
  + boundary comparison.
```

The next law must make spacetime and forces projections of failure of this whole cell to globalize,
not decorations attached to a pre-existing Hilbert space.

## Status

- static complex-field selection: falsified;
- exact realification theorem: dependency-closed on paper and unconditionally formalized in Lean;
- \(J\)-intertwining survivor: dependency-closed on paper and unconditionally formalized in Lean;
- source generation of \(J\): already separately paper-proved and Lean-formalized;
- independent orientation-sewing obstruction: open;
- physical complex selection, gauge sector, gravity, and prediction: open;
- Nature claim: prohibited.

## Log

- 2026-07-30 — hostile realification test killed static complex-field rigidity.
- 2026-07-30 — extracted \(J\)-intertwining and independent orientation descent as positive
  survivor.
- 2026-07-30 — connected the survivor to existing source-generated complex-structure and
  connection-underdetermination theorems.
