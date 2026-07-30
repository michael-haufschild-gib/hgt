# Fixed-carrier quadratic variation is path-flat

- **ID:** `fixed-carrier-quadratic-variation-flatness`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / UNIVERSAL-LAW NO-GO
- **Scientific status:** `[PROVED HERE] [DEPENDENCY-CLOSED] [STANDARD OPERATOR ALGEBRA]`
  `[NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Parent:** `../../1-in-progress/actuality-creates-future-law.md`
- **Statement:** Lost-layer Gram squares form an exact compressed cocycle; every diamond of
  globally supplied nested consequence projections is path-flat.

## Goal

Test the conjecture that the positive quadratic variation of a decreasing quantum consequence
filtration could itself be gravity. The theorem gives the strongest exact survivor and isolates
what any nonzero force must add.

## Setup

Let \(H\) be a complex Hilbert space and let \(P,Q,R\in\mathcal B(H)\). Write
\[
Q\preceq P
\quad\Longleftrightarrow\quad
QP=PQ=Q.
\tag{1}
\]
When \(P,Q\) are orthogonal projections, define the lost layer, lost transition, quadratic
variation, and off-carrier quadratic corner by
\[
L(P,Q)=P-Q,
\qquad
X_D(P,Q)=L(P,Q)DQ,
\tag{2}
\]
\[
\Delta_D(P,Q)=QD(P-Q)DQ,
\qquad
C_D(P)=PD(1-P)DP.
\tag{3}
\]
For the Gram interpretation assume \(D=D^\dagger\). The algebraic restriction and cocycle laws
do not require this assumption.

## Theorem

For orthogonal projections \(Q\preceq P\) and self-adjoint \(D\):

1. \(L(P,Q)\) is an orthogonal projection;
2. restriction of the larger corner creates exactly the lost-layer variation,
   \[
   C_D(Q)-Q\,C_D(P)\,Q=\Delta_D(P,Q);
   \tag{4}
   \]
3. that variation is a positive Gram square,
   \[
   \Delta_D(P,Q)=X_D(P,Q)^\dagger X_D(P,Q)\geq0.
   \tag{5}
   \]

The cocycle is more general than its positive interpretation. For arbitrary bounded operators
\(P,Q,R,D\), the two absorption identities
\[
QR=RQ=R
\tag{6a}
\]
already imply
\[
\boxed{
\Delta_D(P,R)
=
\Delta_D(Q,R)+R\,\Delta_D(P,Q)\,R.
}
\tag{6}
\]

Consequently, if \(Q_1,Q_2\) are any two bounded operators absorbed by a common final carrier,
\[
Q_iR=RQ_i=R,
\]
then the two compressed path sums through the diamond agree:
\[
\boxed{
\Delta_D(Q_1,R)+R\Delta_D(P,Q_1)R
=
\Delta_D(Q_2,R)+R\Delta_D(P,Q_2)R.
}
\tag{7}
\]
Both sides equal \(\Delta_D(P,R)\).

Thus neither idempotence, self-adjointness, nor comparability of \(Q_1,Q_2\) with \(P\) is needed
for fixed-carrier diamond flatness. Those hypotheses are needed only when the terms are to be read
as positive variation of genuinely nested consequence projections.

The ordinary additive curvature of a triple,
\[
\kappa_D(P,Q,R)
:=
\Delta_D(P,R)-\Delta_D(P,Q)-\Delta_D(Q,R),
\tag{8}
\]
is therefore only compression curvature:
\[
\boxed{
\kappa_D(P,Q,R)=R\Delta_D(P,Q)R-\Delta_D(P,Q).
}
\tag{9}
\]

Conversely, quadratic flatness detects absorption exactly. For orthogonal projections \(Q,R\),
the single unit-top, identity-passage test satisfies
\[
\boxed{
\Delta_I(I,R)
=
\Delta_I(Q,R)+R\Delta_I(I,Q)R
\quad\Longleftrightarrow\quad
QR=RQ=R.
}
\tag{10}
\]
Thus fixed-carrier path flatness is not merely a consequence of having a common final consequence
carrier. In this universal test it characterizes that carrier relation.

## Dependency-closed proof

From \(QP=PQ=Q\), \(P^2=P\), and \(Q^2=Q\),
\[
(P-Q)^2=P^2-PQ-QP+Q^2=P-Q.
\]
Self-adjointness is preserved by subtraction, proving claim 1.

Nesting absorbs the outer \(P\)'s:
\[
Q\,C_D(P)\,Q
=QPD(1-P)DPQ
=QD(1-P)DQ.
\]
Hence
\[
\begin{aligned}
C_D(Q)-Q\,C_D(P)\,Q
&=QD\bigl((1-Q)-(1-P)\bigr)DQ\\
&=QD(P-Q)DQ,
\end{aligned}
\]
which is `(4)`. Moreover
\[
X_D(P,Q)^\dagger
=QD(P-Q),
\]
and the lost-layer idempotence gives
\[
X_D(P,Q)^\dagger X_D(P,Q)
=QD(P-Q)^2DQ
=\Delta_D(P,Q).
\]
This proves `(5)`.

From \(QR=RQ=R\), without using any projection hypothesis,
\[
R\Delta_D(P,Q)R
=RD(P-Q)DR.
\]
Therefore
\[
\begin{aligned}
\Delta_D(Q,R)+R\Delta_D(P,Q)R
&=RD(Q-R)DR+RD(P-Q)DR\\
&=RD(P-R)DR\\
&=\Delta_D(P,R),
\end{aligned}
\]
proving `(6)`. Apply `(6)` once with \(Q_1\) and once with \(Q_2\) to obtain `(7)`.
Subtracting \(\Delta_D(P,Q)+\Delta_D(Q,R)\) from `(6)` proves `(9)`.

For `(10)`, projection idempotence gives
\[
\Delta_I(I,R)=R(I-R)R=0,
\qquad
\Delta_I(I,Q)=Q(I-Q)Q=0,
\]
and
\[
\Delta_I(Q,R)=R(Q-R)R=RQR-R.
\]
Hence the flatness equation is equivalent to \(RQR=R\). If \(QR=RQ=R\), this is immediate.
Conversely, put \(X=(I-Q)R\). Orthogonality gives
\[
X^\dagger X
=R(I-Q)^2R
=R(I-Q)R
=R-RQR
=0.
\]
Faithfulness of the Hilbert norm implies \(X=0\), hence \(QR=R\). Taking adjoints gives \(RQ=R\).

## Exact no-go

The route

```text
positive lost-layer square on one fixed Hilbert carrier
  = gravity
```

fails. Even with branching intermediate projections, every globally supplied nested projection
diagram has path-independent transported variation. The apparent triple curvature is a
compression-minus-identity coboundary; on the Sonin aperture chain its trace is already known to
admit an explicit Ward potential.

Thus adding more projections, more nested scales, or more paths inside one common carrier cannot
produce fundamental force curvature.

## Strongest positive survivor

The exact survivor is the **lost-layer quadratic-variation law** `(4)`--`(6)`:

```text
coherent carrier shrinks
  -> lost transition X
  -> new positive record X†X
  -> exact compressed conservation through every chain.
```

This is a rigorous local realization of “what stops being a coherent possibility becomes a
positive distinction.” It also sharpens the missing structure:

```text
nonzero physical curvature
  -> no single fixed carrier containing all local consequence projections compatibly;
  -> comparison must be source-generated only locally;
  -> force is obstruction to gluing the local quadratic-variation laws.
```

Equation `(10)` adds an exact discriminator: failure of the unit quadratic cocycle is precisely
failure of a proposed final projection to absorb the earlier consequence carrier. In the finite
projection model, quadratic curvature measures failure of common-future amalgamation rather than
an arbitrary connection placed on supplied fibres.

The new open object is therefore a presentation-invariant obstruction for locally defined
consequence filtrations on changing carriers, not another fixed-carrier commutator.

## Hostile audit

Equations `(4)`--`(9)` are elementary operator algebra. They do not identify a Hilbert projection
with physical possibility, an operator \(D\) with dynamics, a Gram square with spacetime, or a
gluing obstruction with gravity. They prove neither external novelty nor a physical law.

The result does show that any claimed force obtained from a globally supplied nested projection
family is a false positive: its transported quadratic variation is path-flat before any field
equation is imposed. The formal proof strengthens this: flatness survives even when intermediate
operators are not projections and need not be comparable, provided they share the same absorbed
final carrier.

## Gates

- [x] 0 → 1 in-progress: well-posed exact no-go and positive survivor
- [x] 1 → 2 fully-proven: dependency-closed paper proof above
- [x] 2 → 3 formalized: unconditional Lean module and axiom audit complete; repository lint
  initially encountered an unrelated transient unreachable RHTower module and is rerun after the
  shared worktree settles
- [ ] 3 → 4 publication-ready: not a standalone publication target

## Log

- 2026-07-30 — extracted from Sonin restriction-defect, curvature, and Ward-potential corpus;
  paper proof closed.
- 2026-07-30 — Lean forced a stronger algebraic statement: cocycle and diamond flatness need only
  final-carrier absorption, not orthogonality or comparability of intermediate operators.
- 2026-07-30 — hostile converse test closed: for orthogonal projections, one unit quadratic
  cocycle is flat iff the proposed final carrier absorbs the intermediate carrier.
