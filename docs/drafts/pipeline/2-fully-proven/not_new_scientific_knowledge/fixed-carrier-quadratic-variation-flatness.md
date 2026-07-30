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

For three nested orthogonal projections \(R\preceq Q\preceq P\),
\[
\boxed{
\Delta_D(P,R)
=
\Delta_D(Q,R)+R\,\Delta_D(P,Q)\,R.
}
\tag{6}
\]

Consequently, if \(Q_1,Q_2\) are any two intermediate orthogonal projections with
\[
R\preceq Q_i\preceq P,
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

For \(R\preceq Q\),
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

The new open object is therefore a presentation-invariant obstruction for locally defined
consequence filtrations on changing carriers, not another fixed-carrier commutator.

## Hostile audit

Equations `(4)`--`(9)` are elementary operator algebra. They do not identify a Hilbert projection
with physical possibility, an operator \(D\) with dynamics, a Gram square with spacetime, or a
gluing obstruction with gravity. They prove neither external novelty nor a physical law.

The result does show that any claimed force obtained from a globally supplied nested projection
family is a false positive: its transported quadratic variation is path-flat before any field
equation is imposed.

## Gates

- [x] 0 → 1 in-progress: well-posed exact no-go and positive survivor
- [x] 1 → 2 fully-proven: dependency-closed paper proof above
- [ ] 2 → 3 formalized: Lean module and axiom/lint audit
- [ ] 3 → 4 publication-ready: not a standalone publication target

## Log

- 2026-07-30 — extracted from Sonin restriction-defect, curvature, and Ward-potential corpus;
  paper proof closed.
