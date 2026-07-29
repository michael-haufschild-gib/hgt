# Globally chosen unitary event completions are exactly flat

- **ID:** `fixed-carrier-unitary-completion-flatness`
- **Stage:** 3-formalized
- **Type:** EXACT NO-GO / POSITIVE CLASSIFICATION / BRIDGE
- **Parent:** `actuality-conservation-boundary-colligation-law.md`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [REDISCOVERED] [BRIDGE]`
  `[NO PHYSICAL CLAIM PROVED]`
- **Lean module:**
  `formal/GaloisForLFunctions/HTGeometry/UnitaryCompletionMemoryFlatness.lean`
- **Statement:** Two unitary completions with the same visible event differ only by a unitary on
  the hidden defect sector, and relative completion memory on one global carrier is an exact
  coboundary with zero closed-loop holonomy.

## Goal

Test whether the non-endpoint-compressible component of a complete event can itself carry
curvature when every event is represented by a globally supplied unitary on one fixed carrier.
Extract the strongest exact classification if that representation is flat.

## Setup

Let \(A\in M_n(\mathbb C)\) be a self-adjoint involution and put
\[
P=\frac{1-A}{2},\qquad Q=\frac{1+A}{2}.
\]
Let \(U,V\in M_n(\mathbb C)\) be two-sided unitary completions with the same visible preserving
part:
\[
UQ=VQ.
\]
Define their relative completion memory by
\[
\mu(U,V)=U^\dagger V.
\]

## Exact claim under attack

### Theorem

1. \(\mu(U,V)\) is two-sided unitary;
2. \(\mu(U,V)Q=Q\mu(U,V)=Q\);
3. \(\mu(U,V)=Q+P\mu(U,V)P\);
4. \(V=U\mu(U,V)\);
5. \(VP=(UP)\mu(U,V)\);
6. for any two-sided unitary \(U,V,W\),
   \[
   \mu(U,V)\mu(V,W)=\mu(U,W);
   \]
7. every triangular completion holonomy is the identity; and
8. relative to one reference completion \(U\), the fiber of all completions of \(UQ\) is exactly
   the two-sided unitary matrices \(R\) satisfying \(RQ=QR=Q\); by item 3 their only free block is
   \(PRP\), on the defect sector.

## Dependency-closed proof

Because \(A^2=1\) and \(A^\dagger=A\), the matrices \(P,Q\) are complementary self-adjoint
projections:
\[
P+Q=1,\qquad P^2=P,\qquad Q^2=Q,\qquad PQ=QP=0,\qquad
P^\dagger=P,\qquad Q^\dagger=Q.                              \tag{1}
\]

Write \(\mu=\mu(U,V)=U^\dagger V\). Its adjoint is
\(\mu^\dagger=V^\dagger U\). Two-sided unitarity gives
\[
\mu^\dagger\mu
=V^\dagger UU^\dagger V
=V^\dagger V
=1,
\qquad
\mu\mu^\dagger
=U^\dagger VV^\dagger U
=U^\dagger U
=1.                                                           \tag{2}
\]
This proves item 1.

The common visible part \(UQ=VQ\) implies
\[
\mu Q=U^\dagger VQ=U^\dagger UQ=Q.                            \tag{3}
\]
Taking adjoints of \(UQ=VQ\) and using \(Q^\dagger=Q\) gives
\[
QU^\dagger=QV^\dagger.
\]
Multiplying on the right by \(V\) gives
\[
Q\mu=QU^\dagger V=QV^\dagger V=Q.                             \tag{4}
\]
This proves item 2.

Insert \(1=P+Q\) on both sides of \(\mu\). Equations `(1)`, `(3)`, and `(4)` give
\[
\begin{aligned}
\mu
  &=(P+Q)\mu(P+Q)\\
  &=P\mu P+P\mu Q+Q\mu P+Q\mu Q\\
  &=P\mu P+PQ+QP+Q^2\\
  &=P\mu P+Q.
\end{aligned}                                                  \tag{5}
\]
This proves item 3.

Right unitarity of \(U\) reconstructs the second completion:
\[
U\mu=UU^\dagger V=V.                                          \tag{6}
\]
Thus item 4 holds. Equation `(5)` also gives
\[
\mu P=P\mu P=P\mu.
\]
Multiplying `(6)` on the right by \(P\) therefore yields
\[
VP=U\mu P=UP\mu,                                               \tag{7}
\]
which is item 5. Hence the relative completion changes only the complementary defect transport,
never the visible preserving part.

For arbitrary two-sided unitaries \(U,V,W\),
\[
\begin{aligned}
\mu(U,V)\mu(V,W)
  &=(U^\dagger V)(V^\dagger W)\\
  &=U^\dagger(VV^\dagger)W\\
  &=U^\dagger W
  =\mu(U,W).
\end{aligned}                                                  \tag{8}
\]
This proves item 6. Applying `(8)` twice gives
\[
\mu(U,V)\mu(V,W)\mu(W,U)
=\mu(U,W)\mu(W,U)
=U^\dagger WW^\dagger U
=1,                                                            \tag{9}
\]
proving item 7.

It remains to classify the fiber. Fix a two-sided unitary \(U\). If \(R\) is two-sided unitary and
\[
RQ=QR=Q,                                                       \tag{10}
\]
then \(UR\) is two-sided unitary and
\[
(UR)Q=U(RQ)=UQ.                                                \tag{11}
\]
Thus right multiplication by \(R\) produces another completion of the same visible event.

Conversely, if \(V\) is any two-sided unitary satisfying \(VQ=UQ\), items 1--4 show that
\[
R=\mu(U,V)
\]
is two-sided unitary, satisfies `(10)`, and reconstructs \(V=UR\). This \(R\) is unique: if
\(UR=US\), multiplication on the left by \(U^\dagger\) gives \(R=S\). Finally `(5)` says every
such \(R\) has the form
\[
R=Q+PRP,                                                       \tag{12}
\]
so its only unconstrained block lies on the defect sector. This proves item 8 and the theorem.
\(\square\)

## Hostile proof audit

1. No inference uses dimension counting, a selected basis, positivity beyond unitarity, or a
   physical interpretation.
2. Both equations \(RQ=Q\) and \(QR=Q\) are derived; one-sided invariance is not silently treated
   as a reducing-subspace statement.
3. The fiber classification is surjective and injective, not only an existence statement.
4. The flatness conclusion applies only when all local completions are supplied as matrices on one
   common global carrier. It does not rule out a nontrivial descent obstruction when no such
   global family exists.
5. The theorem does not identify the defect-sector unitary with gravity or any Standard Model
   group.

## Proposed representation lesson

If the claim closes, a family of explicit completion labels \(U_x\) on one fixed carrier cannot
generate physical curvature:
\[
\mu(U_x,U_y)=U_x^\dagger U_y
\]
is a global coboundary. Nonzero force curvature would require local completion data that cannot be
chosen as one globally coherent family. The Nature-bearing object would therefore be a descent
obstruction to global source-complete history, not a connection appended to globally labelled
events.

## External frontier

- Unitary extensions of partial isometries and defect-space freedom are established operator
  theory.
- Narasimhan--Ramanan universal connections show that Stiefel connections can realize arbitrary
  compact gauge connections; universality alone cannot select physical gauge content
  ([Narasimhan--Ramanan 1961](https://repository.ias.ac.in/44931/1/20-PUB.pdf)).
- Gravitational anomalies already provide obstructions to local Hilbert-space factorization.
  ([Hellerman--Orlando--Watanabe 2021](https://arxiv.org/abs/2101.03320)).
- Coherent control can distinguish unitarily equivalent Stinespring dilations of identical
  reduced dynamics, so completion data are not automatically operationally redundant
  ([Karthik--Shenoy--Usha Devi--Pawłowski 2026](https://arxiv.org/abs/2607.05643)).

The exact matrix classification is `[REDISCOVERED] [BRIDGE]`, not new science. Its new value inside
this corpus is the sharp boundary it places on the actuality-memory conjecture.

## Gates

- [x] 0 → 1 in-progress: exact source-pure statement and attack fixed
- [x] 1 → 2 fully-proven: dependency-closed paper proof
- [x] 2 → 3 formalized: exact Lean theorem and audit
- [ ] 3 → 4 publication-ready: not expected; theorem is a boundary result

## No-go closure

- **Exact killing theorem/mechanism:** relative completion memory on one global carrier is
  \(\mu(U,V)=U^\dagger V\), hence a strict coboundary with identity triangular holonomy.
- **Strongest positive survivor:** completions of one visible event form exactly the right orbit of
  defect-supported two-sided unitaries \(R=Q+PRP\).
- **New insight:** local completion history is a necessary carrier of hidden information, but
  globally labelled completion history is still pure gauge. Curvature can only reside in failure
  of source-complete local colligations to descend to one coherent global completion.
- **Status:** `[PAPER-PROVED] [LEAN-PROVED] [REDISCOVERED] [BRIDGE]`.

## Lean certificate

The exact paper theorem is formalized by:

- `unitaryCompletionMemory_leftUnitary`;
- `unitaryCompletionMemory_rightUnitary`;
- `unitaryCompletionMemory_mul_continuation`;
- `continuation_mul_unitaryCompletionMemory`;
- `unitaryCompletionMemory_defect_block`;
- `unitaryCompletionMemory_reconstruct`;
- `symmetryTransmutingPart_completionMemory`;
- `unitaryCompletionMemory_cocycle`;
- `unitaryCompletionMemory_triangle`;
- `unitaryCompletion_same_visible_of_defectGauge`;
- `unitaryCompletionMemory_unique`; and
- `unitaryCompletion_fiber_iff`.

Verification:

- direct foreground check
  `lake env lean GaloisForLFunctions/HTGeometry/UnitaryCompletionMemoryFlatness.lean`: passed;
- final module audit
  `lake build GaloisForLFunctions.HTGeometry.UnitaryCompletionMemoryFlatness`: passed
  (`2949/2949`);
- axiom audit of the defect-block, transmuting, cocycle, triangle, and fiber theorems: only
  `propext`, `Classical.choice`, and `Quot.sound`;
- proof-debt scan: no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe`;
- repository formal lint: passed.

## Log

- 2026-07-29 — created after endpoint-flatness and universal-connection audits isolated global
  completion labels as the next possible pure-gauge representation.
- 2026-07-29 — complete proof closed all eight clauses. Hostile audit found no mathematical gap;
  physical interpretation remains conjectural.
- 2026-07-29 — exact theorem formalized unconditionally and passed direct Lean, final module,
  axiom, proof-debt, and repository lint gates.
