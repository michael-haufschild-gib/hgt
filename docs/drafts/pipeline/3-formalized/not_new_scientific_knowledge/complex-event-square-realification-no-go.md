# A complex event square has a faithful doubled-real presentation

- **ID:** `complex-event-square-realification-no-go`
- **Stage:** 3-formalized
- **Type:** EXACT REALIFICATION THEOREM / UNIVERSAL-LAW NO-GO
- **Scientific status:** `[PAPER-PROVED] [UNCONDITIONAL LEAN] [STANDARD ALGEBRA]`
  `[NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Parent conjecture:** `../../1-in-progress/universal-event-square-law.md`
- **Failed route:** `../../5-failed/static-event-square-selects-complex-field.md`
- **Lean target:**
  `GaloisForLFunctions.HTGeometry.ComplexEventSquareRealificationNoGo`

## Statement

For a complex matrix \(X=A+iB\in M_{m,n}(\mathbb C)\), define
\[
\rho(X)=
\begin{pmatrix}
A&-B\\
B&A
\end{pmatrix}
\in M_{2m,2n}(\mathbb R).
\tag{1}
\]

For all finite matrices of compatible sizes:

\[
\rho(X+Y)=\rho(X)+\rho(Y),
\qquad
\rho(XY)=\rho(X)\rho(Y),
\tag{2}
\]
\[
\rho(X^\dagger)=\rho(X)^T,
\tag{3}
\]
and \(\rho\) is injective. Therefore
\[
\boxed{
\rho(X^\dagger X)=\rho(X)^T\rho(X)
}
\tag{4}
\]
and
\[
\boxed{
\rho(X^\dagger Y)=\rho(X)^T\rho(Y).
}
\tag{5}
\]

In particular,
\[
\rho(q(X))=\rho(q(Y))
\iff q(X)=q(Y),
\qquad q(X)=X^\dagger X.
\tag{6}
\]
Realification loses none of the complex event-square record.

Let
\[
J_n=
\begin{pmatrix}
0&-I_n\\
I_n&0
\end{pmatrix}.
\tag{7}
\]
Then
\[
J_n^2=-I_{2n},
\tag{8}
\]
\[
J_m\rho(X)=\rho(iX)=\rho(X)J_n,
\tag{9}
\]
so every realified complex matrix intertwines the canonical source and target complex structures.

## Dependency-closed proof

Write \(X=A+iB\) and \(Y=C+iD\). Direct multiplication gives
\[
XY=(AC-BD)+i(AD+BC).
\tag{10}
\]
Substituting `(10)` into `(1)` yields
\[
\begin{aligned}
\rho(XY)
&=
\begin{pmatrix}
AC-BD&-(AD+BC)\\
AD+BC&AC-BD
\end{pmatrix}\\
&=
\begin{pmatrix}A&-B\\B&A\end{pmatrix}
\begin{pmatrix}C&-D\\D&C\end{pmatrix}
=\rho(X)\rho(Y),
\end{aligned}
\]
proving multiplication in `(2)`. Addition is entrywise.

Since
\[
X^\dagger=A^T-iB^T,
\]
equation `(1)` gives
\[
\rho(X^\dagger)
=
\begin{pmatrix}
A^T&B^T\\
-B^T&A^T
\end{pmatrix}
=\rho(X)^T,
\]
proving `(3)`. Equations `(4)` and `(5)` now follow from multiplication.

If \(\rho(X)=\rho(Y)\), equality of the upper-left blocks gives
\(\operatorname{Re}X=\operatorname{Re}Y\), while equality of the upper-right blocks gives
\(\operatorname{Im}X=\operatorname{Im}Y\). Hence \(X=Y\), proving injectivity and `(6)`.

Finally, block multiplication gives \(J_n^2=-I_{2n}\) and
\[
J_m
\begin{pmatrix}A&-B\\B&A\end{pmatrix}
=
\begin{pmatrix}-B&-A\\A&-B\end{pmatrix}
=
\begin{pmatrix}A&-B\\B&A\end{pmatrix}
J_n.
\]
The middle block is exactly \(\rho(iX)\), proving `(8)`--`(9)`.

## Exact no-go

A finite axiom system that inspects only:

- equality of event-square and cross-Gram records;
- addition;
- matrix composition;
- dagger/transpose; and
- the resulting quadratic identities

cannot distinguish the complex presentation from its faithful doubled-real presentation. In that
language, selecting the word “complex” is choosing coordinates, not deriving new physical
content.

This is a presentation no-go, not a proof that complex quantum theory and unconstrained real
quantum theory are physically identical. The real image is the restricted class of maps
intertwining \(J\). Tensor locality, independent-source composition, allowed observables, and how
different \(J\)'s are aligned may expose distinctions that a single finite matrix square does not.

## Hostile audit

This is standard realification of complex linear algebra. It is not new mathematics and proves no
physics.

It does **not** prove:

- that complex phase is physically redundant;
- that a physical source generates \(J\);
- that independent real systems share one \(J\);
- the Born rule or local tomography;
- causal order or Lorentz signature;
- a connection or curvature;
- gravity or a gauge force; or
- a continuum limit or prediction.

The result also does not rescue the retired claim that forces are curvature of a local imaginary
unit. A complex structure does not determine its comparison law. The present theorem says the
event square does not determine the complex presentation; the prior no-go says complex structure
does not determine connection. Both missing arrows must be supplied by a deeper compositional
law.

## Strongest positive survivor

The surviving exact structure is not a preferred scalar field but an **oriented intertwining
law**:

```text
complex amplitude
  = faithful real passage carrying J from source to target;

complex phase
  = quarter-turn orientation J with J² = -1;

physical complex selection
  must constrain how independently generated J-orientations compose.
```

This connects to the separately Lean-proved source result that two ordered real source
involutions generate a complex structure. Together they replace

```text
assume C
```

by the sharper open chain

```text
ordered source operations generate J
  -> admissible event passages intertwine J
  -> independent composition must decide relative J-orientation
  -> only a composition-sensitive obstruction can make complex phase physical.
```

The new research target is therefore **orientation descent**, not complex-field reconstruction
from a static cone.

## Lean certificate

Module:
`formal/GaloisForLFunctions/HTGeometry/ComplexEventSquareRealificationNoGo.lean`.

Declarations:

- `complexMatrixRealPart`;
- `complexMatrixImagPart`;
- `complexMatrixRealification`;
- `complexMatrixRealification_injective`;
- `complexMatrixRealification_add`;
- `complexMatrixRealification_mul`;
- `complexMatrixRealification_conjTranspose`;
- `complexMatrixRealification_eventSquare`;
- `complexMatrixRealification_eventCrossGram`;
- `complexMatrixRealification_eventSquare_eq_iff`;
- `doubledRealComplexStructure`;
- `doubledRealComplexStructure_sq`; and
- `complexMatrixRealification_intertwines_complexStructure`.

Direct foreground verification:

```text
lake env lean GaloisForLFunctions/HTGeometry/ComplexEventSquareRealificationNoGo.lean
```

completed with exit code zero and no warnings.

Focused final build:

```text
lake build GaloisForLFunctions.HTGeometry.ComplexEventSquareRealificationNoGo
✔ [1245/1245] Built GaloisForLFunctions.HTGeometry.ComplexEventSquareRealificationNoGo
Build completed successfully (1245 jobs).
```

`#print axioms` for the ten principal structural theorems reports only `propext`,
`Classical.choice`, and `Quot.sound`.

The module contains no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration and is
reachable from the `GaloisForLFunctions.HTGeometry` umbrella. Repository-wide formal lint passed
after a concurrent umbrella-reachability edit settled, with only pre-existing large-file warnings.

## Gates

- [x] exact statement
- [x] dependency-closed proof
- [x] hostile novelty classification
- [x] exact no-go scope
- [x] strongest nontrivial positive survivor
- [x] unconditional Lean formalization
- [x] direct foreground source check
- [x] focused final build
- [x] axiom audit
- [x] formal lint

## Log

- 2026-07-30 — proved faithful block realification for arbitrary finite rectangular complex
  matrices.
- 2026-07-30 — proved preservation of composition, adjoint, event squares, and cross-Gram
  records.
- 2026-07-30 — extracted \(J\)-intertwining as positive survivor and orientation descent as the
  next open primitive.
- 2026-07-30 — focused `1245/1245` build, axiom audit, and repository formal lint passed.
