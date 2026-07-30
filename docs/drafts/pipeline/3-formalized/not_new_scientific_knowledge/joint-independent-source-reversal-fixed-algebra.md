# Joint source reversal preserves complex phase; independent reversals preserve only scalars

- **ID:** `joint-independent-source-reversal-fixed-algebra`
- **Stage:** 3-formalized
- **Type:** EXACT FINITE FIXED-ALGEBRA CLASSIFICATION / CLIFFORD BRIDGE
- **Scientific status:** `[LEAN-PROVED] [REDISCOVERED] [BRIDGE]`
  `[NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Parent conjecture:**
  `../../1-in-progress/correlated-continuation-ambiguity-law.md`
- **Formal parent:** `source-ordered-pair-complex-structure.md`
- **Lean target:** `GaloisForLFunctions.HTGeometry.SourceOrderedPairComplexStructure`

## Convention and statement

Let \(K\) be a characteristic-zero field and put

\[
J=\begin{pmatrix}1&0\\0&-1\end{pmatrix},
\qquad
S=\begin{pmatrix}0&1\\1&0\end{pmatrix},
\qquad
\mathcal I=JS=\begin{pmatrix}0&1\\-1&0\end{pmatrix}.
\]

Thus \(J^2=S^2=I\), \(JS=-SJ\), and \(\mathcal I^2=-I\). Under the convention
that positive Clifford generators square to \(+I\), \(J,S\) present
\(\mathrm{Cl}_{2,0}\cong M_2(\mathbb R)\).

Define individual source reversals on \(M_2(K)\) by

\[
\alpha(A)=JAJ,\qquad \beta(A)=SAS,                         \tag{1}
\]

and their joint reversal by

\[
\Pi(A)=-\mathcal I A\mathcal I.                            \tag{2}
\]

Then:

1. \(\alpha\) and \(\beta\) are commuting involutive algebra automorphisms;
2. \(\alpha\beta=\beta\alpha=\Pi\);
3. \(\alpha(\mathcal I)=\beta(\mathcal I)=-\mathcal I\);
4. the joint fixed algebra is
   \[
   M_2(K)^\Pi=\{aI+b\mathcal I:a,b\in K\};                 \tag{3}
   \]
5. the independently fixed algebra is
   \[
   M_2(K)^\alpha\cap M_2(K)^\beta=\{aI:a\in K\}.           \tag{4}
   \]

Consequently, over \(\mathbb R\), joint reversal preserves a copy of \(\mathbb C\), whereas
requiring invariance under the two reversals independently preserves only \(\mathbb R\).

## Dependency-closed proof

Because \(J^2=I\),

\[
\alpha^2(A)=J(JAJ)J=(J^2)A(J^2)=A.
\]

Similarly \(\beta^2(A)=A\). For all \(A,B\),

\[
\alpha(AB)=JABJ=JA(J^2)BJ=(JAJ)(JBJ)=\alpha(A)\alpha(B),
\]

and the same calculation with \(S^2=I\) proves multiplicativity of \(\beta\). Both maps
fix \(I\), so they are involutive unital algebra automorphisms.

Using \(SJ=-JS=-\mathcal I\),

\[
\begin{aligned}
\alpha(\beta(A))
  &=J(SAS)J
    =(JS)A(SJ)
    =\mathcal I A(-\mathcal I)
    =-\mathcal I A\mathcal I
    =\Pi(A),\\
\beta(\alpha(A))
  &=S(JAJ)S
    =(SJ)A(JS)
    =(-\mathcal I)A\mathcal I
    =\Pi(A).
\end{aligned}
\]

This proves items 1--2. Moreover,

\[
\alpha(\mathcal I)=J(JS)J=SJ=-\mathcal I,
\qquad
\beta(\mathcal I)=S(JS)S=SJ=-\mathcal I,
\]

which proves item 3.

The formal parent already proves the exact centralizer/fixed-algebra identity

\[
\Pi(A)=A
\iff
A=aI+b\mathcal I
\]

for some \(a,b\in K\), proving item 4.

Suppose now that \(\alpha(A)=A\) and \(\beta(A)=A\). Then

\[
\Pi(A)=\alpha(\beta(A))=\alpha(A)=A.
\]

By item 4, \(A=aI+b\mathcal I\). Item 3 and linearity give

\[
\alpha(A)=aI-b\mathcal I.
\]

Since \(\alpha(A)=A\), comparison of the \((0,1)\) entries gives \(-b=b\). Characteristic zero
implies \(b=0\), so \(A=aI\).

Conversely, \(J(aI)J=aJ^2=aI\) and \(S(aI)S=aS^2=aI\), so every scalar matrix is fixed by both
individual reversals. This proves item 5 and the theorem. \(\square\)

## Hostile audit

### What is wrong

1. This is elementary fixed-subalgebra theory in
   \(\mathrm{Cl}_{2,0}\cong M_2(\mathbb R)\).
2. The grade involution and fixed even algebra are standard Clifford structures.
3. Fixed subspaces and inner automorphisms determined by Clifford gradings are established parent
   theory; see
   [Mosna--Miralles--Vaz](https://arxiv.org/abs/math-ph/0212020) and
   [Shirokov](https://arxiv.org/abs/2011.08287).
4. A volume element squaring to \(-1\) as a real complex-structure generator is also established;
   see [Hanson](https://arxiv.org/abs/1104.0399).
5. The two involutions, their admissibility, and their interpretation as source changes are
   supplied. Nothing here derives physical gauge equivalence.

Verdict: `REDISCOVERED / BRIDGE`.

### What survives

The theorem supplies a sharp finite discriminator:

```text
jointly quotiented real source ambiguity
  -> two-dimensional fixed scalar algebra;

independently quotiented real source ambiguities
  -> one-dimensional fixed scalar algebra.
```

This is stronger than merely generating a square root of \(-I\): it identifies exactly which
correlation in the supplied ambiguity group preserves the imaginary direction.

It does **not** prove:

- that physical amplitudes are fixed points of these reversals;
- that source-positive completion selects the joint subgroup;
- complex Hilbert-space quantum theory, positivity, or the Born rule;
- independent tensor composition;
- spacetime, gravity, gauge fields, or any force; or
- a new prediction.

## Lean obligations

The module formalizes exactly:

- `recordSourceReversal`;
- `pairSourceReversal`;
- `recordSourceReversal_involutive`;
- `pairSourceReversal_involutive`;
- `recordSourceReversal_mul`;
- `pairSourceReversal_mul`;
- `record_pair_sourceReversal_eq_sourcePairParity`;
- `pair_record_sourceReversal_eq_sourcePairParity`;
- `recordSourceReversal_sourceOrderedPair`;
- `pairSourceReversal_sourceOrderedPair`;
- `recordSourceReversal_sourceComplexScalar`;
- `pairSourceReversal_sourceComplexScalar`; and
- `individualSourceReversals_fixed_iff_scalar`.

No physical statement on the parent conjecture is authorized by this proof.

## Lean verification

Module:
`formal/GaloisForLFunctions/HTGeometry/SourceOrderedPairComplexStructure.lean`.

Direct foreground verification:

```text
lake env lean GaloisForLFunctions/HTGeometry/SourceOrderedPairComplexStructure.lean
```

completed with exit code zero and no warnings.

Focused final build:

```text
lake build GaloisForLFunctions.HTGeometry.SourceOrderedPairComplexStructure
✔ [1825/1825] Built GaloisForLFunctions.HTGeometry.SourceOrderedPairComplexStructure
Build completed successfully (1825 jobs).
```

`#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound` for
`recordSourceReversal_mul`, `record_pair_sourceReversal_eq_sourcePairParity`, and
`individualSourceReversals_fixed_iff_scalar`.

## Gates

- [x] exact statement and characteristic convention fixed
- [x] dependency-closed proof
- [x] graded-signature error corrected
- [x] external parent collision recorded
- [x] hostile verdict `REDISCOVERED / BRIDGE`
- [x] unconditional Lean formalization
- [x] direct source check, focused build, and axiom audit

## Log

- 2026-07-30 — paper proof closed after separating joint from independent source reversal.
- 2026-07-30 — hostile audit caught and corrected the graded signature:
  two \(+I\)-squaring generators give \(\mathrm{Cl}_{2,0}\) under the stated convention, not
  \(\mathrm{Cl}_{1,1}\).
- 2026-07-30 — classified as standard fixed-subalgebra/Clifford theory; retained only as the exact
  finite discriminator for the correlated-continuation conjecture.
- 2026-07-30 — exact theorem formalized unconditionally; direct source verification, focused
  `1825/1825` build, and axiom audit passed.
