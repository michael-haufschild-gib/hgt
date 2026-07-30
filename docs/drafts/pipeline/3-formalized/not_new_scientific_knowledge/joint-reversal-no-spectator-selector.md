# Joint reversal is the unique idempotent-indecomposable source-reversal quotient

- **ID:** `joint-reversal-no-spectator-selector`
- **Stage:** 3-formalized
- **Type:** EXACT FINITE FIXED-ALGEBRA CLASSIFICATION / SOURCE-SELECTION BRIDGE
- **Scientific status:** `[LEAN-PROVED] [STANDARD ALGEBRA] [BRIDGE]`
  `[NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Parent conjecture:**
  `../../1-in-progress/correlated-continuation-ambiguity-law.md`
- **Formal parent:**
  `../../3-formalized/not_new_scientific_knowledge/joint-independent-source-reversal-fixed-algebra.md`
- **Lean target:**
  `GaloisForLFunctions.HTGeometry.SourceReversalNoSpectatorSelector`

## Statement

In \(M_2(\mathbb R)\), let
\[
J=\begin{pmatrix}1&0\\0&-1\end{pmatrix},\qquad
S=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
\mathcal I=JS=\begin{pmatrix}0&1\\-1&0\end{pmatrix},
\]
and define
\[
\alpha(A)=JAJ,\qquad
\beta(A)=SAS,\qquad
\Pi(A)=-\mathcal I A\mathcal I=\alpha\beta(A).
\]
Then
\[
\begin{aligned}
\operatorname{Fix}(\alpha)
  &=\left\{\begin{pmatrix}x&0\\0&y\end{pmatrix}:x,y\in\mathbb R\right\}
    \cong\mathbb R\times\mathbb R,\\
\operatorname{Fix}(\beta)
  &=\left\{\begin{pmatrix}a&b\\b&a\end{pmatrix}:a,b\in\mathbb R\right\}
    \cong\mathbb R\times\mathbb R,\\
\operatorname{Fix}(\Pi)
  &=\left\{\begin{pmatrix}a&b\\-b&a\end{pmatrix}:a,b\in\mathbb R\right\}
    \cong\mathbb C.
\end{aligned}                                                     \tag{1}
\]

The first two fixed algebras contain nontrivial idempotents. The joint fixed algebra contains only
the idempotents \(0\) and \(1\). Consequently, among the three order-two source-reversal subgroups
\(\langle\alpha\rangle\), \(\langle\beta\rangle\), and \(\langle\alpha\beta\rangle\), joint reversal
is the unique choice whose fixed algebra has no nontrivial idempotent decomposition.

## Dependency-closed proof

Write
\[
A=\begin{pmatrix}x&u\\v&y\end{pmatrix}.
\]
Direct multiplication gives
\[
\alpha(A)=\begin{pmatrix}x&-u\\-v&y\end{pmatrix},\qquad
\beta(A)=\begin{pmatrix}y&v\\u&x\end{pmatrix}.
\]
Thus \(\alpha(A)=A\) exactly when \(u=v=0\), and \(\beta(A)=A\) exactly when
\(x=y\) and \(u=v\). This proves the first two classifications in `(1)`.

The formal parent proves
\[
\Pi(A)=A
\quad\Longleftrightarrow\quad
A=aI+b\mathcal I
=\begin{pmatrix}a&b\\-b&a\end{pmatrix}
\]
for unique \(a,b\in\mathbb R\), proving the third classification.

The matrix
\[
P_J=\begin{pmatrix}1&0\\0&0\end{pmatrix}
\]
is fixed by \(\alpha\), satisfies \(P_J^2=P_J\), and is neither \(0\) nor \(1\). Likewise
\[
P_S=\frac12\begin{pmatrix}1&1\\1&1\end{pmatrix}
\]
is fixed by \(\beta\), satisfies \(P_S^2=P_S\), and is neither \(0\) nor \(1\).

It remains to classify idempotents fixed by \(\Pi\). Let \(A=aI+b\mathcal I\). Since
\(\mathcal I^2=-I\),
\[
A^2=(a^2-b^2)I+2ab\mathcal I.
\]
Injectivity of the two scalar coordinates turns \(A^2=A\) into
\[
a^2-b^2=a,\qquad 2ab=b.                                  \tag{2}
\]
If \(b=0\), then \(a^2=a\), hence \(a=0\) or \(a=1\), giving \(A=0\) or \(A=1\).
If \(b\ne0\), the second equation in `(2)` gives \(2a=1\). Substitution into the first gives
\[
b^2=-\frac14,
\]
impossible over \(\mathbb R\). Therefore the joint fixed algebra has only trivial idempotents.
\(\square\)

## Hostile audit

### What is already known

1. These are elementary fixed-subalgebra calculations in
   \(\mathrm{Cl}_{2,0}\cong M_2(\mathbb R)\).
2. The distinction \(\mathbb R\times\mathbb R\) versus \(\mathbb C\) is the elementary split
   versus nonsplit quadratic-algebra distinction.
3. Relational encodings, global versus local superselection rules, and survival of relative
   degrees under correlated rather than independent reference-frame averaging are established
   quantum-information theory; see
   [Bartlett--Rudolph--Spekkens](https://arxiv.org/abs/quant-ph/0610030).
4. Fixed points under a supplied group action do not explain why that action, subgroup, or
   quotient is physically admissible.

Verdict: `STANDARD / BRIDGE`.

### Strongest positive survivor

The earlier finite bridge supplied joint reversal by hand. This theorem adds one exact conditional
selector:

```text
require the fixed report algebra to contain no nontrivial spectator idempotent
  -> reject either individual source reversal
  -> retain joint source reversal
  -> obtain the generated complex scalar algebra.
```

The source pair distinguishes the joint subgroup algebraically; no tensor split or complex scalar
field is needed for this finite classification.

This does **not** derive the no-spectator requirement from source-positive physics. It also does
not derive amplitudes, positivity, the Born rule, Hilbert composition, spacetime, forces, or a
prediction. Those are the physical open core.

## Lean obligations

Formalized unconditionally:

1. entrywise formulas for `recordSourceReversal` and `pairSourceReversal`;
2. both individual fixed-algebra classifications;
3. explicit nontrivial fixed idempotents for each individual reversal;
4. trivial-idempotent classification for the joint fixed algebra over \(\mathbb R\); and
5. one conjunction stating that joint reversal is the only idempotent-indecomposable choice among
   the three source reversals.

No physical interpretation is eligible for Lean.

## Lean certificate

Module:
`formal/GaloisForLFunctions/HTGeometry/SourceReversalNoSpectatorSelector.lean`.

Exact declarations:

- `recordSourceReversal_apply`;
- `pairSourceReversal_apply`;
- `recordSourceReversal_fixed_iff_splitScalar`;
- `pairSourceReversal_fixed_iff_splitScalar`;
- `recordFixedSector_fixed`;
- `pairFixedSector_fixed`;
- `recordFixedSector_idempotent`;
- `pairFixedSector_idempotent`;
- `sourcePairParity_fixed_idempotent_eq_zero_or_one`; and
- `jointSourceReversal_only_idempotentIndecomposable`.

Direct foreground verification:

```text
lake env lean GaloisForLFunctions/HTGeometry/SourceReversalNoSpectatorSelector.lean
```

completed with exit code zero and no warnings.

Focused final build:

```text
lake build GaloisForLFunctions.HTGeometry.SourceReversalNoSpectatorSelector
✔ [1833/1833] Built GaloisForLFunctions.HTGeometry.SourceReversalNoSpectatorSelector
Build completed successfully (1833 jobs).
```

`#print axioms` for both fixed-algebra classifications, the joint trivial-idempotent theorem, and
the final selector conjunction reports only `propext`, `Classical.choice`, and `Quot.sound`.
The repository formal lint passed; only pre-existing large-file warnings were emitted.

An additional direct check of the umbrella `GaloisForLFunctions/HTGeometry.lean` stopped before
checking imports because the unrelated cached
`MultipleEllipticGammaHypertranscendence.olean` had an incompatible header. No process from this
audit remained. The focused module build above is green; no umbrella-build claim is made.

## Gates

- [x] exact statement
- [x] dependency-closed paper proof
- [x] parent collision and hostile verdict
- [x] strongest positive survivor extracted
- [x] unconditional Lean formalization
- [x] direct source verification, focused final build, and axiom audit

## Log

- 2026-07-30 — extracted after the joint/independent fixed-algebra theorem and the
  reference-frame/superselection collision.
- 2026-07-30 — identified idempotent indecomposability as a finite source-internal discriminator:
  individual reversals leave split spectator sectors; joint reversal leaves the complex plane.
- 2026-07-30 — classified as standard algebra and retained only as a bridge toward a still-missing
  source-derived no-spectator law.
- 2026-07-30 — exact fixed-algebra, idempotent, and selector statements formalized unconditionally;
  direct source check, focused `1833/1833` build, axiom audit, and formal lint passed.
- 2026-07-30 — recorded unrelated stale-olean boundary encountered only by the optional umbrella
  direct check; did not delete caches or expand scope.
