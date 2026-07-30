# Ordered source pairing generates a complex structure

- **ID:** `source-ordered-pair-complex-structure`
- **Stage:** 3-formalized
- **Type:** EXACT FINITE BRIDGE / REAL CLIFFORD ALGEBRA / COMPOSITIONAL RELATIVITY
- **Scientific status:** `[LEAN-FORMALIZED] [STANDARD MATHEMATICS]`
  `[NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Parent:** `../../1-in-progress/dynamical-composition-universal-law.md`
- **Lean target:** `GaloisForLFunctions.HTGeometry.SourceOrderedPairComplexStructure`

## Statement

Over any field \(K\) of characteristic zero, define

\[
J=\begin{pmatrix}1&0\\0&-1\end{pmatrix},
\qquad
S=\begin{pmatrix}0&1\\1&0\end{pmatrix}.
\]

Then

\[
J^2=S^2=I,\qquad JS=-SJ.                                  \tag{1}
\]

Consequently the ordered product

\[
\mathcal I:=JS=
\begin{pmatrix}0&1\\-1&0\end{pmatrix}                     \tag{2}
\]

satisfies

\[
\boxed{\mathcal I^2=-I.}                                  \tag{3}
\]

Reversing the order reverses the generated complex structure:

\[
SJ=-\mathcal I.                                           \tag{4}
\]

More generally, for a selected paired transfer \(q=bS\),

\[
(Jq)^2=-b^2I.                                             \tag{5}
\]

Thus every nonzero selected transfer has a unique normalized projective representative \(S\)
whose ordered product with source polarity is a complex structure on the real two-channel
carrier.

Put \(\mathcal I=JS\). A matrix \(A\in M_2(K)\) commutes with \(\mathcal I\) exactly when

\[
A=
\begin{pmatrix}a&b\\-b&a\end{pmatrix}
=aI+b\mathcal I                                           \tag{6}
\]

for unique \(a,b\in K\). These matrices obey

\[
(aI+b\mathcal I)(cI+d\mathcal I)
=(ac-bd)I+(ad+bc)\mathcal I.                              \tag{7}
\]

For \(K=\mathbb R\), `(7)` is ordinary complex multiplication. Hence

\[
\operatorname{Cent}_{M_2(\mathbb R)}(\mathcal I)
\cong\mathbb C                                             \tag{8}
\]

as real unital algebras.

There is an intrinsic parity formulation of the same algebra. Define

\[
\Pi(A):=\mathcal I A\mathcal I^{-1}
=-\mathcal I A\mathcal I.                                 \tag{9}
\]

Then

\[
\Pi^2=1,\qquad
\Pi(AB)=\Pi(A)\Pi(B),\qquad
\Pi(J)=-J,\qquad
\Pi(S)=-S,                                                 \tag{10}
\]

and

\[
\boxed{
\Pi(A)=A
\iff
A\mathcal I=\mathcal IA
\iff
A=aI+b\mathcal I.
}
\tag{11}
\]

Thus the complex scalar algebra is exactly the even/fixed algebra under simultaneous reversal of
the two real Clifford generators.

## Joint versus independent reversal extension

Define the two individual source reversals

\[
\alpha(A)=JAJ,\qquad \beta(A)=SAS.                         \tag{12}
\]

They are commuting involutive algebra automorphisms and

\[
\alpha\beta=\beta\alpha=\Pi.                               \tag{13}
\]

Each acts as conjugation on the generated complex scalar plane:

\[
\alpha(aI+b\mathcal I)=\beta(aI+b\mathcal I)
=aI-b\mathcal I.                                          \tag{14}
\]

Consequently, over a characteristic-zero field,

\[
\boxed{
\operatorname{Fix}(\alpha)\cap\operatorname{Fix}(\beta)
=\{aI:a\in K\},
\qquad
\operatorname{Fix}(\alpha\beta)
=\{aI+b\mathcal I:a,b\in K\}.
}                                                          \tag{15}
\]

Thus the imaginary direction is invariant under joint reversal but odd under either reversal
separately. The complete paper proof, parent collision, and formal certificate are recorded in
[`joint-independent-source-reversal-fixed-algebra.md`](joint-independent-source-reversal-fixed-algebra.md).

## No-spectator selector extension

The individual fixed algebras are
\[
\operatorname{Fix}(\alpha)
=\left\{\begin{pmatrix}x&0\\0&y\end{pmatrix}\right\}
\cong\mathbb R\times\mathbb R,
\qquad
\operatorname{Fix}(\beta)
=\left\{\begin{pmatrix}a&b\\b&a\end{pmatrix}\right\}
\cong\mathbb R\times\mathbb R.
\]
Each contains a nontrivial idempotent. By contrast,
\(\operatorname{Fix}(\alpha\beta)\cong\mathbb C\) has only the idempotents \(0\) and \(1\).
Therefore joint reversal is the unique idempotent-indecomposable choice among the three
order-two source reversals. The exact paper proof and Lean certificate are recorded in
[`joint-reversal-no-spectator-selector.md`](joint-reversal-no-spectator-selector.md).

This remains standard real algebra. It conditionally selects joint reversal only after
idempotent indecomposability is required; it does not derive that requirement as physics.

## Proof

Direct matrix multiplication gives

\[
J^2=
\begin{pmatrix}1&0\\0&1\end{pmatrix}
=I,
\qquad
S^2=
\begin{pmatrix}1&0\\0&1\end{pmatrix}
=I.
\]

The two ordered cross-products are

\[
JS=
\begin{pmatrix}0&1\\-1&0\end{pmatrix},
\qquad
SJ=
\begin{pmatrix}0&-1\\1&0\end{pmatrix}
=-JS.
\]

Therefore

\[
(JS)^2=J(SJ)S=J(-JS)S=-J^2S^2=-I.
\]

For \(q=bS\), scalar centrality gives

\[
(Jq)^2=(bJS)^2=b^2(JS)^2=-b^2I.
\]

Finally, write \(A=(a_{ij})\). Direct multiplication gives

\[
A\mathcal I=
\begin{pmatrix}-a_{01}&a_{00}\\-a_{11}&a_{10}\end{pmatrix},
\qquad
\mathcal IA=
\begin{pmatrix}a_{10}&a_{11}\\-a_{00}&-a_{01}\end{pmatrix}.
\]

Thus \(A\mathcal I=\mathcal IA\) exactly when
\(a_{10}=-a_{01}\) and \(a_{11}=a_{00}\), proving `(6)` and uniqueness. Expanding the product in
`(6)` and using \(\mathcal I^2=-I\) gives `(7)`. The real-linear bijection
\(a+ib\mapsto aI+b\mathcal I\) preserves the unit and multiplication by `(7)`, proving `(8)`.

Since \(\mathcal I^{-1}=-\mathcal I\), `(9)` is conjugation and therefore preserves
multiplication. Applying it twice gives

\[
\Pi^2(A)=\mathcal I^2A\mathcal I^{-2}=A.
\]

Anticommutation of \(\mathcal I\) with \(J\) and \(S\) gives the final two identities in `(10)`.
Finally,

\[
\Pi(A)=A
\iff
-\mathcal IA\mathcal I=A
\iff
\mathcal IA=A\mathcal I,
\]

where the last equivalence follows by multiplying by \(\mathcal I\) and using
\(\mathcal I^2=-I\). Equation `(6)` then proves `(11)`.

This proves `(1)`--`(11)`.

## Exact relation to the source selector

The upstream paper and Lean results prove:

1. primitive record data alone admit inequivalent paired and self-composition tensors;
2. a nonzero symmetric tensor odd under \(J\) has the form \(q=bS\);
3. all such nonzero tensors lie in the paired projective congruence orbit; and
4. the paired transfer generates its unit ray through \(q^2=b^2I\) over a real field, or
   \(q^\dagger q=|b|^2I\) over \(\mathbb C\).

The present theorem adds the ordered consequence:

```text
retained/created source polarity J
  + source-selected paired composition S
  + order of application
  -> generated complex structure I = JS.
```

This is the first exact finite shadow in the current programme where an operator squaring to
\(-1\) is generated from two real source operations rather than inserted as a scalar.

## Scientific boundary

The result is the standard two-positive-generator presentation of the graded real Clifford algebra
\(\mathrm{Cl}_{2,0}\cong M_2(\mathbb R)\). It is not a new mathematical theorem. Although
\(\mathrm{Cl}_{1,1}\) is isomorphic to the same ungraded matrix algebra, it has a different
signature and even subalgebra; it is not the graded presentation used here.

It does **not** derive:

- the scalar field \(\mathbb C\);
- central multiplication by \(i\);
- a complex Hilbert space;
- a dagger or positive inner product;
- the Born rule;
- a qubit state cone;
- independent tensor composition;
- time, spacetime, gravity, or a gauge force.

In particular, \(\mathcal I\) is central only in its commutant `(8)`, not in the full algebra
generated by \(J\) and \(S\), which is \(M_2(\mathbb R)\). The generators \(J\) and \(S\)
anticommute with the induced complex orientation. Calling `(3)` or `(8)` a derivation of complex
quantum mechanics would be false: one must still prove that physical amplitudes are exactly
\(\mathcal I\)-preserving operations.

## Positive research consequence

The bridge narrows the next theorem target.

It is no longer necessary to assume either an imaginary generator or its local scalar algebra
merely to obtain phase orientation. The missing theorem is instead:

> prove that source-positive extension composition restricts physical amplitudes to the commutant
> of the generated \(\mathcal I\), while \(J\) and \(S\) survive only as event-changing
> operations, then prove that independent composition excludes real and quaternionic alternatives.

This would connect the generated real complex structure to ordinary complex quantum theory.
Hanche--Olsen and local-tomographic Jordan reconstruction results can only be used after the
independent composite is source-derived; taking local tomography as an axiom would insert the
needed exclusion.

One concrete physical candidate is **source neutrality**: scalar reports may have to remain
invariant under simultaneous reversal of the two open real event generators. Equations
`(9)`--`(11)` would then force their algebra to be complex. This is a conjectural physical typing
of the parity theorem, not part of the theorem.

## Novelty and anti-theatre verdict

- `[NOVELTY — FAIL]` Equation `(3)` is elementary Clifford algebra.
- `[ANTI-THEATRE — PASS]` The card labels the result as a standard bridge and states the
  centrality, positivity, and independent-composition gaps explicitly.
- `[PROGRAMME VALUE — PASS]` The bridge removes “assume complex phase” from the first finite
  construction, identifies the full local phase commutant, and exposes the exact stronger
  obligation.
- `[PHYSICS — NOT PROVED]` No physical identification is claimed.

## Lean verification

Module:
`formal/GaloisForLFunctions/HTGeometry/SourceOrderedPairComplexStructure.lean`.

It proves unconditionally:

- `recordPolarityMatrix_mul_self`;
- `pairRecordMatrix_mul_self`;
- `recordPolarity_pair_anticommute`;
- `sourceOrderedPairComplexStructure_sq`;
- `pair_recordPolarity_eq_neg_sourceOrderedPair`;
- `sourceOrderedScaledPair_sq`; and
- `oddSymmetricRecord_ordered_sq`;
- `sourceComplexScalar_mul`;
- `sourceComplexScalar_commute`;
- `sourceComplexScalar_pair_injective`;
- `commutes_sourceOrderedPair_iff`;
- `sourcePairParity_eq_conjugation`;
- `sourcePairParity_involutive`;
- `sourcePairParity_mul`;
- `sourcePairParity_recordPolarity`;
- `sourcePairParity_pairRecord`;
- `sourcePairParity_fixed_iff_complexScalar`; and
- `sourcePairParity_fixed_iff_commutes`;
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

Direct source verification:

```text
lake env lean GaloisForLFunctions/HTGeometry/SourceOrderedPairComplexStructure.lean
```

completed with exit code zero and no warnings. Focused final build:

```text
lake build GaloisForLFunctions.HTGeometry.SourceOrderedPairComplexStructure
✔ [1825/1825] Built GaloisForLFunctions.HTGeometry.SourceOrderedPairComplexStructure
Build completed successfully (1825 jobs).
```

`#print axioms` from `/tmp/SourceOrderedPairComplexStructureAxioms.lean` reports only
`propext`, `Classical.choice`, and `Quot.sound` for the ordered-square, selected odd-square, and
centralizer, parity-multiplicativity, parity-fixed-algebra, individual-reversal multiplicativity,
joint-composite, and independently-fixed-scalar theorems.

Repository `scripts/formal_tools.py lint` was run. It fails on a pre-existing set of unwired
RHTower and HTGeometry modules in the current dirty worktree. This module is imported by
`GaloisForLFunctions/HTGeometry.lean` and is not among the reported unreachable modules. No
unrelated umbrella work was modified.

## Gates

- [x] dependency-closed paper proof
- [x] relation to source selector stated without adding physical assumptions
- [x] real Clifford parent identified
- [x] central-complex-scalar false inference blocked
- [x] unconditional Lean formalization
- [x] direct source verification
- [x] final module build and axiom audit
- [ ] repository formal lint (blocked by unrelated pre-existing unreachable modules)
- [ ] source-derived centrality theorem
- [ ] source-derived independent-composition theorem

## Log

- 2026-07-30 — extracted after the compositional-relativity revision: ordered multiplication of
  the real source polarity and selected paired transfer generates a square root of \(-I\).
- 2026-07-30 — classified as standard \(\mathrm{Cl}_{2,0}\) bridge, not new scientific knowledge;
  retained because it identifies the exact centrality/local-composition gap.
- 2026-07-30 — corrected the graded Clifford signature from \(\mathrm{Cl}_{1,1}\) to
  \(\mathrm{Cl}_{2,0}\): both source generators square to \(+I\); the shared ungraded
  \(M_2(\mathbb R)\) realization had hidden the distinction.
- 2026-07-30 — formalized the involution, anticommutation, ordered square, reversed-order sign,
  scaled square, and source-selected odd-tensor square theorems; direct source check passed.
- 2026-07-30 — proved the exact centralizer classification and complex multiplication law on
  paper and in Lean; repeated direct source check passed without warnings.
- 2026-07-30 — focused module build and axiom audit passed; repository lint remains red only on
  unrelated pre-existing umbrella reachability failures.
- 2026-07-30 — identified the complex commutant as the fixed algebra of generated Clifford parity;
  formalized parity conjugation, involutivity, multiplicativity, generator reversal, and exact
  fixed-algebra/centralizer classification; repeated direct source check, focused build, and axiom
  audit passed.
- 2026-07-30 — formalized the joint-versus-independent sharpening: both individual reversals act
  as complex conjugation, their common fixed algebra is scalar, and their composite fixed algebra
  is the full generated complex plane.
