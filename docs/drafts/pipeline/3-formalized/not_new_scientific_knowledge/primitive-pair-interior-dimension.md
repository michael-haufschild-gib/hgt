# Universal primitive-pair interior fusion forces two complex components

- **ID:** `primitive-pair-interior-dimension`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Status:** `[FULLY-LEAN-PROVED] [CLASSICAL] [BRIDGE]`
- **Paper parent:**
  `../../2-fully-proven/not_new_scientific_knowledge/balanced-causal-fracture-torsor-classification.md`
- **Physics parent:**
  `../../1-in-progress/forbidden-transition-causalization-universal-law.md`
- **Lean module:** `GaloisForLFunctions.HTGeometry.PrimitivePairInteriorDimension`
- **Statement:** For every \(q\ge2\), every linearly independent pair of primitive roots in
  \(\mathbb C^q\) has positive-definite Gram sum if and only if \(q=2\).

## Exact theorem

For \(u\in\mathbb C^q\), define its primitive Gram record by
\[
R_q(u)_{ij}=\overline{u_i}u_j.
\tag{1}
\]
Define
\[
\operatorname{PrimitivePairInterior}(q)
\quad\Longleftrightarrow\quad
\forall u,v\in\mathbb C^q,\quad
\operatorname{LinearIndependent}_{\mathbb C}(u,v)
\Longrightarrow
R_q(u)+R_q(v)>0.
\tag{2}
\]
Lean proves unconditionally:
\[
\boxed{
q\ge2
\Longrightarrow
\bigl(\operatorname{PrimitivePairInterior}(q)\iff q=2\bigr).
}
\tag{3}
\]

For \(q=2\), independence makes the alternating determinant nonzero; the existing
colour-Gram null-fusion theorem then makes the sum positive definite. For every
\(q=n+3\), the first two coordinate roots are independent, but their Gram sum annihilates the
third coordinate root. This gives one proof for arbitrary higher dimension, not an encoded finite
table.

## Lean declarations

- `primitiveRootGram`;
- `primitiveRootPair`;
- `PrimitivePairInterior`;
- `primitiveRootGram_finTwo_eq_colorGram`;
- `primitivePairInterior_finTwo`;
- `primitiveCoordinatePair_linearIndependent`;
- `primitiveRootGram_mulVec`;
- `primitiveCoordinateRootGram_mulVec_of_ne`;
- `not_primitivePairInterior_finAddThree`; and
- `primitivePairInterior_fin_iff`.

Direct `lake env lean` checking passes. `#print axioms` reports only `propext`,
`Classical.choice`, and `Quot.sound`. Proof uses no `sorry`, `admit`, declared axiom, opaque
declaration, unsafe declaration, or computation.

## Meaning and boundary

Exact new corpus fact:

> Two independent primitive possibilities always eliminate every unseen direction only when the
> public record has two complex components.

Via \(H_2(\mathbb C)_{++}\cong\{(t,\mathbf x):t>\|\mathbf x\|\}\), two complex components carry a
four-real-dimensional Lorentz future. Thus a source principle requiring every independent
primitive pair to create a fully interior future would select \(3+1\) causal dimension without
assuming it.

This interpretation is conditional. The theorem does **not** derive condition `(2)` from physical
reality, prove that Gram records are spacetime, establish gravity, prove arbitrary-boundary strict
convexity in Lean, or formalize the \(SU(3)\)-torsor classification. Those remain open parent
gates.

## Gates

- [x] dependency-closed paper theorem
- [x] genuine arbitrary-dimension Lean proof
- [x] direct `lake env lean` check
- [x] standard-axiom audit
- [ ] full arbitrary-boundary elementary-future theorem in Lean
- [ ] free/transitive \(SU(3)\) regular-fibre theorem in Lean
- [ ] source-law derivation of primitive-pair completeness
- [ ] physical prediction and Nature eligibility

## Log

- 2026-07-30 — formalized exact \(q\ge2\) iff classification without computation or dimension
  table encoding.
