# Additive positive groupoid-cost triviality and directed-history necessity law

- **ID:** ULF-HISTORY-1
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** weighted-history-groupoid ontology attack
- **Statement:** Every nonnegative additive cost on a groupoid is identically zero; nontrivial proof cost requires irreversible or subadditive history structure beyond the reversible core.
- **Status:** [PAPER-PROVED] [ROUTE-INDEPENDENT] [POSITIVE SURVIVOR] [NO LEAN]

## 1. Theorem

Let \(\mathcal G\) be a groupoid and let

\[
A:\operatorname{Mor}(\mathcal G)\longrightarrow[0,\infty)
\]

satisfy

\[
A(1_x)=0,
\qquad
A(g\circ f)=A(g)+A(f)
\tag{1}
\]

whenever \(g\circ f\) is defined. Then \(A\equiv0\).

### Proof

For every arrow \(g:x\to y\), the inverse \(g^{-1}:y\to x\) exists and

\[
0=A(1_x)=A(g^{-1}\circ g)=A(g^{-1})+A(g).
\]

Both terms are nonnegative, so both vanish. Thus \(A(g)=0\) for every arrow \(g\). QED.

## 2. Complex-weight corollary

Suppose \(W=A+iM\) is an additive \(\mathbb C\)-valued groupoid cocycle and
\(A=\operatorname{Re}W\ge0\). Then \(A=0\). Therefore one additive complex cocycle on a reversible
history groupoid cannot simultaneously encode nontrivial nonnegative proof cost and reversible phase.

The imaginary component \(M\) may remain a nontrivial additive character, because it changes sign
under inversion rather than remaining nonnegative.

## 3. Strongest positive survivor

A history-based universal field must separate two compositional regimes:

1. a reversible core carrying phase, holonomy, character, and recurrence data;
2. an irreversible or lax layer carrying cost, dissipation, filling volume, or complexity.

At least one of the following changes is necessary for nonzero cost:

- replace the groupoid by a directed category with noninvertible arrows;
- weaken equality in (1) to subadditivity \(A(gf)\le A(g)+A(f)\);
- use a symmetric length \(A(g^{-1})=A(g)\), which cannot be an additive cocycle;
- retain an oriented positive cone of histories before groupoid completion.

This is not a new slot list: the incompatibility theorem forces the polarization between reversible
memory and irreversible cost.

## 4. Representation lesson

The naive weighted-history-groupoid candidate fails. The stronger candidate is a polarized directed
history structure whose reversible core and irreversible completion interact through a theorem, not
an arbitrary product. A double category, equipment, or causal dagger category is only a container;
the open mathematical question is which universal exchange law couples its two compositions.

## 5. Sharp scope

- Signed additive actions on groupoids can be nonzero; nonnegativity is load-bearing.
- A norm or word length can be nonzero on a group because it is subadditive, not additive.
- The theorem does not construct the required polarized history structure.
- No novelty claim is made for the elementary proof. Its role is to kill a tempting universal
  ontology and force a stronger representation.

## Log

- 2026-08-09 — groupoid single-weight conjecture killed; directed-history survivor extracted.
