# Failure-antichain semantic quotient and stable primitive-spectrum law

- **ID:** ULF-SELM-6
- **Stage:** 2-fully-proven
- **Type:** ROUTE-INDEPENDENT PRESENTATION-REDUCTION THEOREM
- **Status:** [PAPER-PROVED] [DEPENDENCY-CLOSED] [SEMANTIC QUOTIENT]
  [STABLE REDUNDANCY] [LEAN TARGET] [NOT MORITA INVARIANCE] [NOT RH]
- **Parents:** ULF-SELM-1--5

## 1. Purpose

Relabeling invariance still leaves Symbolic--Execution Law Mechanics dependent on a raw list of
failure kernels.  This card identifies a larger class of harmless presentation moves.  A kernel
containing an already declared smaller kernel imposes no new nonnegative local inequality.  More
generally, two failure families have identical symbolic, executable, splitting, primitive, and
gap semantics whenever each family dominates the other by inclusion.

The mechanism therefore descends from presented hypergraphs to their failure-antichain semantics.
This is the first noninvertible presentation reduction in SELM.

## 2. Domination and semantic equivalence

For finite failure families `H,G` on the same coordinate set, define

\[
 H\succeq G
 \quad:\Longleftrightarrow\quad
 \forall L\in G\;\exists K\in H\;(K\subseteq L).
 \tag{FA.1}
\]

Call `H` and `G` semantically equivalent, written `H\asymp G`, when both `H\succeq G` and
`G\succeq H` hold.  This is not equality of presentations.  It says each test in either family is
implied by a possibly smaller test in the other.

## 3. Semantic-quotient theorem

### Theorem 3.1 -- domination transports local admission

If `H\succeq G`, then

\[
 \boxed{\operatorname{Local}_H(m,a)\Longrightarrow
        \operatorname{Local}_G(m,a).}
 \tag{FA.2}
\]

### Proof

Fix `L\in G` and choose `K\in H` with `K\subseteq L`.  Local admission for `H` gives

\[
 m\leq\sum_{i\in K}a_i.
\]

Because every `a_i` is a natural number,

\[
 \sum_{i\in K}a_i\leq\sum_{i\in L}a_i.
\]

Therefore the inequality for `L` holds. ∎

### Corollary 3.2 -- local semantics factors through `\asymp`

If `H\asymp G`, then

\[
 \boxed{\operatorname{Local}_H(m,a)\iff\operatorname{Local}_G(m,a).}
 \tag{FA.3}
\]

### Theorem 3.3 -- all SELM predicates factor through `\asymp`

If `H\asymp G`, then for every `m,a`:

\[
\begin{aligned}
 \operatorname{Exec}_H(m,a)&\iff\operatorname{Exec}_G(m,a),\\
 \operatorname{Split}_H(m,a)&\iff\operatorname{Split}_G(m,a),\\
 \operatorname{Primitive}_H(m,a)&\iff\operatorname{Primitive}_G(m,a),\\
 \bigl(\operatorname{Local}_H(m,a)\wedge\neg\operatorname{Exec}_H(m,a)\bigr)
  &\iff
 \bigl(\operatorname{Local}_G(m,a)\wedge\neg\operatorname{Exec}_G(m,a)\bigr).
\end{aligned}
\tag{FA.4}
\]

Consequently

\[
 \boxed{\operatorname{Spec}_{\rm prim}(H)=
        \operatorname{Spec}_{\rm prim}(G).}
 \tag{FA.5}
\]

### Proof

An executable witness is the same finite family of weights on both sides; only grade-one local
admission changes, and `(FA.3)` identifies it.  A dominated split uses the same grades, weights,
and coordinatewise domination; `(FA.3)` identifies the two local premises.  Primitivity is positive
local admission plus absence of such a split.  The gap statement combines the local and executable
equivalences.  Finally transport the same primitive witness in both directions to obtain `(FA.5)`.
∎

## 4. Stable-redundancy corollary

Let `K_0\in H` and `K_0\subseteq L`.  Then

\[
 \boxed{H\asymp(H\cup\{L\}).}
 \tag{FA.6}
\]

Indeed, every old kernel witnesses itself; the new kernel `L` is witnessed by `K_0`.  Therefore
adding or deleting any failure constraint dominated by an existing one preserves every predicate
and the primitive spectrum in Theorem 3.3.

This move is noninvertible on raw presentations: the enlarged family contains more data.  It is an
isomorphism only after passing to SELM semantics.

## 5. Constitutive law and interpretation

### SELM Law VI -- antichain reduction precedes execution analysis

Failure presentations carry a semantic preorder.  All local/executable discrepancy, primitive
genesis, bounded-grammar obstruction, and primitive-degree data descend to the quotient by mutual
domination.  Superset constraints are presentation gauge, not new laws.

This sharpens the field's ontology:

1. raw failure lists are charts;
2. mutual domination is the first semantic equivalence relation;
3. primitive spectrum is an invariant on that quotient;
4. cofinal primitive escape cannot be manufactured by adding dominated constraints;
5. any corpus realization must specify its irredundant failure-antichain semantics before its
   primitive spectrum can be compared with another realization.

## 6. Sharp boundaries

1. Nonnegative weights are load-bearing.  With signed weights, enlarging a kernel can lower its
   sum and domination need not imply `(FA.2)`.
2. Mutual domination preserves the declared SELM predicates, not arbitrary topology, completion,
   orientation, coefficient labels, or source history.
3. Equal primitive spectra alone do not imply mutual domination.
4. This is stronger than relabeling but weaker than Tietze, derived, or Morita invariance.
5. Quotienting coordinates, duplicating resources, and changing the coefficient semiring remain
   open presentation moves.
6. No corpus route is credited until its source map lands in this semantic quotient before endpoint
   specialization.
7. No RH statement occurs.

## 7. Lean target

Formalize in

`formal/GaloisForLFunctions/HTGeometry/ConstitutiveFailureAntichainQuotient.lean`

without project axioms, `sorry`, `admit`, `opaque`, `unsafe`, or computation proofs.  Certify:

1. failure-family domination and mutual semantic equivalence;
2. local-admission monotonicity and equivalence;
3. executable, dominated-split, primitive, and exact-gap equivalence;
4. primitive-degree occurrence equivalence;
5. dominated-superset insertion as a noninvertible stable presentation move;
6. one unconditional capstone imported by `HTGeometry.UniversalLawField`.

## Log

- 2026-08-10 -- extracted as the stable-presentation successor to ULF-SELM-5.  Paper proof is
  dependency-closed.  Lean certification pending.
