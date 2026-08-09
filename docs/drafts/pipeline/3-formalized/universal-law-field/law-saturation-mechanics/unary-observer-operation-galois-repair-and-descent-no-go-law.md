# Unary observer-operation Galois repair and descent no-go law

- **ID:** ULF-LSM-2
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean-certified)
- **Source:** universal algebraic core of Law-Saturation Mechanics
- **Statement:** Every family of unary source laws forces a canonical least observer-equivalence
  repair; every quotient retaining those laws factors through that repair, and any offending law
  cannot descend without changing the law or the observer commitment.
- **Status:** [PROVED HERE] [DEPENDENCY CLOSED] [MECHANISM FIRST] [CLASSICAL UNIVERSAL-ALGEBRA
  CORE] [LEAN-CERTIFIED] [NO PROJECT AXIOMS] [NOT RH]

## Goal

Replace the slogan “observer loses information” by a universal construction that computes the exact
loss forced by retaining source laws.

## 1. Setup

Let \(A\) be a set, \(F\subseteq A^A\) a family of unary source operations, and
\(E\subseteq A\times A\) a declared observer relation. A relation \(R\) is **\(F\)-executable** if

1. \(R\) is an equivalence relation;
2. \(E\subseteq R\);
3. every \(f\in F\) preserves \(R\):

\[
  xRy\Longrightarrow f(x)R f(y).
  \tag{1}
\]

Define

\[
  \operatorname{Cg}_F(E)
  =\bigcap\{R:R\text{ is }F\text{-executable}\}.
  \tag{2}
\]

Equivalently,

\[
 x\operatorname{Cg}_F(E)y
 \Longleftrightarrow
 \text{every executable }R\supseteq E\text{ relates }x,y.
 \tag{3}
\]

No existence hypothesis is needed: the universal relation is executable.

## 2. The theorem

### Theorem 2.1 — least executable repair

For every \(A,F,E\):

1. \(\operatorname{Cg}_F(E)\) is an equivalence relation.
2. \(E\subseteq\operatorname{Cg}_F(E)\).
3. Every \(f\in F\) preserves \(\operatorname{Cg}_F(E)\).
4. If \(R\) is any \(F\)-executable relation, then

   \[
     \operatorname{Cg}_F(E)\subseteq R.
     \tag{4}
   \]

Thus (2) is the unique least observer repair retaining every source law.

### Theorem 2.2 — fixed-point criterion

If \(E\) is already an equivalence relation, then

\[
  \operatorname{Cg}_F(E)=E
  \quad\Longleftrightarrow\quad
  \text{every }f\in F\text{ preserves }E.
  \tag{5}
\]

Hence executable observer doctrines are exactly the fixed points of law repair.

### Theorem 2.3 — quotient factorization and no-descent

Let \(q:A\to B\), and put

\[
  K_q(x,y)\Longleftrightarrow q(x)=q(y).
  \tag{6}
\]

Assume \(E\subseteq K_q\). If every \(f\in F\) has a descended operation
\(\bar f:B\to B\) satisfying

\[
  qf=\bar f q,
  \tag{7}
\]

then

\[
  \operatorname{Cg}_F(E)\subseteq K_q.
  \tag{8}
\]

Equivalently, \(q\) is constant on every class forced by the canonical repair, so it factors
set-theoretically through

\[
  A\longrightarrow A/\operatorname{Cg}_F(E).
  \tag{9}
\]

For one operation \(f\), the following are equivalent:

1. there exists \(\bar f:B\to B\) with (7);
2. \(f\) preserves \(K_q\).

Therefore, if \(f\) does not preserve the observer kernel, no operation on the same observer output
can make \(q\) a homomorphism for \(f\).

### Theorem 2.4 — exact repair dichotomy under fixed commitments

Fix both commitments:

- all identifications in \(E\) must remain;
- all source operations in \(F\) must remain executable.

Then every valid observer kernel contains \(\operatorname{Cg}_F(E)\). If the current observer kernel
\(K\) does not contain that closure, no repair preserving both commitments exists. One must change at
least one commitment:

1. remove every offending operation from the admitted law family; or
2. enlarge the observer kernel to an \(F\)-executable relation, minimally
   \(\operatorname{Cg}_F(E)\).

This is exhaustive relative to the two fixed commitments. Refining the observer so that it no longer
identifies \(E\), adding a marked lift, or changing the carrier abandons the stated problem and is not
silently counted as a third repair.

### Theorem 2.5 — monotonicity of law admission

If \(F\subseteq G\) and \(E\subseteq E'\), then

\[
  \operatorname{Cg}_F(E)
  \subseteq
  \operatorname{Cg}_G(E').
  \tag{10}
\]

Adding legal operations or mandatory identifications can only erase further distinctions.

## 3. Proof

### Proof of Theorem 2.1

An intersection of equivalence relations is an equivalence relation, proving item 1. Every relation
in the intersection contains \(E\), proving item 2.

Let \(f\in F\) and suppose \(x\operatorname{Cg}_F(E)y\). For every executable relation \(R\),
definition (3) gives \(xRy\). Since \(f\) preserves \(R\), we get \(f(x)Rf(y)\). This holds for
every executable \(R\), hence \(f(x)\operatorname{Cg}_F(E)f(y)\), proving item 3.

Every executable \(R\) is one of the relations intersected in (2), so the intersection is contained
in \(R\). This proves item 4 and uniqueness of the least repair. ∎

### Proof of Theorem 2.2

If every \(f\in F\) preserves the equivalence \(E\), then \(E\) itself is executable. Leastness
gives \(\operatorname{Cg}_F(E)\subseteq E\), while Theorem 2.1 gives the reverse inclusion.

Conversely, every \(f\in F\) preserves \(\operatorname{Cg}_F(E)\). If the closure equals \(E\),
every \(f\) preserves \(E\). ∎

### Proof of Theorem 2.3

The kernel \(K_q\) is an equivalence relation. Suppose (7) holds and \(q(x)=q(y)\). Then

\[
 q(f(x))=\bar f(q(x))=\bar f(q(y))=q(f(y)),
\]

so \(f\) preserves \(K_q\). Since \(E\subseteq K_q\), the kernel is executable and leastness gives
(8).

For the converse in the one-operation statement, assume \(f\) preserves \(K_q\). Define
\(\bar f\) on the image of \(q\) by

\[
 \bar f(q(x))=q(f(x)).
\]

Kernel preservation makes this well-defined. Extend it arbitrarily to \(B\setminus q(A)\). Then
(7) holds. The forward implication was proved above. If no arbitrary extension is desired, replace
\(B\) by the image \(q(A)\); the factorization statement is canonical there. ∎

### Proof of Theorem 2.4

Every valid observer kernel is an executable relation containing \(E\). Theorem 2.1 therefore forces
it to contain \(\operatorname{Cg}_F(E)\). If the current kernel does not, validity is impossible.
Deleting offending operations changes \(F\); enlarging the kernel changes the relation. By
Theorem 2.2 these are exactly the two commitments whose incompatibility caused failure. ∎

### Proof of Theorem 2.5

Every \(G\)-executable relation containing \(E'\) is, a fortiori, an \(F\)-executable relation
containing \(E\). The family intersected on the right of (10) is therefore smaller, so its
intersection is larger. ∎

## 4. What this mechanism predicts

Given a concrete source law family and an observer, the theorem computes a set of forced new
identifications before any target theorem is attempted. It also proves that downstream processing
cannot repair a law that never descended through the observer. This is stronger than saying that an
observer is lossy: it gives the universal minimal loss compatible with retaining the laws.

## 5. Hostile scope

1. The theorem is classical universal algebra expressed as a mechanism law. The proposed field
   content depends on source-native applications and exchange with nonalgebraic formations.
2. Unary operations are only the first exact layer. Higher arity, partial operations, analytic
   domains, positivity, and completion require typed extensions.
3. The theorem contains no cost, topology, recurrence, or hypertranscendence by itself.
4. The arbitrary extension of \(\bar f\) off \(q(A)\) uses choice; the canonical statement is on
   the image quotient.
5. No RH or route endpoint is used or implied.

## 6. Lean certificate

Equations (2)--(10) are formalized in
`GaloisForLFunctions.HTGeometry.ConstitutiveUnaryLawRepair`, with unconditional capstone `unaryLawRepairMechanism_closed` bundling
least repair, fixedness, kernel factorization, no-descent, and monotonicity. It is imported through the universal-law umbrella. Source check, module build, lint, and axiom audit passed. The audit reports only Lean/mathlib foundations `propext`, `Classical.choice`, and `Quot.sound`; no project axiom, placeholder, unsafe declaration, or computation proof is used.

## Log

- 2026-08-09 — dependency-closed paper proof completed.\n- 2026-08-09 — Lean source check, module build, umbrella wiring, lint, and axiom audit passed; promoted to Stage 3.

