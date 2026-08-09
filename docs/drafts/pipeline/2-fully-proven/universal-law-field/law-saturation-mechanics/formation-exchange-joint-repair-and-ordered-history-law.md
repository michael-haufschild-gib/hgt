# Formation exchange, joint repair, and ordered-history law

- **ID:** ULF-LSM-3
- **Stage:** 2-fully-proven
- **Type:** ROUTE-INDEPENDENT MECHANISM THEOREM
- **Status:** [PAPER-PROVED] [LEAN-PROVED] [DEPENDENCY-CLOSED] [FORMATION LAW]
  [EXCHANGE LAW] [JOINT REPAIR] [ORDERED HISTORY] [NOT RH]

## 1. Setup

Let (X) be a set. A **law formation** on (mathcal P(X)) is a map

\[
 C:\mathcal P(X)\longrightarrow\mathcal P(X)
\]

that is extensive, monotone, and idempotent:

\[
 S\subseteq C(S),\qquad S\subseteq T\Rightarrow C(S)\subseteq C(T),\qquad C(C(S))=C(S).
\tag{1}
\]

For a family (mathcal F) of formations define its joint repair above (S) by

\[
 J_{\mathcal F}(S)
 =\bigcap\{T:S\subseteq T,\ C(T)=T\text{ for every }C\in\mathcal F\}.
\tag{2}
\]

The family in (2) is nonempty because (X) is fixed by every extensive map.

For a finite word (w=(C_1,\ldots,C_n)), write

\[
 w(S)=C_n\cdots C_1(S).
\tag{3}
\]

## 2. Joint-repair theorem

### Theorem 2.1

For every family (mathcal F) and every (S\subseteq X):

1. (S\subseteq J_{\mathcal F}(S));
2. (C(J_{\mathcal F}(S))=J_{\mathcal F}(S)) for every (C\in\mathcal F);
3. if (S\subseteq T) and every (C\in\mathcal F) fixes (T), then
   (J_{\mathcal F}(S)\subseteq T);
4. every finite formation word using letters from (mathcal F) satisfies
   (w(S)\subseteq J_{\mathcal F}(S)).

Thus joint repair is the unique least executable world above (S), and no finite schedule can
overshoot it.

### Proof

Item 1 holds because every set in the intersection contains (S). For item 2 fix
(C\in\mathcal F). Extensivity gives

\[
 J_{\mathcal F}(S)\subseteq C(J_{\mathcal F}(S)).
\]

For every common fixed point (T) above (S), monotonicity gives

\[
 C(J_{\mathcal F}(S))\subseteq C(T)=T.
\]

Intersect over all such (T). This proves the reverse inclusion and item 2. Item 3 is immediate
from the defining intersection. For item 4, induct on word length. If the current state lies in
(J_{\mathcal F}(S)), applying (C\in\mathcal F) keeps it there by monotonicity and item 2. ∎

## 3. Exchange theorem

Let (C,D) be two law formations and put (J=J_{\{C,D\}}).

### Theorem 3.1

The following are equivalent:

1. (C D=D C) on every subset of (X);
2. for every (S\subseteq X), both two-step schedules are the joint repair:
   \[
   D(C(S))=J(S)=C(D(S)).
   \tag{4}
   \]

Consequently, a coherent invertible exchange law removes all order memory after one application of
each formation. If (C(D(S))\ne D(C(S))), the two length-two histories are observably distinct even
though both remain below the same least joint repair.

### Proof

Assume (CD=DC). Set (U=D(C(S))). It contains (S). It is fixed by (D) by idempotence. It is
fixed by (C) because

\[
 C(U)=C(D(C(S)))=D(C(C(S)))=D(C(S))=U.
\]

Theorem 2.1 therefore gives (J(S)\subseteq U). Conversely (S\subseteq J(S)), so monotonicity and
common fixedness give

\[
 U=D(C(S))\subseteq D(C(J(S)))=J(S).
\]

Hence (U=J(S)); commutation gives the other order. Conversely, if both orders equal (J(S)) for
every (S), they equal one another for every (S), which is commutation. The final statement is
the contrapositive at a witnessing (S). ∎

## 4. Mechanism consequences

1. **Formation is not an object.** The invariant is how enforcing one doctrine changes the next
   enforcement.
2. **Exchange is the zero-history criterion.** Commuting idempotent formations have no residual
   schedule memory; one pass computes exact joint repair.
3. **Failed exchange is ordered history.** No curvature metaphor is required. The raw witness is the
   unequal critical pair (CD(S),DC(S)).
4. **Saturation is canonical.** Even when histories differ, their least common executable repair is
   defined without choosing a schedule.
5. **Endpoint invariants may remain incomplete.** Split/nonsplit extension examples prove that
   identical repair endpoints can retain different carry. Such memory belongs to higher exchange
   data, not to the closure theorem itself.

## 5. Strict three-formation ceiling

### Theorem 5.1

Let $C,D,E$ be pairwise commuting law formations. Then every one of the six schedules applying each
formation exactly once equals the same joint repair

$$
J_{\{C,D,E\}}(S)=E(D(C(S))).
$$

Hence strict pairwise-commuting closure mechanics cannot carry a three-way associator,
Yang--Baxter defect, or higher holonomy.

### Proof

Set $U=E(D(C(S)))$. It contains $S$. Idempotence fixes it under $E$. Commuting $D$ past $E$, then
using idempotence, fixes it under $D$. Commuting $C$ past $E$ and $D$, then using idempotence, fixes
it under $C$. Theorem 2.1 identifies $U$ with joint repair. Any permutation of $C,D,E$ is a product
of adjacent transpositions; pairwise commutation therefore makes every schedule equal to $U$. ∎

This kills a tempting but false next step: higher field strength cannot be obtained by adding more
strict commuting closure operators. A genuine three-way mechanism must use weak or noninvertible
exchange cells, partial/admission-sensitive formation, non-idempotent history, or extension/carry
data not determined by endpoint closure.

## 6. Sharpness and boundaries

- Extensivity is load-bearing: without it the whole set need not be a common fixed point.
- Monotonicity is load-bearing in the intersection and schedule proofs.
- Idempotence is load-bearing for the two-step exchange formula.
- Failed commutation proves order dependence, not nontrivial cohomology or physical curvature.
- The theorem does not ensure a finite word reaches joint repair. The already-proved alternating
  unary model reaches its common repair only at stage (omega) while every finite reporter
  stabilizes.
- The theorem does not generate positivity, topology, differential prolongation, cost, or a source
  signature. Those must enter as concrete formations and exchange laws.

## 7. Parent boundary

This is classical closure-operator mathematics, adjacent to commuting reflectors, abstract
interpretation, and distributive-law theory. Its significance here is foundational: it provides an
exact mechanism law and a falsifiable zero-history criterion for the universal-law programme. It
is not claimed as an isolated novelty theorem.

## 8. Lean certificate

Module `GaloisForLFunctions.HTGeometry.ConstitutiveFormationExchange` certifies:

- `ConstitutiveFormation`;
- `constitutiveJointRepair` and its containment, fixedness, and leastness;
- schedule boundedness;
- commuting-formation joint-repair theorem;
- exchange iff both two-step schedules equal joint repair;
- failed exchange gives unequal formation histories;
- pairwise-commuting triples have exact joint repair and no schedule defect.

The module is wired into `GaloisForLFunctions.HTGeometry.UniversalLawField`. Targeted foreground
build and axiom audit pass. `#print axioms` reports only `propext`, `Classical.choice`, and
`Quot.sound`; no project axiom, placeholder, unsafe declaration, or computation proof is used.

## Log

- 2026-08-09 — dependency-closed proof written after mechanism-first whole-corpus audit.
- 2026-08-09 — theorem formalized in Lean, axiom-audited, and wired into field umbrella.
