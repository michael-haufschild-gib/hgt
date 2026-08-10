# Finitary formation, joint saturation, and the cofinal-law birth barrier

- **ID:** ULF-GTM-2
- **Stage:** 2-fully-proven
- **Type:** THEOREM (Lean)
- **Field role:** Constitutive Process Mathematics, Law XI
- **Statement:** Arbitrarily many monotone extensive finitary law-formers, with arbitrary
  noncommutation and all finite compositions admitted, generate a least joint closure that is still
  finitary. A concrete closure on `Set ℕ` has a law born only from an infinite source and therefore
  cannot arise from any such joint saturation.

## 1. Why this is a mechanism theorem

The frontier map does not mainly display twelve unrelated unfinished proofs. It displays repeated
failure of one inference pattern:

> every finite aperture, finite relation family, finite observer, or finite intervention history
> behaves correctly, yet the required global law is not forced.

Adding routes, rule types, higher but finite arities, or noncommuting reductions does not by itself
answer that failure. The question is whether their **formation mechanism** can create a consequence
whose ancestry is genuinely cofinal.

This card proves a sharp barrier. Within finitary formation mechanics, it cannot.

## 2. Definitions

Let `X` be a set. A **formation** is a map

\[
f:\mathcal P(X)\longrightarrow\mathcal P(X).
\]

It is:

- **monotone** if \(A\subseteq B\Rightarrow f(A)\subseteq f(B)\);
- **extensive** if \(A\subseteq f(A)\);
- **finitary** if
  \[
  x\in f(A)\Longrightarrow
  \exists F\subseteq A\text{ finite such that }x\in f(F).
  \tag{2.1}
  \]

Fix an arbitrary index set `I` and formations \((f_i)_{i\in I}\). For a finite word
\(w=(i_1,\ldots,i_n)\), write

\[
f_w=f_{i_n}\circ\cdots\circ f_{i_1},
\qquad f_\varnothing=\operatorname{id}.
\]

Their **finite-history joint saturation** is

\[
f^*(A)=\bigcup_{w\in I^{<\omega}} f_w(A).
\tag{2.2}
\]

No commutation, bounded arity, finite index set, termination bound, or common presentation is
assumed.

## 3. Main theorem

### Theorem 3.1 — finitary joint-saturation barrier

Let every \(f_i\) be monotone, extensive, and finitary. Then:

1. every finite composite \(f_w\) is finitary;
2. \(f^*\) is finitary;
3. \(f^*\) is monotone, extensive, and idempotent, hence a closure operator;
4. every generator preserves its saturation:
   \[
   f_i(f^*(A))\subseteq f^*(A);
   \tag{3.1}
   \]
5. if `c` is any closure operator satisfying
   \[
   f_i(A)\subseteq c(A)
   \quad\text{for every }i,A,
   \tag{3.2}
   \]
   then
   \[
   f^*(A)\subseteq c(A).
   \tag{3.3}
   \]

Therefore \(f^*\) is the least closure containing all formations, and this least closure remains
finitary even for an arbitrary family of mutually noncommuting formation rules.

### Proof

First prove that the composite of two monotone finitary formations `f,g` is finitary. Suppose
\(x\in g(f(A))\). Finitarity of `g` gives a finite set \(E\subseteq f(A)\) with
\(x\in g(E)\). For each \(e\in E\), finitarity of `f` gives finite \(F_e\subseteq A\) with
\(e\in f(F_e)\). Let \(F=\bigcup_{e\in E}F_e\), still finite. Monotonicity gives
\(E\subseteq f(F)\), hence

\[
x\in g(E)\subseteq g(f(F)).
\]

Induction on word length proves item 1.

For item 2, if \(x\in f^*(A)\), some finite word `w` satisfies \(x\in f_w(A)\). Item 1 gives
a finite \(F\subseteq A\) with \(x\in f_w(F)\subseteq f^*(F)\).

Monotonicity and extensivity of \(f^*\) follow respectively from monotonicity of every finite
composite and the empty word.

The only nontrivial closure step is idempotence. Suppose first that finite
\(E\subseteq f^*(A)\). For every \(e\in E\), choose a word \(w_e\) producing `e`. Because `E` is
finite and every formation is extensive, concatenate those finitely many words. The resulting word
`w` retains every earlier output and therefore satisfies

\[
E\subseteq f_w(A).
\tag{3.4}
\]

Now let \(x\in f_i(f^*(A))\). Finitarity of \(f_i\) gives finite
\(E\subseteq f^*(A)\) with \(x\in f_i(E)\). By (3.4), \(E\subseteq f_w(A)\), so monotonicity gives

\[
x\in f_i(f_w(A))=f_{w i}(A)\subseteq f^*(A).
\]

This proves (3.1). Induction on a second finite word shows
\(f_w(f^*(A))\subseteq f^*(A)\), hence \(f^*(f^*(A))\subseteq f^*(A)\). Extensivity gives the
reverse inclusion, proving idempotence.

Finally, assume (3.2). Induction on `w` gives \(f_w(A)\subseteq c(A)\): the inductive step uses
\(f_i(B)\subseteq c(B)\), monotonicity of `c`, and \(c(c(A))=c(A)\). Taking the union over all
finite words proves (3.3). ∎

## 4. Sharp cofinal-birth countermodel

Define \(B:\mathcal P(\mathbb N)\to\mathcal P(\mathbb N)\) by

\[
B(A)=
\begin{cases}
A\cup\{0\},&A\text{ infinite},\\
A,&A\text{ finite}.
\end{cases}
\tag{4.1}
\]

### Theorem 4.1 — irreducibly cofinal birth

The map `B` is a monotone, extensive, idempotent closure operator, but it is not finitary.
Specifically, for

\[
P=\{1,2,3,\ldots\}=\operatorname{range}(n\mapsto n+1),
\]

one has \(0\in B(P)\), while for every finite \(F\subseteq P\),

\[
0\notin B(F)=F.
\tag{4.2}
\]

Consequently, for every arbitrary family of monotone extensive finitary formations,

\[
f^*\ne B.
\tag{4.3}
\]

### Proof

Extensivity is immediate. If \(A\subseteq C\) and `A` is infinite, then `C` is infinite, so both
sides adjoin `0`; if `A` is finite, \(B(A)=A\subseteq C\subseteq B(C)\). Thus `B` is monotone.
After one application, either nothing was added or only `0` was added; the result is infinite
exactly in the already-infinite case, so a second application changes nothing. Thus `B` is
idempotent.

The set `P` is infinite and excludes `0`, so `0` belongs to `B(P)`. Every finite subset `F` of `P`
remains finite, hence \(B(F)=F\), which excludes `0`. This contradicts the finite-witness condition
(2.1), proving that `B` is not finitary. Theorem 3.1 says every \(f^*\) under the stated hypotheses
is finitary, proving (4.3). ∎

## 5. Constitutive mechanism law

### CPM Law XI — cofinal birth requires a formation-class transition

A consequence with no finite source ancestry cannot be generated merely by:

- adding arbitrarily many finitary rule types;
- allowing those rules to fail to commute;
- admitting every finite history of rule application;
- allowing interaction arity to grow without a uniform finite bound;
- repeatedly saturating until a fixed point.

At least one load-bearing mechanism must instead occur:

1. **infinitary formation:** one admitted law-former itself has genuinely infinite premises;
2. **admission/completion transition:** the carrier or meaning of consequence changes at the limit;
3. **compactness/effectivity theorem:** an apparently global consequence is proved to have finite
   ancestry after all.

This trichotomy is a barrier, not an existence theorem. It does not say which branch a source
chooses. It says what any proposed universal field mechanism must prove before claiming to create a
cofinal law.

## 6. Hostile conjecture loops

### Loop A — noncommutation creates cofinal laws

**False.** Theorem 3.1 imposes no commutation hypothesis. Critical pairs can create ordered history,
residuals, and repair choices while every consequence still has finite ancestry.

**Survivor:** noncommutation is a local history-production mechanism, not a cofinal-birth mechanism.

### Loop B — unbounded finite arity is already infinitary

**False.** An arbitrary family indexed by all finite arities is included in Theorem 3.1. Each
particular consequence still arises from one finite word and a finite source witness.

**Survivor:** unbounded arity gives an unbounded interaction spectrum. It does not by itself give
one irreducibly cofinal consequence.

### Loop C — transfinite-looking saturation escapes finite ancestry

**False in this formation class.** The finite-word union is already a fixed point and the least
joint closure. Further iteration adds nothing.

**Survivor:** any later stage adding a law must have changed formation class, carrier, or
admissibility.

### Loop D — topological closure is automatically finitary

**False.** Limit points such as \(0\in\overline{\{1/n:n\ge1\}}\) need not lie in the closure of any
finite subset. Topological or analytic completion is therefore a natural source of nonfinitary
formation, not evidence against the barrier.

**Survivor:** completion must be represented as a constitutive operation with its admission and
topology marked; writing “take the closure” hides the decisive field transition.

### Loop E — hypertranscendence is nonfinitary consequence

**False as a general identification.** Differential-algebraic consequences are finite equations;
hypertranscendence states persistent nonmembership across all such finite relation attempts.

**Survivor:** HT can witness failure of every finite relation chart without itself being the
infinitary law-former that creates a positive global consequence.

### Loop F — every nonfinitary closure is source selection

**False.** Equation (4.1) is deliberately generic. One can manufacture countless nonfinitary
closures.

**Survivor:** a live application must derive its nonfinitary formation from pre-target source
operations and prove its compatibility with admitted observers.

## 7. Frontier-map interpretation

This theorem changes how the frontier is attacked without attempting any route endpoint.

| frontier obstruction class | mechanism question forced by Law XI |
|---|---|
| singular source descent | which source operation changes finite ancestry at completion? |
| all-prime oscillatory transport | is cancellation an infinitary formation or a compactness theorem? |
| adaptive spectral orientation | what global intervention is not generated by finite adaptive histories? |
| whole-space coercivity | which limit admission turns finite lower bounds into a global carrier? |
| positive carrier existence | is carrier birth a nonfinitary existence operation or an effectivity theorem? |

These are research questions, not claims that the five obstruction classes are identical. The law
locates their common logical bottleneck: a finite-to-cofinal quantifier exchange.

## 8. Mathematical parents and synthesis boundary

The parent machinery is established:

- algebraic/finitary closure operators and closure under arbitrary joins: M. L. H. Kilpack,
  [*The lattice of algebraic closure operators*](https://arxiv.org/abs/1411.6497);
- finitary monads and Lawvere theories: R. Garner,
  [*Lawvere theories, finitary monads and Cauchy-completion*](https://arxiv.org/abs/1307.2963);
- infinitary versus finitary consequence and compactness are classical logical themes.

The field-level synthesis is the interpretation of finitarity as **law ancestry** and its use as a
hard gate between local formation mechanics and cofinal law birth. No priority claim is made for
the closure theory.

## 9. Lean certificate

Formal module:

`GaloisForLFunctions.HTGeometry.ConstitutiveFinitaryFormation`

Significant declarations:

- `finitaryFormation_comp`;
- `runFormations_finitary`;
- `wordSaturationClosure_finitary`;
- `wordSaturationClosure_least`;
- `cofinalBirth_not_finitary`;
- `cofinalBirth_ne_wordSaturationClosure`.

The Lean proof is unconditional, introduces no axiom, and formalizes the arbitrary-index theorem,
least-closure property, concrete cofinal-birth closure, and universal separation capstone.

## 10. Status

- [x] dependency-closed paper proof;
- [x] hostile loops closed with positive survivors;
- [x] exact theorem formalized in Lean;
- [ ] source-specific nonfinitary formation constructed;
- [ ] second independent analytic realization of the same mechanism;
- [ ] route-independent compactness/effectivity theorem derived from corpus source.

This proves CPM Law XI. It does not complete CPM or any RH route.

## Log

- 2026-08-09 — extracted from current frontier as finite-to-cofinal quantifier barrier.
- 2026-08-09 — proved arbitrary-family joint saturation remains finitary despite noncommutation.
- 2026-08-09 — constructed sharp nonfinitary closure and closed Lean certificate.
