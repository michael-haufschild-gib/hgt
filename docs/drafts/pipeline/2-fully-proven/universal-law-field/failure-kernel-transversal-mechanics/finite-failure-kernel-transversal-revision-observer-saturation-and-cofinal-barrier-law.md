# Finite failure-kernel transversal revision, observer saturation, and cofinal barrier law

- **ID:** ULF-FKT-1
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / ROUTE-INDEPENDENT REVISION MECHANISM
- **Statement:** In a finite monotone consequence system, withdrawing a failed consequence is
  exactly the problem of hitting every minimal derivation kernel; minimal repairs have exact
  core-retainment witnesses, quotient observers lift repairs only after fibre saturation, symmetric
  exact repair may fail while a fractional positive repair survives, and cofinally born singleton
  kernels admit no finite global repair.
- **Status:** [PROVED HERE] [DEPENDENCY-CLOSED] [MECHANISM NOT OBJECT]
  [KERNEL--TRANSVERSAL DUALITY] [OBSERVER SATURATION] [COFINAL BARRIER] [LEAN CLOSED] [NOT RH]

## 1. Founding question

The corpus has many exact routes, each of which eventually exposes a different obstruction.  The
usual response is to add another relation, completion, positivity structure, or source-native map.
That is a monotone move.  It cannot explain how mathematics should revise an already admitted law
that erased the distinction now needed by the proof.

This card tests a different mechanism:

> A failed conclusion exposes its minimal derivation kernels.  A genuine law revision must cut all
> of them.  The family of minimal cuts, rather than any one route object, is the successor doctrine.

The result is finite and abstract.  No RH route, analytic realization, topology, metric, or chosen
physical model occurs in the theorem.

## 2. Finite consequence bases and failure kernels

Let `E` be a finite set of primitive law facts.  A consequence operator is a map

\[
  c:\mathcal P(E)\longrightarrow\mathcal P(E)
\]

that is monotone:

\[
  A\subseteq B\quad\Longrightarrow\quad c(A)\subseteq c(B).
  \tag{FK.1}
\]

Extensivity and idempotence may be imposed, but neither is needed for the main theorem.  Let
`T subset E` be the retained proof base and let `a in c(T)` be a conclusion that must be withdrawn.

An **`a`-kernel in `T`** is a set `K subset T` such that

\[
 a\in c(K),\qquad
 a\notin c(L)\quad\text{for every }L\subsetneq K.
 \tag{FK.2}
\]

Write `K_a(T)` for the finite hypergraph of all `a`-kernels.  A removal set `R subset T` is
**successful** when

\[
  a\notin c(T\setminus R).
  \tag{FK.3}
\]

It is **minimal successful** when no proper subset of `R` is successful.

## 3. Exact kernel--transversal law

### Theorem 3.1 -- success is exactly transversal incidence

For every removal set `R subset T`,

\[
 \boxed{
 a\notin c(T\setminus R)
 \quad\Longleftrightarrow\quad
 (\forall K\in\mathcal K_a(T))\;R\cap K\ne\varnothing .}
 \tag{FK.4}
\]

Thus successful revisions are precisely transversals of the failure-kernel hypergraph.

#### Proof

Assume first that `R` is successful.  If some kernel `K` were disjoint from `R`, then
`K subset T\R`.  Monotonicity and `a in c(K)` would give `a in c(T\R)`, contradiction.

Conversely, suppose `R` hits every kernel and nevertheless `a in c(T\R)`.  Because `E` is finite,
among the subsets of `T\R` that entail `a` choose one, `K`, of minimum cardinality.  No proper subset
of `K` entails `a`; hence `K` is an `a`-kernel in `T`.  But `K subset T\R`, so `R cap K` is empty,
contradiction.  QED.

### Theorem 3.2 -- exact core-retainment certificate

A successful removal `R` is inclusion-minimal if and only if for every `r in R` there exists a
kernel `K_r in K_a(T)` such that

\[
  \boxed{R\cap K_r=\{r\}.}
  \tag{FK.5}
\]

Every removed fact is therefore certified as the unique cut of at least one live minimal proof.

#### Proof

Suppose `R` is minimal and fix `r in R`.  Then `R\{r}` is not successful.  By Theorem 3.1 it misses
some kernel `K_r`.  Since `R` itself hits every kernel, `R cap K_r` is nonempty; since
`(R\{r}) cap K_r` is empty, the intersection is exactly `{r}`.

Conversely, assume the displayed certificate exists for every `r in R`.  If a proper subset
`S subsetneq R` were successful, choose `r in R\S`.  Then `S` misses `K_r`, contradicting
Theorem 3.1.  QED.

### Corollary 3.3 -- the successor test is generated, not guessed

The complete exact test for whether a proposed revision succeeds is the incidence vector

\[
  R\longmapsto
  \bigl(\mathbf 1_{R\cap K\ne\varnothing}\bigr)_{K\in\mathcal K_a(T)}.
  \tag{FK.6}
\]

Its coordinates and arities are forced by the minimal proof supports of the failure.  A proposed
repair that tests only one route/kernel is incomplete whenever another kernel survives.

## 4. Expansion--contraction asymmetry

Adding a fact `b` and closing gives a canonical least monotone expansion `c(T union {b})`.  Removing
a consequence is different: there need not be a greatest retained subbase that avoids it.

### Countermodel 4.1 -- no canonical greatest contraction

Take primitives `p,q,a` and let

\[
 c(S)=
 \begin{cases}
   S\cup\{a\},&\{p,q\}\subseteq S,\\
   S,&\text{otherwise}.
 \end{cases}
 \tag{FK.7}
\]

For `T={p,q}`, the unique `a`-kernel is `{p,q}`.  The two minimal repairs are `{p}` and `{q}`; the
two maximal retained bases are `{q}` and `{p}`.  They are incomparable, so there is no greatest
successful retained base.  Monotone saturation is canonical; contraction needs a selection law or
retained provenance.

This is not a pathology.  It is the smallest exact reason repeated requests for “the missing
relation” can be ill-posed: the failure may determine a repair family without selecting a member.

## 5. Observer transport and fibre-saturated over-removal

Let `f:E -> Y` be an observer.  It sends a source kernel `K` to the observed kernel `f(K)`.  For a
source removal `R`, define its observed image `f(R)`.  For an observed removal `S subset Y`, define
its source pullback on `T` by

\[
  f_T^{-1}(S)=\{x\in T:f(x)\in S\}.
  \tag{FK.8}
\]

### Theorem 5.1 -- transversal transport

1. If `R` hits every source kernel, then `f(R)` hits every observed kernel `f(K)`.
2. If `S` hits every observed kernel, then `f_T^{-1}(S)` hits every source kernel.
3. The round trip satisfies
   \[
     R\subseteq f_T^{-1}(f(R)),
     \tag{FK.9}
   \]
   with equality exactly when `R` is a union of observer fibres inside `T`.

#### Proof

For (1), choose `x in R cap K`; then `f(x)` lies in both images.  For (2), choose
`y in S cap f(K)` and a preimage `x in K` with `f(x)=y`; then `x in f_T^{-1}(S) cap K`.
Inclusion (FK.9) is immediate.  Equality says exactly that whenever `x in R` and `z in T` have
`f(z)=f(x)`, then `z in R`, which is fibre saturation.  QED.

### Consequence

A quotient observer can certify existence of a repair but cannot recover an unsaturated minimal
source repair.  Pullback removes the whole observed fibre.  This is an exact information-loss law:
observer-level repair may be valid and still be strictly more destructive than any marked
source-level repair.

## 6. Symmetry obstruction and positive fractional repair

Return to Countermodel 4.1.  The involution interchanging `p` and `q` preserves the failure and its
unique kernel, but exchanges the two minimal exact repairs.  Hence no deterministic equivariant
selector can choose a minimal repair from the unmarked failure record.

Convexification changes the answer.  Give `p` and `q` nonnegative weights `w_p,w_q` and relax exact
incidence to

\[
  w_p+w_q\ge1.
  \tag{FK.10}
\]

The symmetric fractional repair `w_p=w_q=1/2` exists and is fixed by the involution.  It is not an
exact contraction: half a premise has not been withdrawn.

The gap can be quantitative.  For the triangle kernel hypergraph

\[
  \{\{1,2\},\{2,3\},\{1,3\}\},
  \tag{FK.11}
\]

every integral transversal has size at least `2`, while the symmetric fractional transversal
`(1/2,1/2,1/2)` has total weight `3/2`.

### Interpretation law

Positivity is not universally a phase quotient.  Here, precisely, positive convexification is the
fractional relaxation of exact doctrine revision.  It can restore symmetry and lower cost while
forgetting which integral premise was actually retracted.  Exactness is the integrality problem.

## 7. Cofinal kernel birth and open revision history

Let the primitive vocabulary be the natural numbers and let the stage-`n` failure kernels be the
singletons

\[
  \mathcal H_n=\{\{0\},\ldots,\{n-1\}\}.
  \tag{FK.12}
\]

### Theorem 7.1 -- finite-stage repair, no finite global repair

Every transversal of `H_n` contains `{0,...,n-1}`, so its cardinality is at least `n`; this bound is
sharp.  No finite set meets every singleton kernel `{j}` for `j in N`.

#### Proof

Hitting `{j}` is equivalent to containing `j`.  Therefore a stage-`n` transversal contains the
first `n` naturals.  A finite set of naturals omits some natural number, whose singleton it misses.
QED.

### Consequence

Finite success at every stage does not imply a finite global doctrine repair.  If failures keep
creating independent kernels, exact revision cost and support must grow without bound.  This is a
mechanism for closed finite observation with open lifted law history.  In a differential
realization, unbounded independent grade-kernels are a possible carrier of hypertranscendence; the
identification must be proved in that realization and is not asserted universally here.

## 8. Conjecture--proof--failure tournament

1. **More closure will generate the missing law.**  False: closure is canonical expansion and
   cannot choose among contractions in Countermodel 4.1.  Survivor: retain proof kernels.
2. **Repair one failed route and the theorem is repaired.**  False whenever another minimal kernel
   is missed.  Survivor: exact repair is global transversal incidence.
3. **A quotient-level repair lifts minimally.**  False by Theorem 5.1: it lifts as fibre-saturated
   over-removal.  Survivor: mark source fibres or accept the extra loss.
4. **Symmetry selects the natural repair.**  False for the swapped pair.  Survivor: orientation,
   multivalued repair, or fractional convexification.
5. **Positive relaxation is exact.**  False already for the triangle integrality gap.  Survivor:
   positivity supplies a lower-cost relaxation and an obstruction bound, not an integral revision.
6. **Finite repairability implies global repairability.**  False by Theorem 7.1.  Survivor: require
   compactness/coherence or record open cofinal repair history.

## 9. Five frontier-class predictions

This theorem does not instantiate RH routes.  It predicts what any successful instantiation must
prove in each frontier class.

| Frontier class | Kernel--transversal prediction |
|---|---|
| singular source descent | the completion has merged distinct minimal kernels; a continuous repair pulls back as fibre-saturated over-removal unless provenance survives |
| all-prime oscillatory transport | a successful signed intervention must hit every live prime/scale cancellation kernel before modulus or norm quotient |
| adaptive spectral orientation | adaptive flags index failure kernels; a fixed finite sign test cannot be a transversal unless a uniform kernel theorem is proved |
| whole-space coercivity | escaping sequences are cofinal kernels; seedwise repair is insufficient unless compactness turns them into a finite transversal basis |
| positive carrier existence | moment/positivity constraints define a fractional repair; an actual carrier requires an integrality/effectivity theorem |

These are falsifiable.  If a frontier class admits a route theorem that succeeds while missing one
of its proved minimal kernels, the mechanism is wrong.  If no source-level notion of minimal kernel
can be defined invariantly, this synthesis remains only an analogy and must not be promoted.

## 10. Parent mathematics and exact synthesis boundary

The ingredients are established:

- AGM and Hansson kernel contraction: minimal entailment kernels and incision functions;
- hypergraph blockers/minimal transversals and monotone dualization;
- proof and database provenance, including reverse provenance for repairs;
- equivariant decision theory and convex relaxations;
- generated Grothendieck topologies and quotient completions for monotone doctrine expansion.

The field move is their interpretation as one mechanism of mathematical law genesis: theorem
failures produce a proof-kernel hypergraph; exact successor doctrines are its transversals; observer
quotients cause fibre saturation; positive structure is a fractional relaxation; and cofinal kernel
birth is open law history.  No priority claim is made for any ingredient.

Primary parents:

- S. O. Hansson, *Kernel contraction*, J. Symbolic Logic 59 (1994), 845--859,
  <https://doi.org/10.2307/2275912>;
- F. M. Falakh, S. Rudolph, K. Sauerwald, *Semantic Characterizations of General Belief Base
  Revision*, <https://arxiv.org/abs/2112.13557>;
- E. Gradel, V. Tannen, *Provenance Analysis and Semiring Semantics for First-Order Logic*,
  <https://arxiv.org/abs/2412.07986>;
- G. Gottlob, E. Malizia, *Achieving New Upper Bounds for the Hypergraph Duality Problem through
  Logic*, <https://arxiv.org/abs/1407.2912>;
- O. Caramello, L. Lafforgue, *Generation of Grothendieck topologies, provability and operations on
  subtoposes*, <https://arxiv.org/abs/2508.21134>.

## 11. Lean certification

`GaloisForLFunctions.HTGeometry.ConstitutiveFailureKernelTransversal` closes, without route
hypotheses:

1. existence of a minimal kernel inside every finite entailing base;
2. Theorem 3.1 and the core-retainment direction of Theorem 3.2;
3. observer image/pullback transversal transport and exact fibre-saturation criterion;
4. the swapped-pair exact/fractional repair obstruction and triangle integrality gap;
5. sharp finite-stage singleton-kernel cost and the no-finite-global-repair barrier;
6. one closed route-independent capstone combining exact duality, integrality gap, and cofinal
   obstruction.

The module is imported by `GaloisForLFunctions.HTGeometry.UniversalLawField`.  Direct elaboration,
formal lint, umbrella build, and axiom audit are recorded in the Stage-3 card.

## Log

- 2026-08-10 -- generic doctrine mutation and generated-coverage candidates rejected as regressions;
  proof-kernel transversal revision isolated as higher mechanism.
- 2026-08-10 -- finite kernel duality, observer saturation, symmetry/fractional boundary, and
  cofinal barrier proved on paper.
- 2026-08-10 -- theorem family formalized in Lean and wired into the universal-law-field umbrella.
