# Observer-induced relational law, lax composition, and splice-defect law

- **ID:** ULF-RLR-1
- **Stage:** 2-fully-proven
- **Type:** ROUTE-INDEPENDENT MECHANISM THEOREM
- **Statement:** Every observed deterministic law has a canonical relational effective law;
  deterministic descent is exactly right-uniqueness, observer coarsening is strict pushforward,
  execution is lax, and its exact splice defect detects source-unrealizable histories.
- **Status:** [PAPER-PROVED] [DEPENDENCY-CLOSED] [MECHANISM NOT OBJECT]
  [RELATIONAL RENORMALIZATION] [SHARP COUNTERMODELS] [LEAN-PROVED] [AXIOM-FREE]
  [NOT RH]

## 1. Setup

Let `X,B` be sets, let

\[
 q:X\longrightarrow B
 \tag{RR.1}
\]

be a surjective observer, and let `f:X->X` be a deterministic source law.  Define its
**observer-induced effective relation** by

\[
 \boxed{
 b\;\mathcal R_q(f)\;c
 \quad\Longleftrightarrow\quad
 \exists x\in X,\ q(x)=b\ \text{and}\ q(fx)=c.}
 \tag{RR.2}
\]

For relations `R,S` on `B`, use execution-order composition

\[
 b\;(R;S)\;c
 \quad\Longleftrightarrow\quad
 \exists d,\ b\;R\;d\text{ and }d\;S\;c.
 \tag{RR.3}
\]

A relation is **right-unique** if one input has at most one output.  A source law `f` preserves the
observer kernel when

\[
 qx=qy\Longrightarrow q(fx)=q(fy).
 \tag{RR.4}
\]

## 2. Relational survival and deterministic chamber

### Theorem 2.1 — total relational survival

For every `f`:

1. `R_q(id_X)` is the diagonal relation on `B`;
2. `R_q(f)` is total: every `b in B` has at least one related output.

### Proof

For the identity, a witness `x` gives equal input and output observations.  Conversely,
surjectivity supplies `x` with `qx=b`, witnessing `b R_q(id) b`.

For totality, choose `x` with `qx=b`; then `q(fx)` is a related output by `(RR.2)`.  QED.

### Theorem 2.2 — determinism iff kernel preservation

The following are equivalent:

1. `f` preserves the kernel of `q`;
2. `R_q(f)` is right-unique;
3. there is a unique function `f_bar:B->B` satisfying
   \[
   qf=\bar f q;
   \tag{RR.5}
   \]
4. `R_q(f)` is the graph of one function `B->B`.

### Proof

Assume kernel preservation.  If `b R_q(f) c` and `b R_q(f) d`, choose witnesses `x,y`.  Then
`qx=b=qy`, so `(RR.4)` gives `c=q(fx)=q(fy)=d`.  Thus the relation is right-unique.

Conversely, if `qx=qy=b`, then `b R_q(f) q(fx)` and `b R_q(f) q(fy)`.  Right-uniqueness gives
`q(fx)=q(fy)`, proving kernel preservation.

Under kernel preservation define `f_bar(b)=q(fx)` for any `x` with `qx=b`.  Surjectivity gives a
witness and `(RR.4)` makes the definition independent of it.  Equation `(RR.5)` follows by using
`x` itself.  If `h` is another such function, choose `x` with `qx=b`; then
`h(b)=h(qx)=q(fx)=f_bar(b)`, proving uniqueness.

Equation `(RR.5)` says exactly that `(RR.2)` is the graph of `f_bar`.  Conversely, a graph is
right-unique.  QED.

This embeds strict executable descent as the deterministic chamber of relational survival.

## 3. Lax execution and exact splice defect

### Theorem 3.1 — lax effective composition

For all source laws `f,g:X->X`,

\[
 \boxed{
 \mathcal R_q(g\circ f)
 \subseteq
 \mathcal R_q(f);\mathcal R_q(g).}
 \tag{RR.6}
\]

If `g` preserves the kernel of `q`, then equality holds for every `f`.

### Proof

If `b R_q(gf) c`, choose `x` with `qx=b` and `q(g(fx))=c`.  Put `d=q(fx)`.  The same `x`
witnesses `b R_q(f) d`, and `fx` witnesses `d R_q(g) c`; hence the right side of `(RR.6)`.

Now suppose `g` preserves the kernel.  If `b (R_q(f);R_q(g)) c`, choose an intermediate `d`, a
witness `x` with `qx=b`, `q(fx)=d`, and a witness `y` with `qy=d`, `q(gy)=c`.  Since
`q(fx)=qy`, kernel preservation gives `q(g(fx))=q(gy)=c`.  Thus `x` witnesses
`b R_q(gf) c`.  QED.

Define the **splice defect**

\[
 \boxed{
 \Sigma_q(f,g)
 =\bigl(\mathcal R_q(f);\mathcal R_q(g)\bigr)
   \setminus \mathcal R_q(gf).}
 \tag{RR.7}
\]

Its elements are two-step effective histories obtained by joining different source histories at an
observationally equal midpoint.

### Theorem 3.2 — constant-prelaw converse

Assume `X` is nonempty.  For a fixed `g`, the following are equivalent:

1. `g` preserves the kernel of `q`;
2. `Sigma_q(f,g)` is empty for every `f:X->X`;
3. `Sigma_q(const_y,g)` is empty for every `y in X`.

### Proof

Theorem 3.1 proves `1 -> 2`, and `2 -> 3` is immediate.

Assume 3.  Let `y,z` satisfy `qy=qz`, and choose `x_0 in X`.  Put `b=qx_0` and let `f` be the
constant law with value `y`.  Then

\[
 b\;\mathcal R_q(f)\;q(y),
 \qquad
 q(y)\;\mathcal R_q(g)\;q(gz).
\]

Thus `(b,q(gz))` lies in the relational composite.  Empty splice defect puts it in
`R_q(gf)`.  But `gf` is constant with value `gy`, so every output of `R_q(gf)` is `q(gy)`.
Therefore `q(gy)=q(gz)`, proving kernel preservation.  QED.

Constant source preparations are therefore a separating intervention family for exact effective
composition.

## 4. Strict observer scaling

Let `p:B->C` be another surjective observer.  For a relation `R` on `B`, define its direct image

\[
 c\;(p_*R)\;d
 \Longleftrightarrow
 \exists b,b',\ p(b)=c,\ p(b')=d,\ b\;R\;b'.
 \tag{RR.8}
\]

### Theorem 4.1 — exact observer pushforward

For every source law `f`,

\[
 \boxed{
 \mathcal R_{p\circ q}(f)=p_*\mathcal R_q(f).}
 \tag{RR.9}
\]

### Proof

If `c R_(pq)(f) d`, choose `x` with `p(qx)=c` and `p(q(fx))=d`.  Take `b=qx` and
`b'=q(fx)` in `(RR.8)`; the same `x` witnesses `b R_q(f) b'`.

Conversely, choose `b,b'` and `x` witnessing the right side.  Then
`p(qx)=p(b)=c` and `p(q(fx))=p(b')=d`, so `x` witnesses the left side.  QED.

Thus observer coarsening is strict even though execution is only lax.

## 5. Deterministic selector no-go

### Theorem 5.1 — every deterministic law misses a branch

Suppose there are `b,c,d` with

\[
 b\;\mathcal R_q(f)\;c,
 \qquad b\;\mathcal R_q(f)\;d,
 \qquad c\ne d.
 \tag{RR.10}
\]

Then for every function `h:B->B` there exists `x in X` such that

\[
 h(qx)\ne q(fx).
 \tag{RR.11}
\]

### Proof

At least one of `c,d` differs from `h(b)`.  Choose that output and a witness `x` from `(RR.10)`.
Then `qx=b` and `q(fx)` is the chosen output, proving `(RR.11)`.  QED.

A deterministic selector may choose one branch of every nonempty effective fibre, but it cannot
be a source-exact descended law when any fibre branches.

## 6. Sharp four-state countermodels

Let

\[
 X=\mathbb B\times\mathbb B,
 \qquad B=\mathbb B,
 \qquad q(u,v)=u,
 \tag{RR.12}
\]

where `B` is the two-element Boolean set.  Define

\[
 f(u,v)=(\mathsf{true},\mathsf{false}),
 \qquad
 g(u,v)=(v,\mathsf{false}).
 \tag{RR.13}
\]

### Proposition 6.1 — strict splice defect

`R_q(f)` sends every observed input to `true`.  The relation `R_q(g)` sends every observed input to
both Boolean outputs.  The composite source law `gf` sends every observed input only to `false`.
Consequently

\[
 \mathcal R_q(gf)
 \subsetneq
 \mathcal R_q(f);\mathcal R_q(g).
 \tag{RR.14}
\]

### Proof

The formulas follow directly from `(RR.12)`--`(RR.13)`: `q(g(u,v))=v`, while
`g(f(u,v))=(false,false)`.  For strictness, the relational composite contains
`false -> true` through the observed midpoint `true`; the source composite has output only `false`.
QED.

### Proposition 6.2 — coarsening can create or erase branching

1. At the fine observer `id_X`, the effective relation of `g` is the graph of `g` and is
   deterministic.  At the coarser observer `q`, it branches at both Boolean inputs.
2. Let `!:B->Unit` be the constant observer.  The pushed relation `!_*R_q(g)` is the one-point
   diagonal and is deterministic.

### Proof

Item 1 follows because a function graph is right-unique, while `q(g(u,v))=v` varies with the hidden
second coordinate at fixed first coordinate.  Item 2 follows because `Unit` has one element and
`R_q(g)` is total.  QED.

Therefore branching is neither monotonically created nor monotonically destroyed by observation.

## 7. Mechanism theorem and unconditional leverage

The assignment

\[
 f\longmapsto\mathcal R_q(f)
 \tag{RR.15}
\]

is identity-strict and composition-lax from deterministic source execution to relational effective
execution.  It is strictly natural under serial observer pushforward.  Its laxity cell is invertible
exactly in the chambers identified by Theorems 3.1 and 3.2.

This yields one unconditional proof obligation:

> A quotient, scalarization, completion reporter, finite observer, or other lossy map may be used
> to iterate an effective deterministic law only after kernel preservation is established.  Without
> it, the canonical effective law is relational, and relational iteration contains splice histories
> that may have no source realization.

The statement applies only after the chart is literally typed as `(source function, observer)`.
It does not claim that unrelated proof systems are instances by analogy.

## 8. Serial observation--execution interchange

Let `p:B->C` be a further observer.  For source laws `f,g`, define three relations on `C`:

\[
 D_0=\mathcal R_{pq}(gf),\qquad
 D_1=p_*\bigl(\mathcal R_q(f);\mathcal R_q(g)\bigr),\qquad
 D_2=(p_*\mathcal R_q(f));(p_*\mathcal R_q(g)).
 \tag{RR.17}
\]

### Theorem 8.1 — two-defect interchange filtration

There are canonical inclusions

\[
 \boxed{D_0\subseteq D_1\subseteq D_2.}
 \tag{RR.18}
\]

The first gap consists of fine-observer execution splices that survive `p`.  The second consists of
new splices created by matching two distinct fine midpoints having the same `p`-observation.

### Proof

Theorem 4.1 gives `D_0=p_*R_q(gf)`.  Theorem 3.1 and monotonicity of direct image give
`D_0 subset D_1`.  For the second inclusion, a witness of `p_*(R;S)` contains one fine midpoint
`b`.  Its image `p(b)` is a valid common midpoint witnessing `(p_*R);(p_*S)`.  Apply this with
`R=R_q(f)` and `S=R_q(g)`.  QED.

### Theorem 8.2 — exactness chambers and converse

1. If `g` preserves the kernel of `q`, then `D_0=D_1` for every `f,p`.
2. If `p` is injective, then `D_1=D_2` for every pair of relations, hence for every `f,g,q`.
3. Conversely, `p_*` preserves composition for every pair of relations exactly when `p` is
   injective.
4. If both hypotheses in items 1 and 2 hold, the whole interchange filtration collapses to one
   relation.

### Proof

Item 1 is Theorem 3.1 followed by direct image.  For item 2, a coarse composite supplies fine
midpoints `b_1,b_2` with `p(b_1)=p(b_2)`; injectivity identifies them and gives one fine composite
witness.

For the converse, suppose `p(x)=p(y)`.  Let `R` be the singleton loop at `x` and `S` the singleton
loop at `y`.  Their pushforwards compose through the common observed midpoint.  If pushforward
preserves composition, `R;S` must have a witness.  This forces `x=y`.  Thus `p` is injective.
QED.

### Proposition 8.3 — independence of the two defects

Both strictness patterns occur.

1. Take the four-state cell of Section 6 and `p=id_B`.  Then `D_0 subsetneq D_1=D_2`: source
   execution creates a splice, while serial observation creates none.
2. Take the same cell with fine observer `q_0=id_X` and further observer
   `p=relationalLawObserver`.  Fine function graphs compose exactly, so `D_0=D_1`, but
   `D_1 subsetneq D_2`: only the coarser midpoint match creates the false history.

Therefore the two gaps are independent invariants.  A scalar total defect cannot determine where
loss entered the execution--observation square.

This is the first frontier-level mechanism extracted from the five open-problem classes in the
current RH map.  It does **not** identify those classes.  It says that whenever a live chart is
literally formed by serial law execution and serial observation, two distinct proof obligations
exist and cannot be merged: executable descent at the current scale and faithful midpoint matching
under the next observer.

## 9. Hostile conjecture/failure loops

| conjecture | verdict | strongest survivor |
|---|---|---|
| every quotient has a deterministic effective law | false by Theorem 2.2 | canonical total effective relation |
| effective relation formation preserves composition | false by Proposition 6.1 | lax inclusion plus splice defect |
| zero splice against a few arbitrary laws proves descent | false without a separating family | constants give an exact converse on nonempty sources |
| coarse-graining monotonically increases branching | false by Proposition 6.2(2) | exact relation pushforward |
| coarse-graining monotonically decreases branching | false by Proposition 6.2(1) | relation, not branch count, is invariant payload |
| branch selection repairs source dynamics | false by Theorem 5.1 | selection is new constitutive data |
| execution loss and observer loss are one scalar defect | false by Proposition 8.3 | canonical two-step inclusion filtration |
| relation pushforward preserves composition | false for every noninjective observer | exact iff the observer is injective |
| relation calculus alone is the universal field | unsupported | exact transition law inside Reflexive Law Mechanics |

## 10. Parent and significance boundary

Direct images of graphs, relations, nondeterministic transition systems, quotient automata,
hyperoperations, and spurious paths in abstract interpretation are classical.  For example,
correctness-kernel work in abstract model checking explicitly retains spurious abstract paths under
domain simplification.  No novelty claim is made for those ingredients.

The theorem's field role is the exact synthesis:

\[
 \text{observer loss}
 \to \text{canonical relational law}
 \to \text{lax execution}
 \to \text{splice defect}
 \to \text{promotion/selection obligation}.
 \tag{RR.16}
\]

It supplies unconditional new-to-corpus leverage and a reusable anti-theatre gate.  Topological,
convex, admission-sensitive, and higher-history extensions remain open.

## 11. Exact scope

- ordinary sets and total functions;
- surjective observers;
- ordinary binary relations;
- no topology, continuity, measure, positivity, cost, recurrence, hypertranscendence, or RH claim;
- no claim that every route supplies the required source function and observer;
- no deterministic selector or promotion principle is chosen.

## 12. Lean certification

Formalize the exact set-level theorem in

`GaloisForLFunctions.HTGeometry.ConstitutiveRelationalLawRenormalization`

and wire it into `GaloisForLFunctions.HTGeometry.UniversalLawField`.  Required declarations:

1. effective relation, relation composition, and pushforward;
2. identity and totality;
3. right-uniqueness iff kernel preservation;
4. lax composition and exactness under later-law descent;
5. constant-prelaw converse;
6. exact observer pushforward;
7. deterministic selector no-go;
8. strict four-state splice, creation, and erasure countermodels;
9. serial observation--execution two-defect filtration;
10. pushforward composition exactness iff observer injectivity;
11. independence of the two interchange gaps;
12. one unconditional capstone.

Completed in the named module and wired into `UniversalLawField`.  Direct elaboration, leaf build,
and umbrella build pass.  Axiom audit reports no axioms for the exactness classifications,
interchange filtration, independence cells, or capstones.  Formalized record:

`docs/drafts/pipeline/3-formalized/universal-law-field/relational-law-renormalization-mechanics/observer-induced-relational-law-lax-composition-and-splice-defect-law-formalized.md`.

## Log

- 2026-08-10 — dependency-closed paper proof completed after hostile comparison with strict quotient
  repair, abstract interpretation, and relation calculus.  Lean formalization opened.
- 2026-08-10 — serial observation--execution interchange added; Lean module and ULF umbrella build
  pass, with axiom-free capstones and independent strict cells for both defect layers.
