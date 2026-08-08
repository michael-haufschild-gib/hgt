# Observer-horizon stability under bounded and compact repair

- **ID:** `observer-horizon-stability-bounded-compact-repair`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / CROSS-ROUTE NO-GO
- **Source:** `../../1-in-progress/noncommuting-exactification-geometry/noncommuting-exactification-geometry-program.md`
- **Statement:** Bounded perturbations preserve the exact multivalued horizon of a nonclosable
  observer, bounded positive form corrections preserve sequential nonclosability, and compact
  perturbations cannot remove a weakly-null precision horizon.

## Goal

Turn the proposed “precision/provenance uncertainty” into a falsifiable repair theorem.  The
result must predict something outside the two-prime Kummer seed.  It applies independently to the
ordinary-`L2` Hedenmalm form in Route C1 and the countable unit-response codiagonal in Route J.

## Gates

- [x] 0 -> 1 in-progress: exact operator, form, and compact-horizon statements fixed
- [x] 1 -> 2 fully-proven: dependency-closed proofs below, `[PROVED HERE]`
- [ ] 2 -> 3 formalized: no Lean authorized in this research turn
- [ ] 3 -> 4 publication-ready: specialist collision review required

## 1. Closed-relation horizon of an observer

Let `X,Y` be Hilbert spaces, let `D subset X` be a linear subspace, and let

\[
 T:D\longrightarrow Y                                                   \tag{1}
\]

be linear.  Its closed graph relation is

\[
 \overline{G(T)}
 =\overline{\{(x,Tx):x\in D\}}^{X\oplus Y}.                              \tag{2}
\]

Define its **multivalued horizon** by

\[
 \operatorname{Hor}(T)
 =\{y\in Y:(0,y)\in\overline{G(T)}\}.                                    \tag{3}
\]

Thus `y in Hor(T)` exactly when there is a sequence `x_n in D` with

\[
 x_n\longrightarrow0\text{ in }X,
 \qquad Tx_n\longrightarrow y\text{ in }Y.                              \tag{4}
\]

The operator is closable exactly when `Hor(T)={0}`.

## 2. Bounded-repair invariance

### Theorem 2.1 `[PROVED HERE]`

For every bounded linear `B:X->Y`,

\[
 \boxed{\operatorname{Hor}(T+B)=\operatorname{Hor}(T).}                  \tag{5}
\]

More strongly, define the bounded invertible shear

\[
 M_B:X\oplus Y\longrightarrow X\oplus Y,
 \qquad M_B(x,y)=(x,y+Bx).                                                \tag{6}
\]

Then

\[
 \overline{G(T+B)}=M_B\bigl(\overline{G(T)}\bigr).                       \tag{7}
\]

Consequently `T+B` is closable if and only if `T` is closable.

### Proof

The inverse of `M_B` is `M_{-B}`, so `M_B` is a homeomorphism.  Directly,

\[
 M_B(x,Tx)=(x,Tx+Bx)=(x,(T+B)x),
\]

hence `M_B(G(T))=G(T+B)`.  Homeomorphisms commute with closure, proving `(7)`.
For a vertical vector, `M_B(0,y)=(0,y)`.  Therefore the vertical parts of the two closed
relations are equal, proving `(5)`.  The closability statement follows from `(3)`.  `QED`

This is exact defect conservation, not only preservation of nonclosability: every horizon vector
survives unchanged.

### Corollary 2.2 — repair typing

No bounded, compact, Hilbert--Schmidt, trace-class, or finite-rank additive correction on the same
ambient Hilbert spaces can make a nonclosable observer closable.  A successful repair must change
at least one of:

1. source domain or its topology;
2. target topology;
3. single-valued-operator type, replacing it by a relation or quotient;
4. source provenance before the nonclosable projection.

The first sentence follows because all listed corrections are bounded.  The second is the
contrapositive classification of what remains available.

## 3. Positive-form horizon invariance

Let `q:D x D -> C` be a nonnegative Hermitian form on a dense subspace `D subset X`.  Say that `q`
is sequentially closable through `X` when every sequence `x_n in D` satisfying

\[
 x_n\to0\text{ in }X,
 \qquad q(x_n-x_m,x_n-x_m)\to0                                    \tag{8}
\]

also satisfies `q(x_n,x_n)->0`.

Let `b:X x X -> C` be a bounded nonnegative Hermitian form.  Thus for some `C>=0`,

\[
 0\le b(x,x)\le C\|x\|^2.                                          \tag{9}
\]

### Theorem 3.1 `[PROVED HERE]`

\[
 \boxed{q+b\text{ is sequentially closable through }X
 \Longleftrightarrow q\text{ is sequentially closable through }X.}      \tag{10}
\]

### Proof

First suppose `q` is not closable.  Choose a witness `x_n` for which `(8)` holds but
`q(x_n,x_n)` does not tend to zero.  Boundedness gives

\[
 b(x_n-x_m,x_n-x_m)\le C\|x_n-x_m\|^2\to0,
 \qquad b(x_n,x_n)\to0.                                                  \tag{11}
\]

Hence `x_n` is `(q+b)`-Cauchy while `(q+b)(x_n,x_n)` does not tend to zero.  Thus `q+b` is not
closable.

Conversely, suppose `q+b` is not closable and let `x_n` be a witness.  Since `q` and `b` are
nonnegative,

\[
 q(x_n-x_m,x_n-x_m)\le(q+b)(x_n-x_m,x_n-x_m)\to0.                        \tag{12}
\]

Again `b(x_n,x_n)->0` by `(9)`.  If `q(x_n,x_n)->0`, then
`(q+b)(x_n,x_n)->0`, contrary to the witness.  Therefore `q` is not closable.  `QED`

### Corollary 3.2 — Route C1 prediction

The corpus proves that every nonzero nonnegative momentum-symmetric theta-null Hedenmalm source
form is sequentially nonclosable through ordinary `L2(R)`.  Theorem 3.1 therefore gives a new
route-level no-go:

> No bounded nonnegative ordinary-`L2` correction can make that form closable.

In particular, finite-rank or compact positive completion terms cannot repair Route C1 inside the
ordinary `L2` chart.  A survivor must use the already-indicated singular common domain, boundary
transgression, relation-valued graph, or a different source topology.

The corpus input is recorded in
`formal/GaloisForLFunctions/RHTower/XiThetaSchwartzL2Nonclosability.lean`; this card does not alter
or rebuild it.

## 4. Compact stability of a precision horizon

### Theorem 4.1 `[PROVED HERE]`

Let `T:D subset X -> Y` be linear.  Suppose there is a sequence `x_n in D` such that

\[
 \|x_n\|=1,
 \qquad x_n\rightharpoonup0,
 \qquad \|Tx_n\|\longrightarrow0.                                      \tag{13}
\]

Then for every compact `K:X->Y`,

\[
 \|(T+K)x_n\|\longrightarrow0.                                         \tag{14}
\]

Consequently no estimate

\[
 \|(T+K)x\|\ge c\|x\|\qquad(x\in D)                                  \tag{15}
\]

can hold with `c>0`.

If `T` is bounded on all of `X`, no compact perturbation `T+K` can be both injective and have
closed range.

### Proof

A compact operator sends a weakly convergent sequence to a norm-convergent sequence with the same
limit.  Hence `Kx_n->0`.  Equation `(14)` follows from `(13)` and the triangle inequality.
The unit vectors in `(13)` contradict `(15)`.  Finally, a bounded injective operator between
Banach spaces has closed range only if its inverse on that range is bounded, equivalently only if
it is bounded below.  `QED`

This theorem contains the mechanism used in the dedicated two-prime Kummer compact-repair no-go,
but is independent of diagonal form and applies to any weakly escaping source packet.

### Corollary 4.2 — Route J prediction

The countable unit-response codiagonal in Route J is proved nonclosable on the canonical
orthogonal `ell2` source.  Theorem 2.1 yields:

> Adding any bounded post-projection reader leaves its entire multivalued horizon unchanged.

Thus no bounded or compact scalar correction after codiagonal fusion can restore a closable
source-global reader.  Any viable post-J successor must act before fusion, retain a principal
relative current, or change to a relation-valued/source-rigged category.  This is a theorem-level
prediction in a route independent of the Kummer example.

The corpus inputs are recorded in
`formal/GaloisForLFunctions/RHTower/HighExponentShellFusionConservation.lean` and the Route-J
frontier card; no Lean was changed or built here.

## 5. All-route repair discriminator

The three theorems separate two superficially similar horizons.

| Horizon witness | Invariant repair class | What can still work |
|---|---|---|
| `x_n->0`, `Tx_n->y!=0` | every bounded additive perturbation preserves `y` exactly | change topology/domain or retain a relation |
| `x_n weak->0`, `||x_n||=1`, `Tx_n->0` | every compact perturbation preserves the singular sequence | noncompact source incidence or stronger topology |
| nonclosable positive form | every bounded positive form correction preserves nonclosability | singular form domain or boundary transgression |

This gives a falsifiable prediction for any route proposal: identify its witness type before
suggesting a repair.  Bounded corrections cannot cure provenance horizons; compact corrections
cannot cure escaping precision horizons.  Confusing the two is exactly the “make one chart precise,
erase another” pattern the new geometry is meant to expose.

## 6. Novelty and scope

Graph shears, form perturbations, compact singular sequences, and their proofs belong to parent
operator theory.  No priority claim is made for the abstract results.  Candidate-new knowledge is
the exact cross-route conservation law and the two new HGT consequences: bounded-positive repair
is impossible for the Route-C1 Hedenmalm chart, and bounded post-fusion repair is impossible for
Route J.

These no-gos do not prove RH.  They remove whole repair classes and force the source-relative,
noncompact, or relation-valued categories required by the live routes.

## Lean return notes

Later formalization should separate:

1. graph-relation shear and vertical-part invariance;
2. sequential nonclosability of nonnegative forms under bounded positive addition;
3. compact preservation of weakly-null singular sequences.

Existing Hedenmalm and Route-J modules provide application witnesses.  Exact reusable declarations
must be found with `scripts/formal_tools.py research` before any Lean work.  No Lean was written or
built here.

## Log

- 2026-08-08 — bounded graph-horizon invariance, bounded-positive form invariance, compact
  precision-horizon stability, and Route-C1/Route-J consequences paper-proved.
