# Two-sided singular defects in pre-quasi Gelfand triples

- **ID:** `pre-quasi-gelfand-two-sided-singular-defect`
- **Stage:** 4-publication-ready
- **Type:** FALSIFICATION / CLASSIFICATION THEOREM (paper)
- **External target:** Skrepek, *Quasi Gelfand Triples*, IEOT 97 (2025),
  Conjectures 6.7 and 6.8
- **Exact claim:** Hilbert pre-quasi Gelfand triples need not be quasi.  Proper defects are exactly
  proper closed subspaces of a canonical singular graph with both coordinate projections dense;
  a codimension-one defect exists exactly when the canonical operator is unbounded and not bounded
  below.

## Status labels

- `[LITERATURE]` Skrepek's Conjecture 6.7 asserts every Hilbert pre-quasi Gelfand triple is quasi;
  Conjecture 6.8 asserts the Banach analogue.
- `[LOCAL-RESEARCH]` Corpus contains ordinary rigged triples, graph-closure vertical-fibre laws,
  and dense-core relation saturation, but no pre-quasi/quasi discriminator or attack on these
  conjectures.
- `[PAPER-PROVED]` Exact classification, sharp criterion, and explicit counterexample have a
  dependency-closed proof below.
- `[OPEN CORE]` None in the paper theorem.
- `[NOVELTY UNVERIFIED]` Exact-phrase, parent-theory, citation-descendant, and
  equivalent-formulation searches found no resolution through 2026-08-03. Priority remains
  provisional pending independent expert and MathSciNet/zbMATH review.

## Explicit counterexample

Let all three Hilbert spaces be `ell2(N)` with their standard duality.  On even/odd coordinates set

```text
b_(2k)   = k+1,
b_(2k+1) = 1/(k+1),
B = diag(b_n),
A = B^(-1).
```

On the graph domain of `B`, define

```text
c_(2k)   = 1,
c_(2k+1) = 1/(k+1),
L(x) = sum_n c_n x_n,
D = ker L.
```

The candidate embeddings are

```text
i_+ = A : dom A -> ell2,
i_- = B|D : D -> ell2.
```

The coefficient tests are designed so that `L` is graph-norm continuous, while `c` and `c/b` are
both outside `ell2`.  Therefore `D` and `B(D)` should both be dense in `ell2`, although `D` is a
proper graph-closed codimension-one subspace.  The pairing identity is

```text
<i_- g, i_+ f> = <B g, A f> = <g,f>.
```

Since `dom(i_+^*) = dom A = ran B` but `ran(i_-) = B(D)` is proper, this is pre-quasi but not quasi.

## Proposed classification

Let `A : dom A subset X_+ -> X_0` be a closed densely defined injective operator with dense range,
after identifying the Hilbert anti-dual `X_-` with `X_+`.  Put

```text
B = (A^*)^(-1).
```

Every compatible pre-quasi negative embedding is a closed restriction of `B`.  Its graph is a
closed subspace `M` of `graph B` whose two coordinate projections are dense.  Conversely every such
`M` gives a pre-quasi triple.  It is quasi exactly when `M = graph B`.

For the graph Hilbert space `G(B)`, write `P(x,Bx)=x` and `Q(x,Bx)=Bx`.  A codimension-one defect
`M=v^perp` has both projections dense exactly when

```text
v notin ran(P^*) union ran(Q^*).
```

Such a `v` exists exactly when neither adjoint is surjective, equivalently when `B` is unbounded and
not bounded below.  This is the proposed sharp boundary between automatic quasi triples and
singular defective triples.

## Complete paper proof

All Hilbert spaces below are complex and inner products are linear in the first variable.  The real
case is identical.  `Graph(B)` always carries

```text
<(x,Bx),(y,By)>_B = <x,y> + <Bx,By>.
```

### Lemma 1: canonical partner and adjoint domain

Let `B : dom B subset H -> K` be closed, densely defined, injective, and have dense range.  Then
`B*` is closed, densely defined, injective, and has dense range.  Hence

```text
A = (B*)^(-1) : ran(B*) subset H -> K
```

is closed, densely defined, injective, and has dense range.  Moreover

```text
dom(A*) = ran(B),                 A*(Bx)=x.              (1)
```

**Proof.**  Closedness and dense definition of `B*` are standard for a closed densely defined
operator.  `ker(B*)=(ran B)^perp=0`, and
`closure(ran B*)=(ker B)^perp=H`.  Taking an inverse exchanges graph coordinates, so `A` is closed;
its domain is `ran B*`, its kernel is zero, and its range is `dom B*`, which is dense in `K`.

For completeness, prove `(1)` without invoking relation calculus.  Write `f=B*y`, so `Af=y`.
An element `z in K` lies in `dom A*` exactly when there is `h in H` such that

```text
<y,z>_K = <B*y,h>_H                 for every y in dom(B*).
```

This is exactly `h in dom(B**)` and `B** h=z`.  Since `B` is closed, `B**=B`; hence `z=Bh`.
The converse follows from the same equality.  Therefore `dom A*=ran B` and `A*(Bh)=h`.  QED.

### Theorem 2: graph-subspace classification

With `A,B` as in Lemma 1, let `C : dom C subset H -> K` be closed, densely defined, injective,
have dense range, and satisfy

```text
<Cg,Af>_K = <g,f>_H                  (g in dom C, f in dom A).   (2)
```

Then `C` is a restriction of `B`.  The assignment

```text
C |-> graph(C)
```

is a bijection between such compatible negative embeddings and closed subspaces `M` of `Graph(B)`
for which both coordinate projections

```text
P(M) subset H,        Q(M) subset K,
P(x,Bx)=x,            Q(x,Bx)=Bx
```

are dense.  The associated pre-quasi Gelfand triple is quasi exactly when `M=Graph(B)`.

**Proof.**  The canonical pair satisfies `(2)`: if `f=B*y`, then

```text
<Bg,Af> = <Bg,y> = <g,B*y> = <g,f>.
```

For arbitrary `C`, subtract this identity from `(2)`.  Since `ran A=dom B*` is dense in `K`,

```text
<Cg-Bg,Af>=0 for every f in dom A
```

forces `Cg=Bg`; hence `C subset B`.  Its graph is therefore a subspace of `Graph(B)`, closed in the
graph Hilbert space exactly when it is closed in `H x K`.  Dense domain and dense range are exactly
density of `P(M)` and `Q(M)`.  Conversely any closed `M` with both projections dense is the graph of
the closed restriction `B|P(M)`; injectivity follows from injectivity of `P`, and `(2)` follows from
the canonical identity.

By Lemma 1, the Skrepek quasi condition is

```text
ran C = dom A* = ran B.                                  (3)
```

Since `B` is injective and `C subset B`, equality `(3)` holds exactly when `dom C=dom B`, equivalently
when `M=Graph(B)`.  QED.

### Theorem 3: sharp two-sided singularity criterion

Under Lemma 1's hypotheses, a proper compatible `C` as in Theorem 2 exists if and only if

```text
B is unbounded and there is no c>0 with ||Bx|| >= c||x||
for every x in dom B.                                    (4)
```

When `(4)` holds, one may choose `graph C` to have codimension one in `Graph(B)`.  Equivalently,
every Hilbert pre-quasi triple with fixed positive embedding `A` is quasi if and only if its
canonical negative embedding `B=(A*)^(-1)` is bounded or bounded below.

**Proof.**  Regard `P : Graph(B)->H` and `Q : Graph(B)->K` as bounded operators.  They are injective
and have dense range.  For any bounded injective dense-range operator `T:G->L`,

```text
T* is onto  iff  T is bounded below.                      (5)
```

Indeed, if `T` is bounded below, its range is closed and hence, by density, equals `L`; its bounded
inverse makes `T*` onto.  Conversely, if `T*` is onto, the open mapping theorem gives `c>0` such
that every `z in G` has a preimage `y` with `T*y=z` and `||y||<=c||z||`; consequently

```text
||z||^2 = <T*y,z> = <y,Tz> <= c||z||||Tz||.
```

Thus `T` is bounded below.

Now `P` is bounded below exactly when `B` is bounded.  One direction is immediate from the graph
norm.  In the other, a graph-norm lower bound for `P` gives `||Bx||<=C||x||` on `dom B`; the bounded
extension to all of `H` has graph contained in the closed graph of `B`, so `dom B=H`.  Similarly,
`Q` is bounded below exactly when `B` is bounded below.

If either condition holds and `M` is a closed subspace of `Graph(B)`, the corresponding coordinate
image `P(M)` or `Q(M)` is closed.  If both coordinate images are dense, that image is the full
target; injectivity of the coordinate projection then forces `M=Graph(B)`.  Thus no proper
compatible restriction exists.

Assume `(4)`.  By `(5)`, `ran P*` and `ran Q*` are proper linear subspaces of `Graph(B)`.  A vector
space over `R` or `C` is not the union of two proper linear subspaces, so choose

```text
v notin ran P* union ran Q*.
```

Let `M=v^perp`.  It is a proper closed codimension-one subspace.  If `h` is orthogonal to `P(M)`,
then `P*h in M^perp=span{v}`.  Since `v notin ran P*`, this forces `P*h=0`; density of `ran P` gives
`h=0`.  Hence `P(M)` is dense.  The identical argument with `Q` proves `Q(M)` dense.  Theorem 2 now
produces the required proper compatible embedding.  QED.

### Corollary 4: explicit counterexample to Conjectures 6.7 and 6.8

Let `H=ell2(N)` and, for `k>=0`, set

```text
b_(2k)=k+1,                     b_(2k+1)=1/(k+1),
c_(2k)=1,                       c_(2k+1)=1/(k+1).
```

Let `B` be the maximal diagonal multiplication operator by `b`, and let `A=B^(-1)`.  On `dom B`
define

```text
L(x)=sum_n c_n x_n,             D=ker L.                 (6)
```

Then `(H,H,H)` with embeddings `i_+=A` and `i_-=B|D` is a Hilbert pre-quasi Gelfand triple which is
not a quasi Gelfand triple.

**Proof.**  A maximal real diagonal multiplication operator on `ell2` is self-adjoint: testing the
adjoint identity on finite coordinate vectors shows that every adjoint-domain vector `y` has
`(b_n y_n) in ell2`, which is exactly `dom B`.  The same holds for `A`; both are closed, densely
defined, injective, and have dense range, with `A=B^(-1)`.

The functional `(6)` is graph-norm continuous because

```text
sum_n |c_n|^2/(1+b_n^2)
 = sum_k 1/(1+(k+1)^2)
   + sum_k (k+1)^(-2)/(1+(k+1)^(-2))
 < infinity.                                                   (7)
```

Thus `D` is a proper graph-closed hyperplane and `B|D` is closed.  A graph-continuous functional
on a dense operator domain has pivot-dense kernel exactly when it is not pivot-norm continuous:
if the kernel closure were proper, a nonzero continuous functional annihilating it would be a
scalar multiple of the original functional on the one-dimensional quotient, and conversely.
Here `c notin ell2` because its even coordinates equal one, so `L` is not pivot-continuous and `D`
is dense in `H`.

Under `B`, the transported functional has coefficients `c_n/b_n`.  They equal `1/(k+1)` on even
coordinates and one on odd coordinates, hence `c/b notin ell2`.  The same kernel lemma shows that

```text
B(D)=ker(L compose B^(-1))
```

is dense in `H`.  Therefore `i_-` is closed, densely defined, injective, and dense-range.  For
`g in D` and `f in dom A`, self-adjoint inverse duality gives

```text
<i_-g,i_+f>=<Bg,Af>=<g,f>,
```

so the triple is pre-quasi.  Finally, `dom(i_+*)=dom A=ran B`, while `ran(i_-)=B(D)` is proper in
`ran B` because `D` is proper and `B` injective.  Hence it is not quasi.  This falsifies the weak
Hilbert conjecture and therefore also the strong conjecture.  QED.

## Exact frontier and priority audit, 2026-08-03

- `[LITERATURE]` Skrepek's published Definition 4.1 and Conjectures 6.7--6.8 use exactly the
  hypotheses attacked above; the counterexample is not an arXiv-version mismatch.
- `[LITERATURE]` Cojuhari--Gheondea classify *triplets of closely embedded Hilbert spaces*, which
  already impose the full adjoint-domain compatibility.  Their Hamiltonian model is the `M=Graph B`
  case, not a proof that every pre-triple has `M=Graph B`.
- `[LITERATURE]` Canonical regular/singular decompositions of linear relations classify the
  multivalued part after graph closure.  They do not classify proper graph-closed restrictions with
  both coordinate projections dense, nor resolve Skrepek's pre-quasi compatibility conjecture.
- `[LITERATURE]` The two citation descendants returned by the current citation index are Philipp--
  Reis--Schaller's port-Hamiltonian construction, which starts from a completed quasi triple, and
  Skrepek--Pauly's PDE-specific weak-equals-strong theorem.  Neither proves or falsifies the abstract
  conjectures.
- `[LOCAL-RESEARCH]` Exact corpus search found one citation to quasi Gelfand triples and no attack on
  pre-quasi triples.  Existing graph-closure and dense-core saturation results concern multivalued
  closures after fixing one pivot topology; they do not contain the bi-dense graph-hyperplane
  mechanism.
- `[NOVELTY UNVERIFIED]` Exact-phrase, title-descendant, closed-restriction, closely-embedded,
  boundary-trace, and linear-relation searches found no prior counterexample or the sharp criterion
  `(4)`.  Priority remains provisional pending independent expert review and a broader bibliographic
  database audit.

## Hostile paper-proof audit

Verdict: `SURVIVES PRELIMINARY ATTACK` and `[PAPER-PROVED]`.

1. **Duality-convention attack:** explicit counterexample uses the standard complete Hilbert
   anti-dual pair, so no normalization theorem is needed to falsify either conjecture.  Abstract
   classification is stated in this normalized setting and does not overclaim the Banach case.
2. **Canonical-partner attack:** Lemma 1 proves every closedness, domain, injectivity, density, and
   adjoint-domain assertion directly; no inverse-adjoint identity is assumed without proof.
3. **Special-example attack:** Theorem 2 proves both directions of the graph-subspace
   correspondence.  Counterexample is a corollary, not the source of the classification.
4. **Closed-range attack:** Theorem 3 proves `T*` surjective iff `T` is bounded below via the open
   mapping theorem and a direct norm estimate.  It then derives the exact `P`/`Q` criteria.
5. **Density attack:** codimension-one construction proves density by orthogonal complements.  In
   explicit model, density is independently checked from non-`ell2` coefficient sequences on both
   coordinate sides.
6. **Definition attack:** published 2025 Definition 4.1 requires precisely closed, densely defined,
   injective, dense-range embeddings plus pairing identity.  It imposes no maximality condition that
   would exclude a proper graph-closed restriction.
7. **Rediscovery attack:** closely embedded triplets assume full compatibility; canonical linear-
   relation decompositions start after a relation is fixed; two indexed citation descendants use
   completed quasi triples or prove a PDE-specific equality.  None contains this counterexample.
8. **Significance attack:** falsifying two explicit published conjectures is independently
   meaningful.  Sharp criterion explains exact failure mechanism and identifies the maximal
   positive survivor: automatic quasi-ness holds precisely outside simultaneous ultraviolet and
   infrared singularity.
9. **Overreach attack:** result does not claim PDE weak/strong trace definitions always differ.  It
   proves abstract implication advertised for a positive solution cannot hold, while leaving
   Skrepek--Pauly's strongly Lipschitz equality intact.
10. **Theatre check:** mathematical deltas are explicit counterexample, exact graph-subspace
    classification, and sharp iff criterion.  Card motion and terminology are not counted.

## No-go closure and positive survivor

- **Exact killing theorem/mechanism:** the two-channel diagonal hyperplane gives a Hilbert
  pre-quasi triple which is not quasi, falsifying both published conjectures.
- **Strongest positive survivor:** automatic quasi compatibility holds exactly when canonical
  graph is not two-sided singular; equivalently, its inverse-adjoint operator is bounded or
  bounded below.
- **New insight:** failure is possible precisely from simultaneous ultraviolet and infrared
  singularity. Every failure regime already admits graph-codimension-one defect.
- **Status:** paper-proved, Lean-formalized, manuscript and hostile review publication-ready.

## Lean gate

Passed exact formal surface: abstract graph-subspace theorem, sharp two-sided-singularity
criterion, and explicit unconditional infinite-dimensional `ell2` counterexample. Direct
foreground elaboration and targeted module build pass. Axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`; forbidden-token scan is empty. Module is wired into
`GaloisForLFunctions.RHTower`. Global lint reaches unrelated pre-existing `HTGeometry` umbrella
reachability failures; none names this route.

## Log

- 2026-08-03 — external frontier exposed Skrepek Conjectures 6.7--6.8; froze two-sided singular
  graph-defect candidate and explicit alternating diagonal attack.
- 2026-08-03 — complete proof closed and survived ten-point hostile audit; promoted to Stage 2.
- 2026-08-03 — exact theorem surface formalized unconditionally in Lean; direct elaboration,
  targeted build, and axiom audit passed; promoted through Stage 3.
- 2026-08-03 — ten-page LaTeX paper compiled and visually audited; collision audit, claim trace,
  and hostile referee report completed; promoted to Stage 4.
