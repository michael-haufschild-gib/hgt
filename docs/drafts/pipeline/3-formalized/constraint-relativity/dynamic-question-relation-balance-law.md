# Dynamic question--relation balance law

- **ID:** `dynamic-question-relation-balance-law`
- **Stage:** 3-formalized
- **Type:** THEOREM / FRAMED LAWSTACK DYNAMICS / LOCAL KINEMATICS
- **Scientific status:** `[PAPER-PROVED] [FORMALIZED IN LEAN] [NOT RH]`
- **Novelty status:** exact sequence is elementary abelian-category algebra. Its role is corrective:
  source dynamics must change potential questions and relations, not only move a fixed constraint
  subspace.
- **Parents:** `../../1-in-progress/constraint-relativity/framed-lawstack-dynamics.md` and
  `../../1-in-progress/constraint-relativity/constraint-relativity-and-relation-completion-spacetime.md`.

## 1. Purpose

Relation-only dynamics is insufficient for hypertranscendence, operator growth, or source fusion.
A source operation can create new possible questions while also converting old freedom into new
law. This card gives exact local balance.

## 2. Setup

Work in an abelian category. Let

\[
 R\subset P\subset P',
 \qquad
 R\subset R'\subset P'.
 \tag{2.1}
\]

Interpret:

- `P,P'`: old and new potential-law objects;
- `R,R'`: old and new relation objects;
- `F=P/R`, `F'=P'/R'`: exposed freedoms.

Define killed old freedom and genuinely new freedom by

\[
 K={P\cap R'\over R},
 \qquad
 C={P'\over P+R'}.
 \tag{2.2}
\]

## 3. Constraint stress sequence

### Theorem 3.1 — exact question--relation balance

There is a natural exact sequence

\[
 \boxed{
 0\longrightarrow K
 \longrightarrow F
 \longrightarrow F'
 \longrightarrow C
 \longrightarrow0.}
 \tag{3.1}
\]

Consequently, in the Grothendieck group,

\[
 \boxed{[F']-[F]=[C]-[K].}
 \tag{3.2}
\]

For finite-dimensional vector spaces,

\[
 \boxed{
 \dim F'-\dim F
 =\dim C-\dim K.}
 \tag{3.3}
\]

#### Proof

Inclusion `P->P'` followed by quotient defines

\[
 \phi:P/R\longrightarrow P'/R'.
\]

Its kernel consists of classes represented by `p in P` whose image lies in `R'`. Hence

\[
 \ker\phi=(P\cap R')/R=K.
 \tag{3.4}
\]

The image is `(P+R')/R'`. Therefore

\[
 \operatorname{coker}\phi
 ={P'/R'\over(P+R')/R'}
 \cong{P'\over P+R'}=C.
 \tag{3.5}
\]

Equations `(3.4)` and `(3.5)` give `(3.1)`. Additivity in the Grothendieck group gives `(3.2)`,
and dimension gives `(3.3)`. QED.

## 4. Three phases

### Pure question creation

If `R'=R` and `P'=P direct-sum C`, then `K=0` and new freedom is exactly `C`.

### Pure relation creation

If `P'=P` and `R subset R'`, then `C=0` and

\[
 K=R'/R,
 \qquad
 F'=F/K.
\]

### Coupled creation

In general, a source operation creates new freedom `C` and kills old freedom `K` simultaneously.
Net dimension can grow, shrink, or remain constant while the oriented event pair `(K,C)` remains
nontrivial. Scalar dimension loses which side changed.

## 5. Composition law

For two nested source operations, the Grothendieck increments add:

\[
 ([F_2]-[F_1])+([F_1]-[F_0])=[F_2]-[F_0].
 \tag{5.1}
\]

However, intermediate killed/created objects need not be recoverable from endpoint difference.
Therefore oriented provenance should retain the two-term event `(K,C)` or the exact sequence
`(3.1)`, not only its `K_0` index.

This is the dynamic analogue of positive-energy orientation loss: net rank is a scalarized shadow
of two distinct source operations.

## 6. Corpus interpretation limits

### Hypertranscendental fusion

Corpus fusion theorems show finite source operations force analytic carriers outside every finite
differential prefix and give exact rank growth. This is consistent with nonzero creation term `C`
and vanishing closure term `K` on selected graded pieces. An explicit functor from fusion fields to
`(3.1)` remains to be constructed; this card does not reprove the HT result.

### RH route proliferation

Adding a new carrier can make `P'` larger without killing horizontal freedom. After quotienting
observer charts by source isogeny, repeated detectors need not contribute independent `C`. A
decisive source law needs nonzero killed-freedom term on horizontal class, not raw target growth.

### Quantum operator growth

Commutator/Krylov growth enlarges low-resource question space. Exact unitary dynamics transports
full relations, while resource-filtered intersections change. Matching this to `(3.1)` requires a
nested filtration and is not automatic for a moving nonnested subspace.

## 7. Falsifiable extension problem

Construct an exact-category or quasi-abelian version in which:

1. `K` records strict source relation creation;
2. `C` records genuinely new coefficient-faithful questions after source-isogeny quotient;
3. bornological closure does not erase nonclosed-range information;
4. multi-filtration gives a rank surface whose mixed increments are event classes, not only
   integers;
5. source dynamics supplies a conservation or field equation coupling `(K,C)` to provenance
   curvature.

Failure to couple this sequence to at least two other lawstack gates leaves it elementary
bookkeeping, not new field mathematics.

## 8. Lean handoff notes

No Lean code was written or built. Later formalization can use submodule quotient exactness and
finite-dimensional dimension formulas. Keep the source-isogeny, bornological, and HT/RH
interpretations separate until their comparison functors exist.

## Formalized companion

`dynamic-question-relation-balance-law-formalized.md` (same directory).
