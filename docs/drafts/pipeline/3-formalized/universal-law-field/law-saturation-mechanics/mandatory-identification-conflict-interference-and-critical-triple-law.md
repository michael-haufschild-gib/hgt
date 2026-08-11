# Mandatory-identification conflict interference and critical-triple law

- **ID:** ULF-LSM-5
- **Stage:** 3-formalized
- **Type:** ROUTE-INDEPENDENT MECHANISM THEOREM
- **Status:** [PAPER-PROVED] [LEAN-PROVED] [DEPENDENCY-CLOSED]
  [IDENTIFICATION--SEPARATION INTERFERENCE] [CRITICAL TRIPLE] [EXACT TV REPORTER] [NOT RH]

## 1. Mechanism, not object

Let `P` be a finite source set.  A family of mandatory identifications is a relation

\[
R\subseteq P\times P.
\]

It need not already be symmetric or transitive.  Its executable closure is the equivalence
relation

\[
E_R=\operatorname{EqvGen}(R).
\tag{1}
\]

Let `J` be a set of observational tasks.  Task `j` is a pair of nonnegative profiles
`u_j,v_j:P\to\mathbb R_{\ge 0}`.  Write `d_j=u_j-v_j`.  The task-conflict relation is

\[
x\mathrel{C_{u,v}}y
\quad\Longleftrightarrow\quad
\exists j\in J:\ d_j(x)d_j(y)<0.
\tag{2}
\]

Thus `R` says which distinctions a formation must erase, while `C_{u,v}` says which distinctions
total-variation fidelity must retain.  These are opposite laws.  Their interference, rather than
either structure separately, is the subject of this theorem.

For an observer `\kappa:P\to K`, write

\[
\operatorname{Respects}(R,\kappa)
\quad\Longleftrightarrow\quad
R(x,y)\Rightarrow \kappa(x)=\kappa(y).
\tag{3}
\]

The observer is **lossless** when every task preserves total variation after fibre summation.
The already-certified conflict-coloring law says this is equivalent to

\[
C_{u,v}(x,y)\Rightarrow \kappa(x)\ne\kappa(y).
\tag{4}
\]

## 2. Identification saturation law

### Theorem 2.1

For every map `\kappa:P\to K`,

\[
\operatorname{Respects}(R,\kappa)
\quad\Longleftrightarrow\quad
\operatorname{Respects}(E_R,\kappa).
\tag{5}
\]

Consequently, all consequences of mandatory identifications are forced before any observer width,
positivity, topology, or target representation is chosen.

### Proof

The reverse implication follows from `R\subseteq E_R`.  For the forward implication, induct on the
generation of `E_R`: relation steps are respected by hypothesis; reflexive steps by reflexivity of
equality; symmetric steps by symmetry of equality; and concatenated steps by transitivity of
equality. ∎

## 3. Exact interference classification

Call `(R,u,v)` **compatible** when

\[
E_R(x,y)\Longrightarrow\neg C_{u,v}(x,y).
\tag{6}
\]

### Theorem 3.1 — existence classification

The following are equivalent.

1. There exist a finite observer set `K` and `\kappa:P\to K` that respects `R` and is lossless for
   every task.
2. `(R,u,v)` is compatible.
3. The canonical quotient observer
   \[
   q_R:P\longrightarrow P/E_R
   \tag{7}
   \]
   is lossless.

### Proof

If `\kappa` respects `R`, Theorem 2.1 makes it constant on every `E_R`-class.  If a conflict edge
lay inside one class, `\kappa` would collapse that edge, contradicting the conflict-coloring
criterion.  Hence item 1 implies item 2.

Assume item 2.  The quotient map identifies exactly the pairs in `E_R`; none is a conflict pair by
compatibility.  It is therefore a proper coloring of the conflict graph and hence lossless.  This
proves item 3.  The quotient of finite `P` is finite, so item 3 implies item 1. ∎

This is a complete finite consistency test.  It does not search target objects: it computes whether
the two laws can coexist.

## 4. Critical-path and quantitative reporter laws

### Theorem 4.1 — finite certificate

Incompatibility is equivalent to a finite certificate consisting of

1. a conflict edge `(x,y)`; and
2. a finite `R`-zigzag from `x` to `y`, allowing reversed relation steps.

Every observer respecting `R` collapses the entire zigzag and therefore identifies `x` with `y`.

### Proof

An `EqvGen(R)` derivation is built by finitely many relation, reflexive, symmetric, and transitive
steps.  Delete reflexive repetitions and expand transitive steps to obtain the zigzag.  Conversely,
every such zigzag is an `EqvGen(R)` derivation.  Theorem 2.1 makes every respecting observer constant
along it. ∎

### Theorem 4.2 — strict numerical response

Suppose the certificate's conflict edge is witnessed by task `j`:

\[
d_j(x)d_j(y)<0.
\tag{8}
\]

Then every finite observer respecting `R` has strict total-variation loss on task `j`:

\[
\operatorname{TV}(\kappa_!u_j,\kappa_!v_j)
<
\operatorname{TV}(u_j,v_j).
\tag{9}
\]

### Proof

The critical path forces `\kappa(x)=\kappa(y)`.  The certified collapsed-conflict theorem then gives
(9): the positive and negative parts overlap strictly in that observer fibre. ∎

The reporter is therefore not a declared scalar curvature.  It is the exact TV quantity already
fixed before the identification formation.  A critical path forces its strict change.

## 5. Quotient-width law

Assume compatibility.  Put one vertex in the quotient conflict graph `\overline C_R` for every
`E_R`-class and join two distinct classes when any representatives conflict.  This is well-defined
as a simple graph.

### Theorem 5.1

For every `q\in\mathbb N`, the following are equivalent.

1. There is a lossless observer `\kappa:P\to\operatorname{Fin}(q)` respecting `R`.
2. The quotient conflict graph `\overline C_R` is `q`-colorable.

Hence the least observer width after mandatory identification is exactly

\[
\chi(\overline C_R).
\tag{10}
\]

### Proof

Every respecting observer factors uniquely through `q_R` by Theorem 2.1.  The factor is lossless
exactly when it separates every quotient conflict edge, namely exactly when it is a proper coloring.
Taking the least number of used labels gives (10). ∎

Compatibility and width are different invariants.  Compatibility asks whether any legal observer
exists; width measures how much target alphabet remains necessary after all forced contractions.

## 6. Pairwise-compatible but jointly impossible doctrines

Let `R_1,R_2` be two mandatory-identification relations and let

\[
R_1\vee R_2:=\operatorname{EqvGen}(R_1\cup R_2).
\tag{11}
\]

### Theorem 6.1 — critical triple criterion

Assume `(R_1,u,v)` and `(R_2,u,v)` are each compatible, but there are conflict endpoints `x,y`
connected by an `(R_1\cup R_2)`-zigzag.  Then:

1. the `R_1` formation and fidelity doctrine have a joint realization;
2. the `R_2` formation and fidelity doctrine have a joint realization;
3. the two identification formations have a joint realization, for example their common quotient;
4. all three doctrines have no joint realization;
5. every observer respecting both formations has strict TV loss for a witnessing conflict task.

Thus pairwise compatibility does not imply joint compatibility.  The obstruction is not stored in
any one doctrine: it is born when their generated identification paths close across a forbidden
edge.

### Proof

Items 1 and 2 follow from Theorem 3.1.  The quotient by `R_1\vee R_2` supplies item 3 without any
fidelity requirement.  The assumed zigzag puts a conflict edge inside one generated equivalence
class, so Theorems 3.1 and 4.2 give items 4 and 5. ∎

## 7. Smallest exact countermodel

Take `P={0,1,2}`, one task

\[
u=\delta_0,\qquad v=\delta_2,
\tag{12}
\]

and mandatory identifications

\[
R_1:0\sim1,qquad R_2:1\sim2.
\tag{13}
\]

The only conflict edge is `{0,2}`.  Quotienting by `R_1` preserves that distinction, as does
quotienting by `R_2`.  The joint generated relation contains

\[
0\sim_{R_1}1\sim_{R_2}2,
\]

so every joint observer is constant on all three points.  Numerically,

\[
\operatorname{TV}(\delta_0,\delta_2)=1,
\qquad
\operatorname{TV}(\kappa_!\delta_0,\kappa_!\delta_2)=0.
\tag{14}
\]

Every proper subfamily of the three doctrines is realizable; the full family is not.  Three source
states are minimal: two states cannot support two individually harmless nontrivial identifications
whose generated join newly collapses a conflict pair.

## 8. Mechanism laws extracted

1. **Identification-saturation law.** Executability propagates supplied equalities through their
   equivalence closure.
2. **Fidelity-separation law.** Positive task pairs generate distinctions that every lossless
   observer must retain.
3. **Interference law.** Joint realizability is exactly disjointness of generated identifications
   and forbidden conflicts.
4. **Critical-path law.** Every failure has a finite path certificate, even when no individual
   formation is at fault.
5. **Quantitative-response law.** A closed critical path forces strict loss in a predeclared TV
   reporter.
6. **Residual-width law.** After compatible contraction, observer complexity is chromatic width of
   the quotient conflict graph.
7. **Critical-triple law.** Pairwise-realizable formations can be jointly impossible because their
   closures compose before fidelity is tested.

These laws are the field content.  Equivalence relations, graph contraction, coloring, and total
variation are local coordinate systems for them.

## 9. Parent boundary and scope

Equality/disequality constraint systems, signed-graph balance, congruence generation, graph
contraction, and coloring are classical parents.  Harary's balance theory is an early graph-level
parent: <https://doi.org/10.1307/mmj/1028989917>.  The present theorem makes no priority claim for
those ingredients.  Corpus-specific significance is their exact coupling to the positive-overlap
TV reporter and to law-formation critical triples.

The theorem is finite and set-based.  It does not yet prove:

- topological closedness of generated identifications;
- cofinal compatibility when every finite stage is compatible;
- differential or analytic formation of conflicts;
- source generation of three independent corpus doctrines;
- any RH endpoint or selector.

The next field question is not which additional object to attach.  It is which laws decide when
identification closure, completion, positivity, prolongation, and history formation preserve or
create conflict paths.

## 10. Lean certificate

Module `GaloisForLFunctions.HTGeometry.ConstitutiveIdentificationConflictInterference` certifies:

- respect of a relation iff respect of `Relation.EqvGen`;
- canonical quotient losslessness iff exact identification--conflict compatibility;
- respecting width-`q` observer existence iff quotient-conflict `q`-colorability;
- generated and joined identification conflicts force strict TV loss;
- each identification doctrine in the three-point model separately admits a lossless observer;
- no finite observer can jointly respect both and remain lossless;
- a capstone theorem packages saturation and compatibility;
- state-minimality of the three-point critical triple, through the two-state lemmas
  `finTwo_relation_diagonal_of_compatible` and `finTwo_pairwiseCompatible_joinCompatible` in the
  sibling module `HTGeometry.ConstitutiveEndogenousUnitizationInterference`.

Direct foreground elaboration and formal lint pass.  The final foreground build of
`GaloisForLFunctions.HTGeometry.UniversalLawField` passes with 11,519 jobs.  Axiom prints report no
axioms for pure equivalence saturation and only `propext`, `Classical.choice`, and `Quot.sound` for
the finite quotient/TV theorems.  No computation, added axiom, placeholder, `opaque`, or `unsafe`
declaration is used.
- 2026-08-11 — Lean surface audited complete against the card, including two-state minimality; promoted to stage 3.
