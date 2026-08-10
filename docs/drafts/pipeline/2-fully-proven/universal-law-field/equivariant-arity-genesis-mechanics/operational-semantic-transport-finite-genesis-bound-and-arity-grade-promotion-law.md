# Operational semantic transport, finite-genesis bound, and arity-grade promotion law

- **ID:** ULF-EST-1
- **Stage:** 2-fully-proven
- **Type:** ROUTE-INDEPENDENT MECHANISM THEOREM
- **Status:** [PAPER-PROVED] [DEPENDENCY-CLOSED] [MECHANISM NOT OBJECT]
  [SEMANTIC TRANSPORT] [SHARP FINITE BOUND] [SYMMETRY-CLOSED ARITY PROMOTION]
  [CLASSICAL PARENT INGREDIENTS] [LEAN CLOSED] [NOT RH]

## 1. Operational semantics of a reporter

Let

\[
q:X\to Y,\qquad r:X\to Z
\]

be reporters.  Define the monoid of interventions invisible to `q` by

\[
\operatorname{Inv}(q)
=\{u:X\to X:q(ux)=q(x)\text{ for every }x\}.
\tag{EST.1}
\]

Say that `r` is **determined by `q`**, written `r\preceq q`, when

\[
q(x)=q(y)\Longrightarrow r(x)=r(y).
\tag{EST.2}
\]

This fibrewise definition avoids an irrelevant choice of values outside the attained range of
`q`.  Equivalently, `r` factors uniquely through the attained-image quotient of `q`.

## 2. Exact semantic-transport theorem

### Theorem 2.1 -- operational novelty criterion

For arbitrary sets `X,Y,Z`,

\[
\boxed{
r\preceq q
\quad\Longleftrightarrow\quad
\operatorname{Inv}(q)\subseteq\operatorname{Inv}(r).}
\tag{EST.3}
\]

If `q\oplus r:x\mapsto(qx,rx)`, then

\[
\operatorname{Inv}(q\oplus r)
=\operatorname{Inv}(q)\cap\operatorname{Inv}(r).
\tag{EST.4}
\]

Consequently

\[
\boxed{
\operatorname{Inv}(q\oplus r)\subsetneq\operatorname{Inv}(q)
\quad\Longleftrightarrow\quad
r\not\preceq q.}
\tag{EST.5}
\]

When the inclusion is strict, an excluded intervention can always be chosen to overwrite exactly
one state.

### Proof

Assume `r\preceq q` and let `u in Inv(q)`.  For every `x`, equation `(EST.1)` gives
`q(ux)=q(x)`, so `(EST.2)` gives `r(ux)=r(x)`.  Thus `u in Inv(r)`.

Conversely, assume `Inv(q) subset Inv(r)`.  If `q(x)=q(y)`, define

\[
u_{x\rightsquigarrow y}(z)=
\begin{cases}
y,&z=x,\\
z,&z\ne x.
\end{cases}
\tag{EST.6}
\]

The only changed value remains in the same `q`-fibre, hence `u_(x->y) in Inv(q)`.  By the assumed
inclusion it lies in `Inv(r)`, and evaluation at `x` gives `r(y)=r(x)`.  Therefore `r\preceq q`.

Equation `(EST.4)` follows componentwise.  If `r\preceq q`, `(EST.3)` and `(EST.4)` give equality
with `Inv(q)`.  If not, choose `x,y` with equal `q`-value and unequal `r`-value.  The overwrite
`u_(x->y)` lies in `Inv(q)` but not `Inv(r)`, proving strictness and `(EST.5)`.  QED.

The theorem gives a non-circular definition of semantic reporter birth:

> a born reporter changes future law exactly when it forbids a transformation that was legal under
> the previous reporter doctrine.

## 3. Sharp finite-carrier genesis bound

Let `X` be finite and nonempty.  Begin with a reporter `Q_0:X->Y_0`.  At step `j+1`, pair the
cumulative reporter with `r_(j+1)`:

\[
Q_{j+1}=Q_j\oplus r_{j+1}.
\tag{EST.7}
\]

Call the step effective when `r_(j+1) not\preceq Q_j`, equivalently when `(EST.5)` is strict.

### Theorem 3.1 -- exact termination rank

If `b=|im Q_0|`, every history of effective births has length at most

\[
\boxed{|X|-b.}
\tag{EST.8}
\]

For a constant initial reporter the bound is `|X|-1`, and it is sharp for every finite nonempty
`X`.

### Proof

Every `Q_(j+1)`-fibre lies in a `Q_j`-fibre.  Effectiveness supplies `x,y` in one `Q_j`-fibre with
different `r_(j+1)` values, so that fibre splits into at least two nonempty `Q_(j+1)`-fibres.
Therefore

\[
|\operatorname{im}Q_{j+1}|\ge|\operatorname{im}Q_j|+1.
\tag{EST.9}
\]

After `m` steps, `b+m≤|im Q_m|≤|X|`, proving `(EST.8)`.

For sharpness, enumerate `X={x_1,...,x_d}`.  Starting from the constant reporter, successively add
the Boolean tests `r_j(x)=[x=x_j]` for `1≤j<d`.  After `j` steps the fibres are the `j`
singletons `{x_1},...,{x_j}` and their nonempty complement.  Every step is effective, giving
exactly `d-1` births.  QED.

### Corollary 3.2 -- bounded-arity no-go

Let `D` be a finite alphabet and let all tests have arity at most `M`.  Externalize their inputs as

\[
\operatorname{Ctx}_{\le M}(D)=\coprod_{k=0}^{M}D^k.
\tag{EST.10}
\]

This is a finite carrier of size

\[
\sum_{k=0}^{M}|D|^k.
\]

Any cumulative test-genesis process whose semantic effect is solely refinement of reporters on
this fixed context carrier has fewer than that many effective births.  Hence an unbounded effective
history over finite `D` must use unbounded arity/history length, change admission or carrier, or use
a semantic mechanism not reducible to cumulative reporter refinement.

This conclusion is restricted to the stated mechanism class.  Finite carriers can support other
nonmonotone dynamics, but not an infinite chain of genuinely new cumulative reporter distinctions.

## 4. Arity-grade escape mechanism

Let `I` be finite and `A` an abelian group.  Put

\[
\mathcal L_I=A^{\mathcal P(I)}.
\tag{EST.11}
\]

An element `f` assigns a coefficient to every finite interaction support.  At horizon `m`, observe

\[
Q_m(f)=\bigl(f(S)\bigr)_{|S|\le m}.
\tag{EST.12}
\]

Let the invisible translation tail be

\[
K_m=\{h\in\mathcal L_I:h(S)=0\text{ for }|S|\le m\}.
\tag{EST.13}
\]

Translation by `h` is `T_h(f)=f+h`.

### Theorem 4.1 -- exact associated-grade promotion

For `m<|I|`, restriction to the next support grade gives a canonically split exact sequence

\[
\boxed{
0\longrightarrow K_{m+1}\longrightarrow K_m
\xrightarrow{\rho_{m+1}}
A^{\{S\subseteq I:|S|=m+1\}}
\longrightarrow0.}
\tag{EST.14}
\]

Moreover:

1. `T_h` is invisible to `Q_m` exactly when `h in K_m`;
2. if `h in K_m\setminus K_(m+1)`, then `T_h` is legal before promotion and illegal after
   promotion;
3. the quotient `K_m/K_(m+1)` is exactly the newly operational `(m+1)`-support grade.

### Proof

The map `rho_(m+1)` restricts `h` to subsets of cardinality `m+1`.  Its kernel consists of elements
already zero in all grades at most `m` and now also zero in grade `m+1`; this is `K_(m+1)`.
Given any function on the `(m+1)`-subsets, extend it by zero on every other subset.  The result lies
in `K_m` and is a right inverse to `rho_(m+1)`, proving split exactness.

For every visible `S`,

\[
Q_m(T_hf)(S)=f(S)+h(S).
\]

This equals `Q_m(f)(S)` for all `f,S` exactly when `h` vanishes on all supports of size at most
`m`, proving item 1.  An element of `K_m\setminus K_(m+1)` has a nonzero coordinate on some
`(m+1)`-support, proving items 2 and 3.  QED.

## 5. Symmetry closes a witnessed support to a grade

The permutation group `Sym(I)` acts on supports and on reporters by reindexing.

### Theorem 5.1 -- orbit-forced grade promotion

Let a reporter doctrine be closed under `Sym(I)`.  If it contains evaluation at one support
`S subset I` of size `k`, it contains evaluation at every `k`-support.  Thus one witnessed
`k`-support promotes the whole grade, not a fitted coordinate.

### Proof

For any `T subset I` with `|T|=|S|`, choose a bijection `S->T` and a bijection between their
complements; combining them gives a permutation `pi:I->I` with `pi(S)=T`.  The translate of
evaluation at `S` by `pi` is evaluation at `T`.  Closure of the doctrine under the action includes
it.  QED.

Together, Theorems 2.1 and 4.1 say precisely what a symmetry-closed failure does:

\[
\boxed{
\text{witnessed support}
\longmapsto
\text{whole reporter grade}
\longmapsto
\text{strict contraction }K_m\supsetneq K_{m+1}.}
\tag{EST.15}
\]

This is semantic transport.  A failure changes the set of future interventions still counted as
law-preserving.

## 6. Failure loops and exact survivors

1. **Mixed support values automatically change future laws.** `[FALSIFIED]` Higher parity on a
   signed cube factors through singleton signs.  It produces no contraction once elementary signs
   are already observed.
2. **Every added reporter is operationally new.** `[FALSIFIED]` Theorem 2.1 and equation `(EST.5)` show exact
   inertness when the reporter is constant on old fibres.
3. **A nonzero cross-effect automatically constrains future operations.** `[FALSIFIED]` Attach the
   interaction as a spectator factor and let every future operation ignore it.
4. **Fixed finite reporter type supports open effective genesis.** `[FALSIFIED IN THIS MECHANISM
   CLASS]` Theorem 3.1 gives the sharp rank bound.
5. **One failed support selects one coordinate.** `[FALSIFIED BY EQUIVARIANCE]` Theorem 5.1 forces
   the full support orbit.
6. **Grade promotion is cofinal birth.** `[FALSIFIED]` Finite `I` terminates at `|I|`.  Unbounded
   genesis needs unbounded arity, growing history/carrier, or an admission/formation-class change.

The positive survivor is not another hidden object.  It is the operational mechanism `(EST.15)`.

## 7. Relation to the existing universal-law field

- ULF-EAG-2 supplies support orbits but not semantic novelty.  Theorem 2.1 is its hostile acceptance
  test.
- ULF-RMP-1 proves reporter refinement can remove strict promotions.  Theorem 2.1 now decides
  exactly when refinement removes any currently invisible intervention at all.
- ULF-IRR-1 supplies unbounded irreducible arities.  Theorem 4.1 turns arity layers into exact
  changes of legal intervention symmetry.
- ULF-GTM-1 and ULF-GTM-2 prove termination and the finitary cofinal-birth barrier.  Theorem 3.1
  supplies the sharp reporter-fibre resource consumed by each effective birth.

Consequently every proposed route-independent law genesis now faces a falsifiable question:

> Which old observation fibre does the born test split, and which explicit old-invisible
> intervention does it make illegal?

If neither can be exhibited, the alleged law birth is bookkeeping.

## 8. External parent boundary

All ingredients have classical parents.

- Partition endomorphism monoids: Araújo--Schneider,
  *The Rank of the Endomorphism Monoid of a Partition*, arXiv:0807.1214.
- Operation--relation Galois duality: Geiger and
  Bodnarchuk--Kalužnin--Kotov--Romov; modern functional variants include Polyakov,
  arXiv:1810.02945.
- Counterexample-generated predicates: CEGAR; a current general reactive-system realization is
  König--Rensink--Stoltenow--Urrigshardt, arXiv:2504.08617.
- Higher cross-effects and total fibres: Eilenberg--Mac Lane and Goodwillie calculus; current
  comparison work includes *The spectrum of excisive functors* (Invent. Math., 2025).

The claim is therefore not a new parent theorem in semigroup, clone, or functor calculus.  Its
field contribution is the exact synthesis of four operations usually studied separately:

\[
\text{failure witness}\to
\text{equivariant test birth}\to
\text{invisible-symmetry contraction}\to
\text{arity escape or termination}.
\]

## 9. Hostile correctness and significance verdict

- **Correctness:** every implication has an explicit finite/set-theoretic proof; no compactness,
  topology, source oracle, or RH premise is hidden.
- **Rediscovery:** Theorems 2.1 and 4.1 are elementary shadows of established partition and graded
  module theory.  Label the package `[BRIDGE]`, not a priority claim.
- **Significance:** unlike a classification of stored obstructions, the theorem predicts whether a
  proposed new test changes future legal mathematics and gives an explicit forbidden intervention.
- **Limitation:** it does not derive which failure witness a source produces.  It turns a sourced
  witness into a forced semantic update; source generation remains the next field gate.
- **All-route leverage:** bounded observers, finite apertures, fixed jets, finite recurrence
  windows, scalar positivity quotients, and finite relation lattices cannot support an unbounded
  effective reporter history without spending one of the escape resources in Corollary 3.2.
  This is a diagnostic theorem, not an RH proof.

## 10. Lean closure

Lean module
`GaloisForLFunctions.HTGeometry.ConstitutiveSemanticTransportArityPromotion` certifies:

1. arbitrary-set equivalence `(EST.3)` and explicit overwrite witness;
2. paired-reporter strictness criterion `(EST.5)`;
3. finite image-cardinality growth and bound `(EST.8)`, including sharpness;
4. finite support-grade restriction, kernel, zero-extension splitting, and detected translation;
5. permutation-orbit grade closure.

Direct elaboration, project lint, `UniversalLawField` umbrella build, and axiom audit all pass.
The declarations use no project axioms; `#print axioms` reports only Lean's standard `propext`,
`Classical.choice`, and `Quot.sound` where required.
