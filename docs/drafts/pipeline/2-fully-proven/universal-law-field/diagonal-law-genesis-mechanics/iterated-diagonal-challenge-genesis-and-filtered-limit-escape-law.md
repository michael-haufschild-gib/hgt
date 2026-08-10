# Iterated diagonal challenge genesis and filtered-limit escape law

- **ID:** ULF-DJG-1
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / SOURCE-NORMAL GRAMMAR UPDATE
- **Statement:** Complementing a Boolean self-evaluator on its diagonal canonically generates an
  unrepresented challenge.  Adjoining that challenge as one new reporter is a relabelling-natural
  minimal grammar update.  Iteration from the empty evaluator yields the strict-order evaluator on
  finite ordinals, while the filtered limit acquires a new cofinal diagonal challenge and the
  update fails to commute with that limit.
- **Status:** [PAPER-PROVED] [DEPENDENCY-CLOSED] [MECHANISM NOT OBJECT] [ROUTE-INDEPENDENT]
  [LAWVERE/CANTOR PARENT] [MINIMAL DIAGONAL SUCCESSOR]
  [FILTERED-COLIMIT NONEXCHANGE] [LEAN-PROVED] [AXIOM-AUDITED] [NOT RH]

## 1. Frontier forcing

The corpus already closes four easier mechanisms:

1. fixed reciprocal compatibility collapses after one round or becomes period two;
2. arbitrary state-dependent compatibility realizes every transition graph and predicts nothing;
3. a failed consequence generates its minimal proof kernels and exact transversal repairs;
4. a supplied new reporter is effective exactly when it splits an old operational fibre.

What remains missing is the production law

\[
  \text{current legal doctrine}
  \longmapsto
  \text{a new challenge not representable in that doctrine}.
  \tag{DJG.1}
\]

Generic cell attachment, free-signature growth, and an arbitrary counterexample oracle fail the
source-normality gate.  The proposed replacement uses self-evaluation itself to manufacture the
next challenge.

## 2. Boolean self-evaluators and anti-diagonal birth

A Boolean self-evaluator is a set `X` with

\[
  E:X\times X\longrightarrow\{0,1\}.
\]

Its row at `x` is `E_x(y)=E(x,y)`.  Define the anti-diagonal challenge

\[
  \delta_E(x)=1-E(x,x).
  \tag{DJG.2}
\]

### Theorem 2.1 -- exact diagonal novelty

For no `a in X` does `E_a=delta_E`.

#### Proof

If `E_a=delta_E`, evaluation at `a` gives

\[
 E(a,a)=\delta_E(a)=1-E(a,a),
\]

which is impossible for a Boolean value. QED.

This is the set-level Lawvere--Cantor diagonal argument and is expected to be
`[REDISCOVERED]`.  It is not the field claim.  Its role is to produce a witness without inspecting
an external target.

## 3. Canonical one-step grammar update

Put `X^+=X disjoint-union {star}` and define `E^+` by

\[
\begin{aligned}
 E^+(x,y)&=E(x,y), &&x,y\in X,\\
 E^+(\star,y)&=\delta_E(y), &&y\in X,\\
 E^+(x,\star)&=0, &&x\in X^+.
\end{aligned}
\tag{DJG.3}
\]

Thus old evaluations transport unchanged; the new row restricts to the exact challenge that the old
doctrine could not represent; and the new column is initialized by the distinguished Boolean zero.

An **extension** of `E` is an evaluator `F:Y times Y -> {0,1}` together with an injection
`j:X->Y` satisfying

\[
 F(jx,jy)=E(x,y)\qquad(x,y\in X).
 \tag{DJG.3a}
\]

It **realizes the old anti-diagonal** when some `a in Y` satisfies

\[
 F(a,jy)=\delta_E(y)\qquad(y\in X).
 \tag{DJG.3b}
\]

### Theorem 3.1 -- source-normal minimal update

1. the old evaluator embeds as a full principal sub-evaluator of `E^+`;
2. the new row restricts to `delta_E` and is distinct from every transported old row;
3. every extension which retains every old row and represents `delta_E` requires an index outside
   the old carrier, so adjoining one point is cardinal-minimal;
4. conjugate evaluators have conjugate successors under the extended relabelling.

#### Proof

The inclusion `j(x)=inl(x)` is injective, and the first line of `(DJG.3)` is exactly
`(DJG.3a)`.  The new row is `(DJG.2)` on the old carrier by the second line.  If its restriction
equalled the transported row of some `x`, then `E_x=delta_E`, contradicting Theorem 2.1.

Now let `(Y,F,j)` be any extension realizing the anti-diagonal at `a`.  If `a=j(x)`, then for every
`y`

\[
 \delta_E(y)=F(a,jy)=F(jx,jy)=E(x,y),
\]

again contradicting Theorem 2.1.  Hence `a` lies outside `j(X)`.  Every conservative realization
therefore needs at least one new index, while `(DJG.3)` uses exactly one.

Finally, suppose `phi:X->Y` is a bijection and

\[
 F(\phi x,\phi y)=E(x,y).
 \tag{DJG.3c}
\]

Extend it by `phi^+(inl x)=inl(phi x)` and `phi^+(star)=star`.  This is a bijection.  On old--old
pairs, preservation is `(DJG.3c)`.  On new--old pairs it follows from
`F(phi y,phi y)=E(y,y)` and Boolean complementation.  Every pair in the new column has value zero
on both sides.  Thus `phi^+` conjugates the successors. QED.

Item 4 is the presentation-stability gate.  The successor may not depend on names or a chosen failed
coordinate.

## 4. Iteration and explicit normal form

Start from the empty evaluator.  Repeated application of `(DJG.3)` gives a carrier of size `n` at
stage `n`.

### Theorem 4.1 -- strict-order normal form

After the canonical identification with `Fin n`,

\[
  E_n(i,j)=1\quad\Longleftrightarrow\quad j<i.
  \tag{DJG.4}
\]

Consequently:

1. the stage-`n` anti-diagonal is the all-true function on `Fin n`;
2. it is realized exactly as the restriction of the new row born at stage `n+1`;
3. every step is effective and consumes exactly one new reporter index;
4. no finite stage is closed under its own diagonal challenge.

This is not an arbitrary counter.  The next row is forced coefficient-by-coefficient by the current
self-evaluator.

#### Proof

Use induction on `n`.  The empty evaluator is the strict order on `Fin 0`.  Identify
`Fin n disjoint-union {star}` with `Fin(n+1)` by sending old `i` to `i` and `star` to `n`.

For old `i,j`, the induction hypothesis and the first line of `(DJG.3)` give
`E_(n+1)(i,j)=1` exactly when `j<i`.  For the new row and old column `j`, the second line gives

\[
 E_{n+1}(n,j)=1-E_n(j,j)=1,
\]

and indeed `j<n`.  The whole new column is zero, matching the fact that `n<i` fails for every
`i≤n`.  This proves `(DJG.4)`.

Every diagonal value is zero, so the anti-diagonal is all true.  The new row has that restriction
by construction.  Theorem 2.1 makes the step strict, and Theorem 3.1 makes the one-index cost
minimal. QED.

## 5. Filtered-limit escape

The coherent union has carrier `N` and evaluator

\[
  E_\omega(i,j)=1\quad\Longleftrightarrow\quad j<i.
  \tag{DJG.5}
\]

### The category used for the exchange statement

Let `BoolEvalEmb` have Boolean evaluators as objects.  A morphism

\[
 f:(X,E)\longrightarrow(Y,F)
\]

is an injection satisfying

\[
 F(fx,fy)=E(x,y)\qquad(x,y\in X).
 \tag{DJG.5a}
\]

Composition and identities are inherited from functions.  The successor construction acts on a
morphism by `S(f)=f disjoint-union id_{star}`.  The case analysis in Theorem 3.1 proves that this is
a functor.

### Theorem 5.1 -- cofinal incompleteness and filtered-colimit nonexchange

1. every row of `E_omega` has finite true support;
2. the anti-diagonal `delta_(E_omega)` is the constant-true function and is not a row;
3. on every finite column set, some row agrees with that constant-true challenge;
4. therefore the challenge is in the finite-cylinder/product closure of the row image but outside
   the image;
5. the colimit of the finite successors is again `E_omega`, whereas the successor of `E_omega`
   has a new row with infinite true support; hence diagonal succession does not commute with this
   filtered colimit, even up to evaluator isomorphism.

The expected exact exchange defect is

\[
  \operatorname*{colim}_n S(E_n)=E_\omega
  \quad\not\cong\quad
  S\!\left(\operatorname*{colim}_nE_n\right)=E_{\omega+1}.
  \tag{DJG.6}
\]

This is the load-bearing claim.  It gives a source-generated formation-class transition which
escapes the finitary-saturation barrier without inserting an arbitrary nonfinitary closure.

#### Proof

For row `i`, the true support is `{0,...,i-1}`, hence finite.  Since
`E_omega(i,i)=0`, the anti-diagonal is constant true.  It cannot equal row `i`, already at column
`i`.

Let `K subset N` be finite.  If it is empty choose row `0`.  Otherwise choose
`i>max K`.  Then every `j in K` satisfies `j<i`, so row `i` agrees with the constant-true function
on `K`.  Basic product cylinders constrain only finitely many coordinates; therefore every basic
neighbourhood of the constant-true function contains a row, proving closure.  Nonmembership was
proved above.

The inclusions `Fin n -> Fin(n+1)` are morphisms by `(DJG.4)`.  Their union is `N`, and the union
relation is `(DJG.5)`.  This union has the colimit universal property in `BoolEvalEmb`: for every
compatible cocone `f_n:Fin n->Y`, define `f(i)=f_(i+1)(i)`.  Compatibility makes this independent
of stage, injectivity follows inside a common later stage, and `(DJG.5a)` follows by placing any
pair in a common finite stage.  Uniqueness follows because every natural number occurs at a finite
stage.  Hence the colimit is `E_omega`.

The successor chain is the shifted chain `(E_(n+1))_n`, whose union and colimit are again
`E_omega`.  By contrast, `S(E_omega)` contains the new row `star`, whose true support on the old
carrier is all of `N`, hence infinite.

An evaluator isomorphism preserves row supports up to bijection: if `phi` conjugates `E` and `F`,
then

\[
 \{\phi y:F(\phi x,\phi y)=1\}
 =\phi\bigl(\{y:E(x,y)=1\}\bigr).
\]

Therefore finiteness of every row support is isomorphism-invariant.  Every row of `E_omega` has
finite support, while `S(E_omega)` has an infinite-support row.  They are not isomorphic.  Thus `S`
does not preserve this filtered colimit. QED.

## 6. Completed hostile attacks

### Attack 1 -- pure rediscovery

The anti-diagonal theorem is Lawvere/Cantor, and `(DJG.4)` is the strict order on finite ordinals.
If the whole card reduces to those names, it is only a bridge.

**Verdict:** the diagonal lemma is `[REDISCOVERED]`; strict finite-order rows are elementary.

**Survivor:** the exact coupling of minimal source-generated grammar update with filtered-limit
nonexchange and completion-born challenge is not used as a novelty claim, but it is new corpus
leverage and passes dependency closure.

### Attack 2 -- renamed free counter

The tower may merely append one symbol per step.

**Verdict:** passed.  The appended row is uniquely forced on every old coordinate by the previous
evaluator, natural under relabelling, and minimal among conservative realizations.  Only the value
on the genuinely new coordinate is a convention; fixing Boolean zero makes the update strict and
functorial.

### Attack 3 -- no true formation-class transition

Perhaps the limit defect is only a bad choice of colimit presentation.

**Verdict:** passed.  The isomorphism-invariant property “some row has infinite support” separates
`E_omega` from its successor.

### Attack 4 -- fixed grammar in disguise

Perhaps the entire tower is definable from the original order relation and hence violates the
reflexive-grammar requirement.

**Verdict:** passed in the exact stated sense.  Meta-level definability does not provide an internal
row: at every finite stage and at the filtered limit the anti-diagonal is absent.  The successor
changes the carrier and realizes that previously unavailable challenge.  No stronger claim about
logical undefinability is made.

### Attack 5 -- no cross-doctrine leverage

Even a correct diagonal tower may have no relevance beyond Boolean self-evaluation.

**Verdict:** passed as a mechanism calibration, not as universal-field acceptance:

1. finite-coordinate observers report realization of the all-true challenge at a sufficiently
   late row;
2. the full observer proves nonrealization;
3. successor and filtered completion fail exact exchange;
4. every finite repair is effective while no finite stage or the colimit is internally complete.

These are exact predictions in three doctrines--observation, completion, and grammar formation.
Cross-route realization remains open.

### Overall hostile verdict

`[BRIDGE] [PAPER-PROVED]`.  The package is not a new diagonal theorem.  Its significant field role
is that it supplies the source-normal update missing from ULF-PCG-2 and a concrete nonfinitary exit
from ULF-GTM-2.  It does not establish the Universal Law Field by itself.

## 7. Internal and external parent boundary

### Internal corpus

- ULF-RLM-12: fixed-polarity revision collapse;
- ULF-ECM-1: arbitrary endogenous compatibility universality no-go;
- ULF-FKT-1: failure kernels generate transversal repair tests;
- ULF-EST-1: operational novelty and finite genesis bound;
- ULF-PCG-1/2: completion-born signatures and quotient-descent grammar birth;
- ULF-GTM-2: finitary formation saturation cannot create a cofinal law.

The new claim must connect these boundaries rather than restate any one of them.

### External parents

- F. W. Lawvere, *Diagonal arguments and cartesian closed categories* (1969; TAC reprint 2006),
  <https://www.tac.mta.ca/tac/reprints/articles/15/tr15.pdf>;
- N. Yanofsky, *A Universal Approach to Self-Referential Paradoxes, Incompleteness and Fixed
  Points* (2003), <https://arxiv.org/abs/math/0305282>;
- A. Karimi and S. Salehi, *Diagonalizing by Fixed-Points* (2013),
  <https://arxiv.org/abs/1303.0730>;
- finitary monads/filtered-colimit parents already audited under ULF-GTM-2.

Current searches found the diagonal and filtered-colimit ingredients separately, not the exact
iterated conservative-successor/nonexchange package.  No novelty claim is made before a broader
hostile audit.

## 8. Paper-proof closure and Lean target

The Stage-2 gate is closed:

1. every clause A--D has a dependency-closed proof;
2. the colimit comparison is explicitly typed and its nonisomorphism invariant is proved;
3. the update's relabelling naturality and minimality are exact;
4. the free-counter and fixed-grammar attacks are answered without rhetoric; and
5. the theorem is scoped as a source-normal mechanism calibration, not an established universal
   field or RH result.

The exact theorem is formalized under
`GaloisForLFunctions.HTGeometry.ConstitutiveDiagonalLawGenesis`.

Required Lean surface:

1. generic anti-diagonal novelty;
2. conservative successor realization, strictness, and relabelling naturality;
3. finite strict-order normal form;
4. finite approximation and global nonrealization of the constant-true row;
5. finite support of every limit row and infinite support of the successor row; and
6. one unconditional capstone containing the finite/cofinal exchange failure.

Direct foreground elaboration is warning-free.  The leaf build passes with 2,997 jobs.  Axiom
prints on diagonal novelty, the finite/cofinal capstone, and the no-isomorphism theorem report only
Lean/mathlib foundations `propext`, `Classical.choice`, and `Quot.sound`; no project axiom or
unproved premise occurs.  The module is wired into `HTGeometry.UniversalLawField`.

## Log

- 2026-08-10 -- opened after fixed-polarity, arbitrary-endogeneity, failure-kernel, operational-
  novelty, and finitary-saturation audits.  Live conjecture: diagonal complement supplies the
  missing source-normal grammar update and fails to commute with its own filtered limit.
- 2026-08-10 -- clauses A--D proved.  Exact category `BoolEvalEmb`, successor functor, finite-chain
  colimit, support invariant, and nonexchange closed.  Hostile verdict: known diagonal ingredients,
  dependency-closed new corpus coupling.  Promoted to Stage 2; no Lean written yet.
- 2026-08-10 -- Lean-certified generic anti-diagonal novelty, minimal conservative extension,
  successor naturality, finite strict-order normal form, finite-cylinder approximation, global
  nonrealization, support jump, and finite/cofinal nonexchange capstone.  Wired into the dedicated
  Universal Law Field umbrella.
