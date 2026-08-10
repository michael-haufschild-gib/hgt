# Iterated diagonal challenge genesis and filtered-limit escape law

- **ID:** ULF-DJG-1
- **Stage:** 1-in-progress
- **Type:** LIVE MECHANISM CONJECTURE / SOURCE-NORMAL GRAMMAR UPDATE
- **Statement:** Complementing a Boolean self-evaluator on its diagonal canonically generates an
  unrepresented challenge.  Adjoining that challenge as one new reporter is a relabelling-natural
  minimal grammar update.  Iteration from the empty evaluator yields the strict-order evaluator on
  finite ordinals, while the filtered limit acquires a new cofinal diagonal challenge and the
  update fails to commute with that limit.
- **Status:** [CONJECTURE] [MECHANISM NOT OBJECT] [ROUTE-INDEPENDENT]
  [LAWVERE/CANTOR PARENT] [FILTERED-LIMIT EXCHANGE UNDER ATTACK] [NOT RH] [NO LEAN]

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

### Conjecture A -- exact diagonal novelty

For no `a in X` does `E_a=delta_E`.

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

### Conjecture B -- source-normal minimal update

1. the old evaluator embeds as a full principal sub-evaluator of `E^+`;
2. the new row restricts to `delta_E` and is distinct from every transported old row;
3. every extension which retains every old row and represents `delta_E` requires an index outside
   the old carrier, so adjoining one point is cardinal-minimal;
4. conjugate evaluators have conjugate successors under the extended relabelling.

Item 4 is the presentation-stability gate.  The successor may not depend on names or a chosen failed
coordinate.

## 4. Iteration and explicit normal form

Start from the empty evaluator.  Repeated application of `(DJG.3)` gives a carrier of size `n` at
stage `n`.

### Conjecture C -- strict-order normal form

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

## 5. Filtered-limit escape

The coherent union has carrier `N` and evaluator

\[
  E_\omega(i,j)=1\quad\Longleftrightarrow\quad j<i.
  \tag{DJG.5}
\]

### Conjecture D -- cofinal incompleteness and nonexchange

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

This is the load-bearing claim.  It would give a source-generated formation-class transition which
escapes the finitary-saturation barrier without inserting an arbitrary nonfinitary closure.

## 6. Hostile attacks to run before proof work

### Attack 1 -- pure rediscovery

The anti-diagonal theorem is Lawvere/Cantor, and `(DJG.4)` is the strict order on finite ordinals.
If the whole card reduces to those names, it is only a bridge.

**Required survivor:** the exact coupling of minimal source-generated grammar update with
filtered-limit nonexchange and completion-born challenge.

### Attack 2 -- renamed free counter

The tower may merely append one symbol per step.

**Required survivor:** prove the appended row is uniquely forced on every old coordinate by the
previous evaluator, natural under relabelling, and minimal among conservative realizations.

### Attack 3 -- no true formation-class transition

Perhaps the limit defect is only a bad choice of colimit presentation.

**Required survivor:** use the isomorphism-invariant property “some row has infinite support” to
separate `E_omega` from its successor.

### Attack 4 -- fixed grammar in disguise

Perhaps the entire tower is definable from the original order relation and hence violates the
reflexive-grammar requirement.

**Required survivor:** distinguish meta-level definability of the completed tower from internal
representability of each stage's anti-diagonal.  If no operational difference survives, retire the
field interpretation.

### Attack 5 -- no cross-doctrine leverage

Even a correct diagonal tower may have no relevance beyond Boolean self-evaluation.

**Required survivor:** before any route use, extract predictions for observer contraction,
completion/admission exchange, and finite-versus-cofinal challenge effectivity.  Route analogies do
not count.

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

## 8. Promotion gate

Move to Stage 2 only after:

1. every clause A--D has a dependency-closed proof;
2. the colimit comparison is explicitly typed and its nonisomorphism invariant is proved;
3. the update's relabelling naturality and minimality are exact;
4. the free-counter and fixed-grammar attacks are answered without rhetoric; and
5. the theorem is scoped as a source-normal mechanism calibration, not an established universal
   field or RH result.

Only after Stage 2 may the exact theorem be formalized under
`GaloisForLFunctions.HTGeometry.ConstitutiveDiagonalLawGenesis`.

## Log

- 2026-08-10 -- opened after fixed-polarity, arbitrary-endogeneity, failure-kernel, operational-
  novelty, and finitary-saturation audits.  Live conjecture: diagonal complement supplies the
  missing source-normal grammar update and fails to commute with its own filtered limit.
