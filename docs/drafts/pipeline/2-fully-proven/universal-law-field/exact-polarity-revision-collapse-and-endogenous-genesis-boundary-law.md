# Exact polarity revision collapse and endogenous-genesis boundary law

- **ID:** ULF-RLM-12
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / MECHANISM BOUNDARY
- **Statement:** Exact reciprocal revision under a fixed rule--test polarity either stabilizes after
  one serial round or becomes period two after one synchronous round; open law genesis therefore
  requires the compatibility law, admission, resource horizon, or retained history itself to change.
- **Status:** [PROVED HERE] [DEPENDENCY-CLOSED] [LEAN-CERTIFIED] [MECHANISM NOT OBJECT]
  [FIXED-POLARITY NO-GENESIS] [POSITIVE DYNAMICS CLASSIFICATION] [NOT RH]

## 1. Founding question

Suppose legal rules and admissible tests determine one another exactly by preservation. Can repeated
mutual revision itself generate a prolonged hierarchy of new laws?

The answer is no. This card classifies the complete dynamics of exact reciprocal revision under one
fixed compatibility relation. The result is a boundary theorem for Reflexive Law Mechanics: a live
law-genesis mechanism must revise more than the two polar families.

## 2. Fixed polarity

Let `X` be a set of candidate rules, `Y` a set of candidate tests, and

\[
  x\perp y
\]

mean that rule `x` passes test `y`. For `A subset X` and `B subset Y`, define

\[
 A^\perp=\{y\in Y:(\forall x\in A)\ x\perp y\},
 \qquad
 {}^\perp B=\{x\in X:(\forall y\in B)\ x\perp y\}.
 \tag{PR.1}
\]

Write

\[
 c_X(A)={}^\perp(A^\perp),
 \qquad
 c_Y(B)=({}^\perp B)^\perp.
 \tag{PR.2}
\]

These are exact closures induced by the fixed rule--test compatibility law.

## 3. The polarity laws

### Theorem 3.1 -- antitonicity, extensivity, and triple-polar collapse

For all `A,A' subset X` and `B,B' subset Y`:

1. `A subset A'` implies `(A')^perp subset A^perp`, and `B subset B'` implies
   `^perp(B') subset ^perp B`;
2. `A subset c_X(A)` and `B subset c_Y(B)`;
3. `(c_X(A))^perp=A^perp` and `^perp(c_Y(B))=^perp B`;
4. `c_X(c_X(A))=c_X(A)` and `c_Y(c_Y(B))=c_Y(B)`.

#### Proof

Antitonicity is immediate from the universal quantifiers in (PR.1). If `x in A` and `y in
A^perp`, then `x perp y`; hence `x in ^perp(A^perp)`. This proves `A subset c_X(A)`. The proof on
`Y` is symmetric.

From `A subset c_X(A)`, antitonicity gives `(c_X(A))^perp subset A^perp`. Conversely, take
`y in A^perp`. Every `x in c_X(A)=^perp(A^perp)` passes every test in `A^perp`, hence passes `y`;
so `y in (c_X(A))^perp`. Thus equality holds. The other triple-polar identity is symmetric.
Applying the opposite polar to either triple-polar identity proves idempotence. QED.

## 4. Exact classification of reciprocal revision

Two natural update schedules exist.

### Serial revision

First replace the tests by all tests passed by the current rules; then replace the rules by all
rules passing those revised tests:

\[
 S(A,B)=\bigl(c_X(A),A^\perp\bigr).
 \tag{PR.3}
\]

The old `B` is irrelevant because serial exact revision recomputes the full test doctrine from `A`.

### Synchronous revision

Update both sides from the previous state:

\[
 P(A,B)=\bigl({}^\perp B,A^\perp\bigr).
 \tag{PR.4}
\]

### Theorem 4.1 -- serial collapse and synchronous two-cycle law

For every pair `(A,B)`:

\[
 S^2(A,B)=S(A,B),
 \qquad
 P^3(A,B)=P(A,B).
 \tag{PR.5}
\]

More explicitly,

\[
 P^2(A,B)=\bigl(c_X(A),c_Y(B)\bigr).
 \tag{PR.6}
\]

Therefore every serial history is fixed after one full round. Every synchronous history, after its
first step, is either fixed or alternates with exact period two. No fixed-polarity reciprocal
revision has an arbitrarily long transient, period greater than two, or open genesis history.

#### Proof

Using Theorem 3.1,

\[
 S^2(A,B)
 =S\bigl(c_X(A),A^\perp\bigr)
 =\bigl(c_X(c_X(A)),(c_X(A))^\perp\bigr)
 =\bigl(c_X(A),A^\perp\bigr).
\]

For the synchronous update,

\[
 P^2(A,B)
 =P\bigl({}^\perp B,A^\perp\bigr)
 =\bigl({}^\perp(A^\perp),({}^\perp B)^\perp\bigr)
 =\bigl(c_X(A),c_Y(B)\bigr).
\]

One further update and the triple-polar identities give

\[
 P^3(A,B)
 =\bigl({}^\perp(c_Y(B)),(c_X(A))^\perp\bigr)
 =\bigl({}^\perp B,A^\perp\bigr)
 =P(A,B).
\]

The orbit classification follows. QED.

### Corollary 4.2 -- exact fixed-point criterion

A synchronous state `(A,B)` is fixed exactly when

\[
 A={}^\perp B,
 \qquad
 B=A^\perp.
 \tag{PR.7}
\]

Such a state is precisely a closed rule--test concept. A post-first-step synchronous state has
period exactly two iff it is not fixed.

#### Proof

Equation `P(A,B)=(A,B)` is componentwise exactly (PR.7). The second assertion follows from
`P^3=P`: after one step, applying `P` twice returns to the same state. QED.

## 5. No-go closure and positive survivor

### Killed conjecture

> Repeated exact Pol--Inv feedback under one fixed preservation relation can itself produce an open
> hierarchy of new laws.

This is false by Theorem 4.1. Exact serial feedback is idempotent; exact synchronous feedback is
eventually period two.

### Strongest positive survivor

The complete fixed-polarity dynamics is classified. Hence every prolonged law-genesis mechanism
must violate at least one fixed-polarity hypothesis in a typed way:

1. **endogenous testing:** executing or repairing rules creates new test kinds, changing `perp`;
2. **endogenous legality:** admission changes which rule--test pairs are meaningful;
3. **resource filtration:** only bounded-arity or bounded-cost polars are available at each stage;
4. **nonexact exchange:** revision transports only part of one polar family;
5. **retained lineage:** extension or history data survive after endpoint polar closure.

These are not five extra coordinates. They are five mechanisms by which the compatibility law used
at the next revision differs from the one used at the previous revision.

## 6. Consequences for the new field

1. **Rule/test coevolution is insufficient unless compatibility coevolves.** Merely alternating
   `Pol` and `Inv` cannot be the missing theory.
2. **Period two is a diagnostic.** A purportedly reflexive exact-duality model with longer exact
   recurrence has silently changed its tests, admission, or transport.
3. **Open history locates the missing law.** If finite observers stabilize while law history stays
   open, the cause cannot be a fixed exact polarity; it must lie in a changing horizon or
   compatibility rule.
4. **Next research variable is a transition law for compatibility.** The field should classify
   which failures change future falsifiers, not search for a larger static closure object.

## 7. Parent mathematics and scope

The proof uses classical polarity/Galois-connection identities. Fixed-arity restriction and
closure decomposition are studied, for example, in Couceiro,
*On Galois Connections between External Operations and Relational Constraints* (2015),
<https://arxiv.org/abs/1508.01568>. Orthogonality fixpoints are broad existing machinery, including
Fiore--Galal--Jafarrahmani, *Fixpoint constructions in focused orthogonality models of linear
logic* (2023), <https://arxiv.org/abs/2309.10084>.

The field contribution claimed here is the mechanism boundary and its research consequence, not
priority for Galois closure theory. No proof route, arithmetic endpoint, positivity assumption,
topology, or RH statement enters the theorem.

## 8. Lean certification

The exact set-polarity definitions, triple-polar laws, `S^2=S`, `P^2=(c_X,c_Y)`, `P^3=P`, and the
fixed-point criterion are certified in
`GaloisForLFunctions.HTGeometry.ConstitutivePolarityRevision`. The module is imported by
`GaloisForLFunctions.HTGeometry.UniversalLawField`; its direct elaboration and umbrella build pass.
The axiom audit reports only Lean's standard `propext` and quotient soundness foundations.

## Log

- 2026-08-09 -- fixed-polarity reciprocal dynamics classified on paper; naive self-modifying
  Pol--Inv genesis killed; endogenous compatibility change isolated as positive survivor.
