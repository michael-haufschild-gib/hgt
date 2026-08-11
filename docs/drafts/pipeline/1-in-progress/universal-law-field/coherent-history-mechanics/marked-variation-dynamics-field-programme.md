# Marked Variation Dynamics — field programme

- **ID:** ULF-MVD-0
- **Stage:** 1-in-progress
- **Type:** NEW-FIELD PROGRAMME / COFINAL EXTENSION OF COHERENT HISTORY MECHANICS
- **Status:** [ACTIVE] [MECHANISM NOT ROUTE] [FROZEN FIELD CONJECTURE]
  [FINITE FUSION CORE LEAN-FORMALIZED] [UNIVERSAL REALIZATION OPEN] [NOT RH]

## 1. Public sentence

A law is not determined by its answer.  It carries a marked family of ways that the answer was
generated, a coherent execution that may cancel those ways, and a positive execution that retains
their variation.  Observation loses variation in exact conserved installments; refinement creates
new variation in exact conserved installments.

## 2. Ontological reversal

Coherent History Mechanics established the finite double execution

\[
  \text{marked histories}
  \longmapsto
  \bigl(\text{coherent sum},\ \text{positive envelope}\bigr).
\]

Marked Variation Dynamics (MVD) takes the **defect between these executions** as a transported
quantity rather than a scalar diagnostic.  It is neither curvature nor one obstruction class.  It
is a positive current obeying two different exact laws:

1. a **fusion/refinement law** when new marked histories are generated;
2. an **observer chain rule** when histories are forgotten or completed.

These operations have opposite meanings.  Generation may enlarge the retained envelope while
leaving the coherent endpoint fixed.  Positive observation can only transport existing defect and
add new phase loss.  It cannot recover variation discarded by an earlier observer.

## 3. Primitive grammar

One chart consists of:

1. a finite or admitted locally finite packet of source-marked complex histories;
2. coherent addition of their amplitudes;
3. a positive envelope obtained before coherent cancellation;
4. positive observer kernels acting on both executions;
5. refinements replacing one marked history by several histories with the same coherent sum;
6. a cofinal observer/refinement history.

For a positive kernel `T` and packet `a=(a_i)`, define

\[
 C_T(a)=T\!\left(\sum_i a_i\right),\qquad
 E_T(a)=T\!\left(\sum_i|a_i|\right),\qquad
 \mathfrak D_T(a)=E_T(a)-|C_T(a)|.
 \tag{MVD.1}
\]

The finite theorem proves `D_T(a)>=0`, reconstructs `E_T` from `(C_T,D_T)`, and gives the two
exact laws.  No RH route appears in the definition.

## 4. Frozen conjecture — constitutive marked-variation realization

There is a source-normal class of marked-history processes containing literal realizations of the
five frontier mechanisms such that:

1. singular descent is an observer-chain defect;
2. oscillatory all-prime transport is coherent cancellation inside the genuine-history sector;
3. adaptive orientation is the relative phase between independently generated sectors;
4. whole-space coercivity is boundedness/tightness of the cofinal positive envelope;
5. positive carrier existence is convergence of the normalized envelope with vanishing
   observer-manufactured history mass;
6. the source process is fixed before divisor specialization and its observer chain is
   coefficient-faithful before the first non-phase-sufficient step.

The conjecture is not that every mathematical law is a positive kernel.  That stronger statement
is false and is recorded in the failed lane.  The open claim is that the literal arithmetic source
has one marked-current realization rich enough to carry all five mechanisms without fitting their
RH endpoints.

## 5. Exact finite laws already available

The paper theorem `ULF-MVD-1` proves:

1. **reconstruction**
   \[
     E_T(a)=|C_T(a)|+\mathfrak D_T(a);
   \]
2. **fusion** for disjoint packets `a,b`
   \[
   \mathfrak D_T(a\sqcup b)
   =\mathfrak D_T(a)+\mathfrak D_T(b)
    +|C_T(a)|+|C_T(b)|-|C_T(a)+C_T(b)|;
   \]
3. **observer chain rule**
   \[
   \mathfrak D_{ST}(a)
   =S\mathfrak D_T(a)+S|C_T(a)|-|SC_T(a)|;
   \]
4. **generation-observation interchange**
   \[
   \mathfrak D_{ST}(b)
   =S\mathfrak D_T(a)+STH_r(b)+\delta_S(C_T(a));
   \]
5. **refinement monotonicity with exact increment**;
6. **serial telescoping** of every observer loss as a transported positive summand, with a finite
   budget for every fixed macroscopic loss threshold;
7. **recurrence rigidity:** total-variation recurrence through mass-preserving positive observers
   forces every observer-loss increment to vanish;
8. **source/splice fusion:** stagewise coarse execution splits exactly into genuine source histories
   and observer-manufactured splice histories;
9. **carrier distance:** normalized splice mass is exactly the total-variation distance from the
   stagewise positive carrier to the nearest genuine-history-supported carrier.

## 6. Five frontier shadows — theorem versus conjecture

| frontier class | exact MVD coordinate | current realization status |
|---|---|---|
| singular source descent | serial observer defect `delta_S(C_T)` | abstract theorem; literal shared-source map open |
| all-prime oscillatory transport | within-genuine marked defect | finite/current charts exist; cofinal arithmetic estimate open |
| adaptive spectral orientation | between-sector interference term | exact coordinate; source-selected phase map open |
| whole-space coercivity | bounded cofinal envelope and recurrence rigidity | exact abstract obstruction; Route-O map open |
| positive carrier existence | normalized envelope and splice-mass distance | exact finite criterion; P/Q tight source carrier open |

This table is falsifiable.  A route that has no source-normal marked packet or positive observer is
not an MVD chart.  It may require a nonlinear, relational, derived, or higher-arity successor.

## 7. Hostile conjecture loops

### Loop A — every route is a positive-kernel process

`[FALSIFIED]`.  The native nonlinear law `x -> x^2` on `R` is not linear on its native carrier:
any linear map taking `1` to `1` takes `2` to `2`, not `4`.  Koopman or feature lifts can linearize
it only by adding a representation that is not source-canonical.  Adaptive null flags and
multivalued relations present the same typing obstruction.

**Positive survivor:** MVD is mandatory only after a literal source chart supplies marked additive
histories and positive observers.  It becomes an anti-theatre gate, not a universal encoding.

### Loop B — zero variation defect means faithful observation

`[FALSIFIED]`.  A positive observer may identify several same-phase histories and preserve modulus
exactly.  It can lose source labels while `D=0`.

**Positive survivor:** zero defect means phase sufficiency along the tested current, not observer
injectivity or source faithfulness.

### Loop C — the defect is curvature or cohomology

`[FALSIFIED]`.  The serial law is an exact transported cocycle identity obtained by inserting and
subtracting `S|C_T|`.  No nontrivial cohomology follows.

**Positive survivor:** nonnegative summands cannot cancel each other under later positive
observation.  This is an irreversible accounting law.

### Loop D — coherent output plus defect reconstructs source history

`[FALSIFIED]`.  It reconstructs the pushed positive envelope, not individual source amplitudes or
marks.  Phase-Gram data and a separating intervention coframe remain necessary for source
tomography.

**Positive survivor:** `(coherent output, defect)` is the minimal exact double needed to retain both
observed law and its positive execution budget at one observer scale.

### Loop E — recurrent observation always forces closed history

`[FALSIFIED]`.  Initial marked interference and later source refinements may remain open.  The
theorem excludes only newly accumulated loss along a mass-preserving positive observer chain.

**Positive survivor:** recurrent-shadow/open-history examples require a genuine generation or
refinement step; observation alone cannot create their growing variation ledger.

## 8. External parent boundary

Parents supply the ingredients:

- Banach lattices and positive operators supply `|Tx| <= T|x|` and lattice-homomorphism equality;
- Markov-chain lumpability studies when a projected process remains Markov and how realizable
  preimage histories grow ([Geiger--Temmel](https://arxiv.org/abs/1212.4375));
- weighted rewriting and semiring provenance retain derivation histories
  ([Ahrens--Kassing--Giesl--Katoen](https://arxiv.org/abs/2505.08496));
- Markov categories organize positive observer composition
  ([Fritz](https://arxiv.org/abs/1908.07021));
- decoherent-history and extended-probability formalisms separate fine histories from positive
  coarse shadows ([Gell-Mann--Hartle](https://arxiv.org/abs/1106.0767)).

The finite algebra is elementary and no priority claim is made for its ingredients.  The field
burden is the bivariant interpretation, the source-normal arithmetic realization, and the
prediction that source-faithful carrier formation is equivalent to vanishing cofinal splice
density rather than compactness alone.

## 9. Fourth-organ prediction

For every finite aperture, stagewise observed composition produces genuine and splice history
weights.  The theorem proves

\[
 \inf_{\nu\text{ supported on genuine histories}}
 d_{TV}(\pi_{stage},\nu)
 =\pi_{stage}(\text{splice histories}).
 \tag{MVD.2}
\]

Therefore a cofinal positive carrier obtained after stagewise observation is source-faithful in
total variation **iff** its normalized splice mass tends to zero.  Tightness, moment determinacy,
or weak compactness alone cannot replace this condition.  This is the withheld prediction for the
positive-carrier organ.

## 10. RH selection gate

MVD does not prove RH.  It strengthens the required source-normal envelope theorem:

1. construct the arithmetic marked packet before Xi specialization;
2. prove that every comparison used before the physical two-head landing is phase-sufficient on
   that packet, or retain its exact defect current;
3. prove cofinal splice density zero, so the positive carrier is source-supported rather than an
   observer artefact;
4. prove genuine-history envelope contractivity on the two-head receiver.

Then no transported positive defect can cancel a strict off-critical amplification.  The existing
right-half amplification theorem would contradict item 4 and yield RH by reflection.  Each item is
independent of the RH endpoint and has an explicit defect witness when it fails.

The finite exclusion step is now Lean-certified as
`markedRealization_strictAmplification_impossible`.  What remains open is not the inequality: it is
the source-faithful arithmetic realization supplying its hypotheses before specialization.

## 11. Acceptance gate

MVD becomes an accepted source field only after:

1. one pre-zero marked process realizes at least three structurally different route organs;
2. its serial defect current is coefficient-faithful;
3. the carrier-distance prediction is proved in a fourth literal organ;
4. cofinal completion is handled without replacing finite variation by a fitted renormalization;
5. every significant dependency-closed theorem is formalized in Lean.

The finite theorem closes the universal algebra, not these arithmetic gates.
