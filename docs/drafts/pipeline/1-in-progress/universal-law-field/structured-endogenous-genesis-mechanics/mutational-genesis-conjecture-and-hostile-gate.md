# Mutational genesis conjecture and hostile gate

- **ID:** ULF-SEGM-1
- **Stage:** 1-in-progress
- **Type:** MECHANISM CONJECTURE / MINIMAL BIFURCATION LABORATORY
- **Question:** What restricted law of compatibility change lies strictly between fixed-polarity
  collapse and arbitrary state-indexed vacuity?
- **Status:** [MECHANISM NOT OBJECT] [CLUSTER-MUTATION CALIBRATION]
  [CALIBRATION CLOSED] [NEXT CLASSIFICATION OPEN] [LEAN-CERTIFIED] [NO RH]

## 1. Higher pivot

The live problem is not to find a larger static law object. It is to find a predictive transition
law for changing the rulebook itself.

Two Lean-certified boundaries already force this question:

1. fixed exact rule--test polarity stabilizes after one serial round or becomes period two after
   one synchronous round;
2. arbitrary state-indexed compatibility realizes every transition system and is therefore
   non-predictive.

The missing mechanism must produce open law history from local typed data while forbidding an
arbitrary update oracle.

## 2. Candidate mechanism: mutation with conserved semantic exchange

Use a rank-two seed with two layers.

### Visible compatibility layer

The exchange orientation alternates

\[
  B_{n+1}=-B_n,
  \qquad B_{n+2}=B_n.
  \tag{MG.1}
\]

Thus every observer retaining only the current compatibility matrix sees exact period two.

### Semantic lineage layer

Starting from \(x_0=x_1=1\), require the local exchange law

\[
  x_{n+2}x_n=x_{n+1}^2+1.
  \tag{MG.2}
\]

The next law value is forced from the previous two; no state-indexed transition table is supplied.
Positivity makes every division in the equivalent mutation formula

\[
  x_{n+2}=\frac{x_{n+1}^2+1}{x_n}
  \tag{MG.3}
\]

admitted.

## 3. Bold conjecture

**Mutational genesis law.** A locally generated compatibility mutation can have a recurrent finite
rulebook while its semantic lineage is open. The open lineage is predictive rather than arbitrary
exactly when a transported invariant converts the nonlinear exchange into a closed recurrence.

For the smallest affine rank-two laboratory, the predicted invariant and recurrence are

\[
  \frac{x_n^2+x_{n+1}^2+1}{x_nx_{n+1}}=3,
  \qquad
  x_{n+2}=3x_{n+1}-x_n.
  \tag{MG.4}
\]

Consequently the visible rulebook is periodic while the positive lineage is strictly increasing
and unbounded.

The proposed field mechanism is not "cluster algebras explain the corpus." Cluster mutation is a
hostile minimal laboratory for a more general law:

> a legal local replacement may recur on compatibility data while conserved exchange transports
> enough lineage to force indefinitely new semantic laws.

## 4. Dependency-closed paper target

For positive triples \((a,b,c)\) obeying

\[
  ac=b^2+1,
  \tag{MG.5}
\]

define

\[
  H(a,b)=\frac{a^2+b^2+1}{ab}.
  \tag{MG.6}
\]

The target theorem has six clauses.

1. **Invariant transport:** \(H(a,b)=H(b,c)=(a+c)/b\).
2. **Forced linearization:** initial value \(H(1,1)=3\) makes every later mutation satisfy
   \(c=3b-a\).
3. **Exchange reconstruction:** the linear recurrence with initial pair \((1,1)\) preserves
   \(x_{n+2}x_n-x_{n+1}^2=1\), so it reconstructs the nonlinear mutation exactly.
4. **Positive openness:** after the first step, \(0<x_n<x_{n+1}\); hence the lineage never becomes
   periodic and is unbounded.
5. **Observed recurrence:** the compatibility sign has exact period two.
6. **Withheld prediction:** the nonlinear local rule predicts one constant-coefficient linear
   recurrence and all later values from the first two, without fitting a future transition table.

## 5. Hostile attacks

### Attack A -- this is arbitrary endogeneity in disguise

No. The update is fixed by one exchange polynomial and two initial values. Later states are outputs,
not coefficients in a state-indexed compatibility relation. The conserved quantity supplies a
falsifiable withheld prediction.

**Falsifier:** two histories satisfying the same sourced exchange and initial data but disagreeing
later. Equation (MG.3) forbids this on the positive domain.

### Attack B -- open lineage is merely an appended counter

The lineage coordinate is not incremented by definition. It is the response forced by (MG.2), and
its nonlinear dynamics is constrained by the independently derived invariant (MG.4).

**Remaining risk:** growth index \(n\) is still external. This laboratory does not yet construct
source time or a universal cost.

### Attack C -- periodic compatibility means no genuine law change

False in this laboratory. Compatibility matrix and semantic seed are different typed layers. The
first recurs; the second changes and controls every future legal mutation. Forgetting the seed is a
lossy observer, not a full state equivalence.

### Attack D -- positivity itself creates the selection

Positivity only guarantees admission of division and preserves the positive chamber. The exchange
polynomial and invariant create the predictive lineage. A positive endpoint without exchange does
not determine it.

### Attack E -- this is already cluster algebra theory

The recurrence, Laurent positivity, affine rank-two classification, frieze linearization, and
mutation invariants are established mathematics. No priority claim is made for these ingredients.
The research question is whether their exact mechanism boundary supplies a reusable law of
structured endogenous genesis across unlike doctrines. Until a second non-cluster realization and
a cross-doctrine withheld prediction exist, this is a calibration, not the field core.

### Attack F -- it solves a proof route

No route object, zero, determinant, or RH endpoint occurs here. Current proof routes enter only
after the mechanism is independently closed and only as attempted falsifiers.

## 6. Phase-boundary strengthening

For exponent one,

\[
  x_{n+2}x_n=x_{n+1}+1,
  \tag{MG.7}
\]

the initial pair \((1,1)\) follows the finite cycle

\[
  (1,1)\to(1,2)\to(2,3)\to(3,2)\to(2,1)\to(1,1).
  \tag{MG.8}
\]

For exponent two, the visible compatibility still has period two but semantic lineage is open.
Thus recurrence of the compatibility observer does not decide termination. Interaction strength in
the exchange law changes the genesis phase.

This strengthening is paper-elementary. Lean formalization should prioritize the exponent-two
invariant/open-lineage theorem; finite-cycle arithmetic is secondary.

## 7. Literature boundary

Primary parents:

- Fomin--Zelevinsky, *Cluster algebras I: Foundations*, arXiv:math/0104151;
- Musiker--Propp, *Combinatorial interpretations for rank-two cluster algebras of affine type*,
  arXiv:math/0602408;
- Reutenauer, *Linearly recursive sequences and Dynkin diagrams*, arXiv:1204.5145;
- Nobe, *Generators of rank 2 cluster algebras of affine types via linearization of seed
  mutations*, arXiv:1808.08125;
- Chen--Li, *Mutation invariants of cluster algebras of rank 2*, arXiv:2401.09704.

The exact recurrence is occupied. Potential field residue is the law-genesis interpretation and a
future theorem classifying structured compatibility updates between the two certified vacuity
boundaries.

## 8. Acceptance gate

Promote this card only if:

1. all six clauses in Section 4 have dependency-closed paper proofs;
2. the theorem is formalized without axioms, computation certificates, or hidden recurrence
   premises;
3. the paper explicitly labels cluster dynamics as classical calibration;
4. a next conjecture extracts a mechanism invariant usable outside cluster theory.

Do not claim whole-corpus realization, HT generation, physical action, or RH leverage.

## 9. Next mechanism question

What replaces \(H\) in a general compatibility-changing process?

Candidate answer: a **transported semantic certificate** \(C_n\) satisfying two laws:

1. local revision transports \(C_n\) functorially;
2. \((\text{current rulebook},C_n)\) determines the next response, while the rulebook alone does
   not.

The research target is a classification of certificate-bearing mutations for which recurrent
observed rulebooks force either termination, open lineage with quantified growth, or singular
admission. This is a mechanism programme, not a request for one universal object.

## Log

- 2026-08-10 -- opened after the attenuated noncommuting-formation candidate was found already
  formalized in the corpus and rejected as regression.
- 2026-08-10 -- rank-two affine mutation selected as minimal structured-endogeneity laboratory.
