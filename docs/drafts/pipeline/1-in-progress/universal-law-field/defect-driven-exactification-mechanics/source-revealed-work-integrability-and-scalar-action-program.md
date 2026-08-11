# Source-revealed work integrability and scalar-action program

- **ID:** ULF-DDE-2
- **Stage:** 1-in-progress
- **Type:** MECHANISM CONJECTURE / PROOF PROGRAM
- **Statement:** Repair cost should be reconstructed from source interventions by a cyclic-work
  integrability law; positive work cycles are exact obstructions to every scalar action selector.
- **Status:** [CONJECTURE] [MECHANISM NOT OBJECT] [ROUTE-INDEPENDENT]
  [PARENT THEORY: CONVEX ANALYSIS / DIFFERENCE CONSTRAINTS] [EXCHANGE SURVIVOR PROVED]
  [FINITE ENVELOPE CORE OPEN]

## 1. Failure-driven pivot

ULF-DDE-1 proves that choosing a minimum-norm primitive is nonpredictive when the metric is free:
every repair can be made uniquely minimum-cost. The stronger question is therefore not

> Which cost should be minimized?

but

> Do source interventions reveal responses that can arise from any coherent scalar work law?

This asks for a mechanism and exact laws, not a carrier object.

## 2. Finite revealed-work mechanism

Let `I` be a finite nonempty set of repair states. Suppose source interventions produce a directed
increment

\[
 \omega(i,j)\in\mathbb R,
 \tag{1}
\]

interpreted as the minimum work that any scalar action must gain when replacing repair `i` by
repair `j`. A scalar action is a function `A:I->R` satisfying

\[
 \omega(i,j)\le A(j)-A(i)
 \qquad(i,j\in I).
 \tag{2}
\]

The data are **cyclically admissible** when every closed finite intervention history
`i_0,...,i_n=i_0` obeys

\[
 \sum_{k=0}^{n-1}\omega(i_k,i_{k+1})\le0.
 \tag{3}
\]

### Conjecture A -- finite constitutive work integrability

Conditions `(2)` and `(3)` are equivalent. When `(3)` holds and a base repair `b` is fixed, the
least normalized action `A_b` is the maximal accumulated work of a path from `b` to the target.
Because `I` is finite and positive cycles are absent, it suffices to maximize over simple paths.

This is expected to be a finite difference-constraint/Rockafellar theorem rather than isolated new
mathematics. Its proposed field role is different: scalar cost becomes a falsifiable consequence of
intervention consistency, not inserted geometry.

## 3. Paper-proof attack

The forward implication is forced by telescoping `(2)` around a closed history.

For the converse, remove repeated-vertex cycles from any walk. By `(3)` every removed cycle has
nonpositive weight, so removal never decreases total work. Every walk is therefore dominated by a
simple path, and only finitely many simple paths exist. Define

\[
 A_b(j)=\max\{\text{weight}(p):p\text{ is a simple path }b\rightsquigarrow j\}.
 \tag{4}
\]

Appending edge `i->j` to a maximizing path for `i` and deleting cycles gives
`A_b(j)>=A_b(i)+omega(i,j)`. Any other normalized action bounds the work of every path by
telescoping, hence dominates `A_b`.

`[OPEN CORE]` Close all path conventions, especially the zero path at `b`, loops, and the
normalization condition needed for the claimed leastness. Then perform a hostile literature audit
against finite difference constraints, Afriat/Rockafellar revealed preference, and dissipativity.

## 4. Proposed mechanism laws

If Conjecture A closes, it supports the following laws.

1. **Intervention-before-energy.** Work increments are produced by legal source interventions;
   potential is reconstructed afterward.
2. **Cycle falsification.** One positive work cycle disproves every scalar-action selector without
   guessing another metric.
3. **Least action envelope.** When cycles pass, path saturation constructs the least compatible
   action relative to one marked origin.
4. **History birth.** Positive cycles force a history-sensitive, vector-valued, or nonconservative
   repair law; they cannot be repaired by changing scalar normalization.
5. **Exchange law.** Combining intervention doctrines changes path weights. Infimal convolution is
   the candidate composition; whether cyclic admissibility survives becomes a theorem, not a
   declaration.
6. **Admission law.** Cofinal validity requires uniform control of the action envelopes. Finite
   cyclic admissibility alone does not supply coercivity or strict completion.

### Exact exchange survivor

`competitive-work-envelope-cycle-birth-and-scalar-integrability-rigidity-law.md` closes the first
nontrivial exchange question. If two exact scalar work laws are combined conjunctively by taking
their pointwise maximum, the combined law is scalar-integrable iff the two parent potentials differ
by a constant. Every genuine disagreement creates a strictly positive two-step cycle. In contrast,
their pointwise minimum is always scalar-integrable. Thus selection can create directed history even
when every parent law is individually exact.

## 5. Hostile attacks already passed or pending

### Attack 1 -- arbitrary metric

Passed. The mechanism never chooses a metric first; it tests response data. ULF-DDE-1's cost
manufacture no longer proves the conclusion because changing the potential cannot remove a positive
cycle.

### Attack 2 -- arbitrary response data

Live. If `omega` is fitted after seeing the desired action, the programme is theatre. Every
application must construct `omega` from pre-target source interventions and prove composition.

### Attack 3 -- rediscovery

Expected verdict: `[BRIDGE]` for Conjecture A itself. Rockafellar's cyclic-monotonicity theorem and
finite difference constraints are parents. Recent work continues to extend Rockafellar-type
representation beyond ordinary cyclic monotonicity, e.g. De Pascale--Pegon:
<https://arxiv.org/abs/2507.09437>. Field content can only lie in source production, exchange, and
cofinal laws, not in renaming convex analysis.

### Attack 4 -- scalar-action insufficiency

Likely. Even a valid scalar action does not encode reversible phase, determinant memory, HT rank, or
admission. Existing Lean theorems already force separation of reversible memory and irreversible
cost. Therefore this mechanism is one constitutive sector, not universal ontology.

## 6. Exact predictions if the mechanism survives

1. Any claimed scalar repair energy must satisfy every finite source-intervention cycle inequality.
2. Two repair systems with the same endpoint minima but different positive-cycle spectra are not
   constitutively equivalent.
3. Observer quotient may create false integrability by collapsing a positive cycle; a conserved
   future reporter must detect the collapsed cycle before scalar action descends.
4. Rank loss of a chosen quadratic model is secondary. Primary failure is either cyclic
   nonintegrability, loss of coercivity, or both.

These predictions involve no RH route. Routes enter only after the finite theorem, exchange law,
and source-generation gate close.

## 7. Death criteria

Retire this candidate if:

- source response increments cannot be constructed without fitting a metric or desired endpoint;
- cyclic integrability adds no constraint beyond already-declared reporter conservation;
- exchange of two cyclically admissible mechanisms has no nontrivial universal law;
- all cross-organ examples require unrelated response definitions;
- the finite theorem is the only survivor and no genesis/cofinal extension follows.

### Exact pathwise survivor

`competitive-path-variation-observer-descent-and-history-production-law.md` closes the arbitrary
finite-history extension. Mandatory and permissive work equal the common endpoint contribution
plus and minus relative total variation. Closed mandatory histories carry exactly half the
variation of `A-B`. The same theorem proves that this memory descends through an observer exactly
when `A-B` is constant on every observer fibre; otherwise one collapsed pair carries positive
invisible work.

This kills the idea that selection history is only a local two-state artifact. It also limits the
programme: the theorem is one mechanism law for competitive selection and quotient loss, not a
common explanation of completion, coercivity, positive-carrier existence, or cancellation.

## Log

- 2026-08-09 -- optimizer-first exactification killed; source-revealed cyclic-work mechanism opened.
- 2026-08-09 -- competitive-envelope theorem proved: mandatory pointwise competition creates a
  positive two-cycle unless parent actions are gauge-equivalent; permissive minimum survives.
- 2026-08-09 -- pathwise extension proved and Lean-certified: closed competitive work is relative
  total variation, with exact observer-descent criterion.
- 2026-08-11 -- multi-parent open core closed by
  `multi-parent-tropical-projective-work-reconstruction-and-prime-recurrence-law.md`.
  Mandatory family work is the tropical maximum of exact parent increments; reversible work is
  exact projective width, closed histories are nonnegative, and observer descent is equivalent to
  vanishing on collapsed two-cycles.  Scalar action exists only on the common-gauge stratum.
  Boolean formation, Mass clocks, and Hankel reconstruction instantiate the law and force a new
  recurrence theorem with linearly escaping projective work.
