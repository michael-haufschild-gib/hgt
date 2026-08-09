# Finite monotone compatibility revision termination law

- **ID:** ULF-GTM-1
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / GENESIS TERMINATION BOUNDARY
- **Statement:** A process that strictly adds compatibility facts at every active step cannot have
  an infinite active history when its compatibility vocabulary is finite.
- **Status:** [PROVED HERE] [DEPENDENCY-CLOSED] [LEAN-CERTIFIED] [MECHANISM BOUNDARY]
  [FINITE MONOTONE TERMINATION] [POSITIVE SURVIVOR] [NOT RH]

## 1. Setup

Let `E` be a finite set of possible compatibility facts. A rulebook state is a finite subset

\[
  R_n\subseteq E.
\]

A **strict monotone active revision** is a history indexed by natural numbers satisfying

\[
  R_n\subsetneq R_{n+1}
  \quad\text{for every }n.
  \tag{FT.1}
\]

The word active excludes scheduled no-op time. A process may pause arbitrarily; remove pauses before
applying the theorem.

## 2. Termination theorem

### Theorem 2.1 -- no infinite strict finite-vocabulary revision

No history satisfying (FT.1) exists.

#### Proof by cardinal growth

Every strict inclusion increases cardinality:

\[
 |R_n|<|R_{n+1}|.
\]

But `|R_n|<=|E|` for every `n`. Hence there can be at most `|E|-|R_0|` strict additions. An
infinite strict history is impossible. QED.

#### Equivalent proof by finite pigeonhole

The powerset of `E` is finite, so any natural-number-indexed history repeats a state: `R_i=R_j`
for some `i!=j`. Strict monotonicity makes the history injective, contradiction. This is the proof
formalized in Lean.

## 3. Exact consequence

Finite monotone compatibility enrichment is a completion procedure, not an open-genesis mechanism.
It can be long, but its number of strict active revisions is bounded by the finite vocabulary.

### Strongest positive survivor

Any infinite strict law history must expose at least one of:

1. infinitely growing compatibility vocabulary;
2. nonmonotone withdrawal of old facts;
3. changing admission, so the effective fact universe is not fixed;
4. retained history not represented by the endpoint subset;
5. a nonactive time parameter containing infinitely many no-ops, which is not law genesis.

This list is exhaustive relative to the theorem's hypotheses.

## 4. Law-genesis trilemma

Together with two independent certified boundaries:

- ULF-RLM-12: fixed exact polarity collapses;
- ULF-ECM-1: arbitrary endogenous polarity realizes every transition;

Theorem 2.1 yields:

> A predictive open-genesis theory must be structured, nonstationary in vocabulary/admission, or
> history-retaining. It cannot be fixed exact closure, arbitrary self-modification, or finite
> monotone saturation.

The statement is a mechanism constraint, not a proposed universal object.

## 5. Sharp scope

1. Infinite `E` permits infinite strict chains.
2. Nonmonotone histories can cycle on finite `E`.
3. A monotone history with inserted no-op times may be infinite as a clocked sequence while having
   only finitely many strict revisions.
4. The theorem supplies no canonical rule for generating new vocabulary or withdrawing old facts.
5. No proof route, topology, positivity law, arithmetic source, or RH endpoint enters the proof.

## 6. Lean certification

`GaloisForLFunctions.HTGeometry.ConstitutiveFiniteRevisionTermination` certifies:

- impossibility of a natural-number-indexed strict chain of finite compatibility states;
- a monotone finite-vocabulary history has at least one stable adjacent step;
- a closed capstone quantifying over every finite vocabulary and history.

The module is wired into the Universal Law Field umbrella. Direct elaboration, final umbrella build,
forbidden-token scan, and axiom audit are recorded in Stage 3.

## Log

- 2026-08-09 -- finite monotone active revision proved terminating; third boundary of the
  law-genesis trilemma closed.
