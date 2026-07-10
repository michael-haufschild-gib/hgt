# Nonlinear Finite Selector Oracle Vacuity

- **ID:** nonlinear-finite-selector-oracle-vacuity
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / source-functor guardrail
- **Source:** `finite-type-source-functor-rh-nonselection.md`;
  `rh-landscape-proof-gate.md`;
  `source-selector-repair-obligation-ledger.md`;
  `meta-proof-novelty-gate.md`
- **Statement:** Unrestricted nonlinear finite-valued selectors are vacuous:
  every target property admits a finite-valued selector by its characteristic
  function. Therefore a nonlinear finite source functor has proof content only
  after its definition is source-built and shown not to encode the target
  property.

## Setup

Let `C` be any class of objects and let `P <= C` be any property. In the RH
route, `C` may be a class of completed xi-type objects, while `P` may be:

- the repaired semilocal index condition;
- `kappa_-=0`;
- all-order shifted Stieltjes positivity;
- zero localization on the critical line.

A **finite-valued selector** is a map

`S:C -> A`

to a finite set `A`, together with a subset `B <= A`, such that

`x in P <=> S(x) in B`.

## Theorem

Every property `P <= C` has a finite-valued selector.

In particular, the mere existence of a nonlinear finite-valued selector for RH
has no proof content.

## Proof

Take

`A={0,1}`,

and define

`S_P(x)=1` if `x in P`,

`S_P(x)=0` otherwise.

Then with `B={1}`,

`x in P <=> S_P(x) in B`.

Thus every property admits a finite-valued selector. The construction used the
property itself, so it supplies no independent reason that the property holds.

## Application To RH Source Functors

For the RH route, the following finite-valued maps are exact selectors:

`S(F)=1 iff kappa_-(F)=0`,

`S(F)=1 iff Q_0^F[p]>=0 for every real polynomial p`,

`S(F)=1 iff every reciprocal zero atom lies in R_+`.

Each is a finite-valued selector. Each is also circular if used as a source
axiom or as the decisive source functor, because it names the target condition.

Thus the problem with nonlinear finite selectors is not that they are too weak.
It is that they are too unconstrained. Without a source-built definition, they
can select RH exactly by becoming the target oracle.

## Relation To Finite-Type Source Functors

`finite-type-source-functor-rh-nonselection.md` proves a different statement:
if the local repair decision factors through finitely many real-linear
observables on polynomial-tail perturbations, then a false-nearby object with
the same output exists.

That theorem does not cover arbitrary nonlinear finite summaries. The present
card records why that is the correct stopping point: an unrestricted nonlinear
summary can encode any property, including RH itself.

Therefore a proposed nonlinear source functor must provide more than
finite-valued selection. It must provide a non-oracular source construction.

## Anti-Oracle Gate

A nonlinear finite source functor can enter the RH route only if all of the
following are explicit:

1. **Source formula.** The functor is defined from non-zero source data:
   Euler/local factors, Gamma boundary, functional equation, completed explicit
   formula, finite order, canonical gauge, or a completed polarization.
2. **No target predicate.** Its definition does not mention `kappa_-=0`,
   `s_d>0`, Stieltjes/Herglotz positivity, zero localization, or an equivalent
   repaired-index condition.
3. **Fake-family gate.** Davenport-Heilbronn, sign-reversed prime fakes, and
   finite polynomial-tail fakes fail a named source condition before target
   positivity or zero placement is evaluated.
4. **All-order input.** If the functor is not covered by the finite-linear
   nonselection theorem, the proof must identify the all-order source object
   that prevents finite-tail perturbations.
5. **Transfer theorem.** The argument proves a transfer from the source
   construction to the repaired index; it does not define the source
   construction by the repaired index.

Failing this gate, the nonlinear selector is indistinguishable from
`S_P=1_P` at the logical level.

## Consequence For The Landscape Proof

There are two opposite bad moves:

1. Claiming that every finite-valued source functor is killed by finite-probe
   nonselection. This is false without regularity or factorization hypotheses.
2. Claiming that a finite-valued nonlinear selector is progress merely because
   it selects the right side. This is vacuous unless the selector is built from
   source data without the target predicate.

The live theorem remains:

`source construction => repaired semilocal index`.

The selector itself is evidence only after its source construction and transfer
proof are supplied.

## Source Boundary

This card is a logical guardrail. It proves no positivity for zeta and no zero
localization. Its purpose is to keep the source-functor route from alternating
between two theatre moves: overextending finite-linear nonselection to arbitrary
nonlinear maps, or accepting a nonlinear target oracle as a source theorem.

## Gates

- [x] 0 -> 1 in-progress: entropy selected the nonlinear-functor/oracle route.
- [x] 1 -> 2 fully-proven: characteristic-function selector proof written and
  anti-oracle gate stated.
- [ ] 2 -> 3 formalized: optional elementary set-theoretic selector lemma.

## Log

- 2026-06-24 -- Codex: created under the private RH continuation. The card
  explains why the finite-linear functor kill cannot be naively extended to all
  nonlinear finite summaries, and why unrestricted nonlinear finite selectors
  must pass an anti-oracle gate before they count as source mathematics.
