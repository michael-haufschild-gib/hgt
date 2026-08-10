# Static failure-kernel exchange universality — failed

- **ID:** ULF-FKT-FAIL-2
- **Stage:** 5-failed
- **Claim killed:** Minimal failure kernels of a monotone or idempotent consequence doctrine obey a
  universal exchange, matroid, antimatroid, Helly, or convex-geometry law.
- **Verdict:** [FALSIFIED] [REPRESENTATION TOO GENERAL] [POSITIVE SURVIVOR PROMOTED]
- **Lean status:** pending exact formalization of the killing representation theorem; the positive
  overlap survivor is the first formalization target.

## Killing theorem

Let `V` be any set and let `H` be any clutter on `V`: a family of subsets no one of which properly
contains another.  Add one new symbol `a` and define a consequence operator on `V ⊔ {a}` by

\[
  c_H(S)=S\cup
  \{a:\text{some }K\in H\text{ satisfies }K\subseteq S\cap V\}.
  \tag{F.1}
\]

Then `c_H` is extensive, monotone, and idempotent.  Relative to the premise base `V`, its minimal
derivation kernels for `a` are exactly the members of `H`.

Extensivity and monotonicity are immediate.  Idempotence holds because the only new fact added by
`c_H` is `a`; adding `a` cannot create a new inclusion `K subseteq S cap V`.  Every `K in H`
derives `a`.  If a proper subset of `K` derived `a`, it would contain some `L in H`; clutter
minimality would force `L=K`, contradiction.  Conversely, every minimal set deriving `a` contains
some `K in H`, so minimality makes it equal to `K`.

Thus every finite clutter, including ones violating circuit elimination, accessibility, Helly
bounds, and every proposed uniform exchange axiom, already occurs inside an idempotent consequence
doctrine.

For example, `H={{1,2},{1,3}}` violates matroid circuit elimination: the two kernels meet in `1`,
but no kernel is contained in `{2,3}`.

## Exact why the representation failed

The finite theorem ULF-FKT-1 extracted the blocker/transversal kinematics of a failure after its
minimal supports were known.  It placed no law on how those supports were produced.  Monotonicity,
extensivity, and idempotence constrain closure of consequences, but they impose no relation among
the minimal supports of one selected conclusion.  Asking those axioms for kernel exchange was
therefore asking an arbitrary clutter to manufacture geometry.

This also kills CFL-B in `counterfactual-law-science.md` as stated: well-behaved intervention
composition alone does not force minimal repair sets to be matroidal or antimatroidal.

## Positive-survivor search

The static family is arbitrary, but transport of positive kernel profiles through an observer is
not.  If source atoms are aggregated along observer fibres, addition is strict while common-support
meet is only lax.  The resulting nonnegative false-overlap defect:

1. vanishes for every profile pair exactly for injective observers;
2. equals lost total-variation distinguishability;
3. obeys an exact composition/chain law;
4. localizes which observer exit made independent failures appear to share a repair.

That survivor is proved in:

`docs/drafts/pipeline/2-fully-proven/universal-law-field/failure-kernel-transversal-mechanics/positive-observer-lax-overlap-defect-composition-and-distinguishability-budget-law.md`.

## Representation lesson

Static obstruction incidence is not the missing field.  Nontrivial laws first appear after adding
typed doctrine morphisms and asking what algebraic operations they preserve strictly, laxly, or not
at all.  The successor primitive is therefore an **exchange defect of mechanisms**, not a special
class of kernel objects.

## Parent boundary

The killing construction is the elementary clutter/edge-ideal correspondence.  Hypergraph ideals,
blocker duality, kernel contraction, and monotone Boolean functions already contain it.  No novelty
claim is made.

## Log

- 2026-08-10 — arbitrary-clutter realization killed static exchange, matroid, antimatroid, and
  Helly conjectures; lax-overlap transport extracted as positive survivor.
