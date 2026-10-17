# Signed grid traces and tail compactness

- **ID:** signed-grid-trace-compactness-2026-10-17
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Scope:** Infinite-Grid Tail Rigidity Beyond Trap 5; independent BiScaleUncertainty.
- **Guide:** `formal/GaloisForLFunctions/BiScaleUncertainty/README.md` (read-only).
- **Status:** Paper proof and Lean certificate complete; certified package 11.
- **Paper:** `docs/reports/BiScaleUncertainty/SignedGridTraceCompactness.md`
- **Plan:** Prove signed sampling and the two tail implications; prove compactness
  necessity using finite nets centered in the original family; formalize the exact
  three-way equivalence and audit every declaration. `update_plan` is unavailable.

## Exact theorem

For a family of actual compact C² real sources with positive mass and one normalized
energy ceiling K, the following are equivalent:

1. For every epsilon>0, some N makes |h_f(log n)/h_f(0)|<epsilon for every family
   member and every n>=N.
2. Normalized correlations vanish uniformly over the family as |x| tends to infinity.
3. Their closure in the global supremum norm is compact.

Node values remain signed and unrestricted. Grid blindness is only the special case
of an identically zero trace. This extends the certified all-grid compactness question
without erasing nonzero node data. It does not assert exponentially weighted polar
tail control or continuity of the singular energy.

## Evidence and proposed mechanism

Package 7 already gives the grid-free estimate

    exp(-1/2) T |H_f(T)-H_f(log ceil(exp T))|² <= 8K, T>=0.

The error tends to zero uniformly over the family. Thus signed-grid tail decay should
transfer to continuum tail decay; evenness handles negative x. The reverse implication
comes from evaluating at the grid nodes. The same energy ceiling supplies uniform
equicontinuity, so the existing bounded-function compactness theorem should give (2)->(3).
For (3)->(2), use finite uniform nets and each actual compact source's vanishing tail;
audit carefully how centers are chosen in the original family or in its closure.

## Corpus check and remaining gates

- Deep search `grid trace compactness signed tail` was partial at 58.49 seconds,
  with unmeasured semantic coverage; most suggestions were unrelated and are not used.
- Lexical fallback found the actual `autocorr_logarithmicCeilNode_error_sq_le` and
  `HTGeometry.compact_uniformVanishesAlong_of_lipschitz` declarations.
- The latter source was read fully. Its pointwise hypothesis covers its entire parameter
  space; applying it to a closure requires proving the relevant vanishing property or
  restricting the parameter type. Do not silently assume that hypothesis.
- Existing package 8 uses `HTGeometry.isCompact_closure_bcf_of_uniform_tails`.
- Search logs: `/tmp/infinite-grid-signed-trace-{search,ingredients}.txt`.
- [x] Audit exact quantifiers, empty family and zero ceiling. Use max(K,0) for
  the energy-controlled modulus; finite-net necessity also handles an empty net.
- [x] Complete paper proof and check corpus overlap. Current deep search completed
  in 76.06 seconds; older-generation coverage snapshot, semantic coverage unmeasured.
  Actual source APIs and the original-center finite-net lemma were inspected directly.
- [x] Derive every analytic input from actual sources; verify names in scratch Lean.
  Name probe passed and was cleaned up. `SignedGridEnergySources.lean`
  passes its direct leaf check without diagnostics: actual source domain, compact
  correlation support, signed quadratic sampling bound and common sampling radius.
- [x] Formalize, run direct leaf and axiom checks, wire umbrella and run formal lint.
  All three leaves pass without diagnostics. All 22 public declaration audits use
  only `propext`, `Classical.choice`, `Quot.sound`; the private finite-family helper
  is covered transitively. All imports and API pairs verified. Lint reports only
  seven foreign unwired modules, listed in the paper. Count once: total 11/100.

## Certified conclusion and next question

Uniform signed-grid decay, uniform continuum tails and global compact closure
are exactly equivalent on the actual bounded-energy source domain. The criterion
requires neither zero samples nor a common support bound. Uniformly trace-tight
sequences have global uniform correlation subsequences. Polar-weighted tails and
singular-energy continuity are not asserted.

Next candidate: `../0-backlog/distant-copy-topology-classification-2026-10-17.md`.

## Separate origin refinement

Investigate whether a fixed finite-energy source f and perturbations q_n with
R(q_n)->0 and bounded raw J(q_n) satisfy
J(f+q_n)-J(f)-J(q_n)->0 without support separation. Split the mixed increment at a
positive cutoff: weighted Young bounds use the small origin energy of fixed f,
and the positive-cutoff tail should be controlled by vanishing source mass.
If proved, this would replace sign selection by exact prescribed energy defects.
It is unproved and not part of the signed-trace conjecture's count.
