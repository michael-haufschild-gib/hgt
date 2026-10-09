# Generic moment divergence inside the bounded-history cube

- **ID:** weil-logshift-bounded-cube-genericity
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** local Lean corpus: adaptive antipodal recovery, generic moment divergence, cofinal recovery cutoffs, and one-sided local divergence laws.
- **Statement:** In [-1,1]^ℕ, all three log-2 moments are nonsummable on a dense residual set. For every bounded history, the three summability conditions are equivalent. Generic nonsummability also holds at every shift with |y|≥log 2.

## Scope and audit
Only local Lean corpus and installed Lean API checks. Previous turn proved generic nowhere summability in unrestricted history space. That result does not imply genericity in the bounded cube. Direct corpus search and exhaustive relevant source search found no bounded-cube theorem or finite-prefix antipodal extension.

## Dependency-closed paper proof
[PROVED HERE] Modify the existing adaptive policy only at the first M steps, choosing a prescribed bounded history there. Thereafter choose ±1 opposite the current probe. Triangular stabilization still gives exact samples; each later correction has probe magnitude at least 1, and the existing diagonal/full-kernel comparison forces every later absolute log-2-weighted deviation term to be at least 1/2. Every final history value lies in [-1,1]. No new builder is needed.

For each N, the event that some n≥N+2 has absolute weighted term greater than 1/4 is open in the bounded product cube, since reconstructed coefficients depend continuously on history. It is dense: the finite-prefix antipodal extensions converge coordinatewise to any target bounded history. Their countable intersection is dense and residual by the existing corpus category theorem and the cube's Baire property. Its weighted terms fail to tend to zero, hence signed summability fails.

For any bounded history, signed summability implies both one-sided summability conditions. Conversely, either finite one-sided moment together with signed nonsummability would force the actual probe to tend to minus or plus infinity along all real cutoffs. The cofinal bounded recovery mesh excludes both alternatives. Thus the three local summability conditions at log 2 are equivalent, without any extra analytic hypothesis on cube elements.

Inward transfer extends nonsummability to every shift with |y|≥log 2. This does not assert anything about shifts |y|<log 2, nor boundedness at intervening real cutoffs.

## Plan
1. Check bounded product's category/topology APIs.
2. Generalize the existing antipodal theorem to preserve finite prefixes, factor its bounded-mesh one-sided implication, and expose shared deviation continuity; preserve existing APIs.
3. Formalize bounded prefix extensions, open dense tail events, moment equivalence, category classification, and outer-shift transfer.
4. Compile touched leaves, audit every public declaration, wire imports, refresh index, run lint, update memory, clean scratch.

## Gates
- [x] Corpus audit and dependency-closed paper proof.
- [x] Exact Lean declarations compiled and axiom-audited.
- [x] Imports, index, scoped checks, and global lint recorded.

## Formal results

New leaf: `formal/GaloisForLFunctions/RHTower/WeilLogShiftBoundedCubeGenericity.lean`.
Sixteen public declarations: one type abbreviation, four definitions, eleven theorems.

- `WeilLogShiftBoundedHistory := ℕ → Set.Icc (-1:ℝ) 1`, with the product topology.
- `weilLogShiftBoundedHistoryValues`, `continuous_weilLogShiftBoundedHistoryValues`: real-valued coordinates and continuity.
- `weilLogShiftBoundedHistoryTerm`, `continuous_weilLogShiftBoundedHistoryTerm`: absolute log-2-weighted reconstructed deviation and continuity.
- `weilLogShiftBoundedHistory_probe_bound`: every visible recovery sample is bounded by one.
- `exists_weilLogShiftBoundedHistory_prefix_large_terms`: exact arbitrary finite bounded prefix, with all later absolute weighted terms at least 1/2.
- `weilLogShiftBoundedTailEvent`, `isOpen_weilLogShiftBoundedTailEvent`, `dense_weilLogShiftBoundedTailEvent`: strict 1/4 tail events are open and dense.
- `dense_and_residual_weilLogShiftBoundedTailEvents`: all such tail events occur densely and residually.
- `weilLogShiftBoundedHistory_summability_equivalences`: for every cube element, signed summability at log 2 iff excess summability, and iff deficit summability.
- `WeilLogShiftBoundedOuterDivergence`, `weilLogShiftBoundedOuterDivergence_of_tailEvents`: persistent terms force all three series nonsummable for every |y|≥log 2.
- `dense_and_residual_weilLogShiftBoundedOuterDivergence`: this simultaneous outer-shift property is dense and residual in the bounded cube.
- `isMeagre_weilLogShiftBounded_some_outer_moment`: any convergent signed/excess/deficit moment at any outer shift is a meagre exception within the cube.

Reused and generalized existing implementations:
- `WeilLogShiftBoundedRecoveryNoGo.lean`: added `exists_antipodal_recovery_after_prefix` and `nonsummable_excess_deficit_of_bounded_recovery`; original two counterexample theorems now specialize these results without changing their public statements.
- `WeilLogShiftGenericMomentDivergence.lean`: added `continuous_weilDeviation_recoveryInverse`; existing origin-term continuity now specializes it. All prior category results remain unchanged.

## Verification

- All three touched leaves compile/export with exit 0 and no diagnostics. The new cube leaf passed its first compilation.
- All 35 public declarations across those leaves, including the type abbreviation: exact axiom set `[propext, Classical.choice, Quot.sound]`, scratch audit exit 0.
- Nineteen new public declarations; sixteen prior public declarations retained.
- Cube compactness/Baire instances and new topology APIs checked in scratch Lean.
- Umbrella wired; index refresh exit 0; all 35 API rows checked for unique names and correct modules.
- Scoped whitespace/conflict-marker checks and `git diff --check` passed.
- Global lint exited 1 only for unrelated unwired `RHTower.LeeYangProducerFieldDensity` and `HTGeometry.BandKernelOperators`. Neither was modified. This replaces prior lint snapshots.
- No new analytic assumptions/axioms, proof gaps, numerical experiments, raised heartbeat/recursion limits, web/external-paper sources, umbrella builds, commits, or subagents.

## Interpretation and limits

Boundedness of the complete recovery history does not make finite moments typical. Within the compact unit cube, generic histories fail all three local moments at and beyond log 2. The exact positive classification is the equivalence of signed and either one-sided summability at log 2 for every cube element, together with arbitrary finite-prefix antipodal extension.

This is a category statement, not a probability statement. It neither proves convergence for interior shifts |y|<log 2 nor proves that the exceptional outer-convergence set is nonempty. It does not bound the actual probe between recovery samples and gives no RH conclusion.

## Next conjecture

The universal signed interior question is now resolved negatively by `WeilLogShiftOriginDiagonalDivergence`: even the origin diagonal grows exponentially, and every finite bounded prefix extends to one history with nonsummable signed moments at every real shift. These histories are dense in the unit cube. This does not extend this card's residual or one-sided conclusions to the origin; those require separate arguments. Boundedness of the actual probe at every positive real cutoff remains unresolved.

The subsequent uniform and finite-matrix receiver cards give exact quantitative reformulations and discharge the affine baseline premise using a bounded arithmetic anchor. The smooth-edge result then proves those finite matrix budgets unbounded at every real shift. The equivalences and Lipschitz implications remain valid; their universal moment premise fails for this recovery mesh.

## Log
- 2026-10-09 — previous turn classified verified progress; bounded-cube theorem and exact one-sided equivalence derived from existing Lean results.
- 2026-10-09 — bounded product compactness/Baire APIs verified. Generalized antipodal construction and factored bounded-mesh implication compile/export cleanly; original counterexamples retained. Shared deviation continuity compiling; bounded-cube leaf written, verification pending.
- 2026-10-09 — shared deviation continuity and all prior generic-moment declarations compile/export cleanly. New bounded-cube leaf is compiling on owned session 43948. Audit list contains all 35 public declarations across the three touched leaves.
- 2026-10-09 — cube leaf and all 35 public axiom audits passed. Exact three-way equivalence, generic outer divergence, and meagreness formalized; imports/index/scoped checks complete.
