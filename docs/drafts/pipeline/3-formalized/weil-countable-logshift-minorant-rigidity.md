# Countable log-shift tests determine every Weil minorant

- **ID:** weil-countable-logshift-minorant-rigidity
- **Stage:** 3-formalized
- **Type:** PREMISE REDUCTION / exact coefficient-fiber classification
- **Source:** `RHTower/WeilFullConeMinorantRigidity.lean`, especially
  `eq_vonMangoldt_of_weilPositiveFull_of_le`.
- **Write scope:** that existing Lean module, this card, and session memory. Preserve
  every existing public theorem statement. No unrelated module edits or full builds.

## Exact theorem

Define P(lam) to mean nonnegativity of the actual full Weil functional on
`EF.weilTest f f`, for the explicit tests
`f = logShiftRiemannDifference (k : R) (log m)`, at every natural k,m with
`2 <= m` and `(m : R) <= exp(2k)`.

Lean proves the unconditional classification, for every lam:N→R:

`(lam(n)<=Lambda(n) for all n>=2) AND P(lam)`
iff
`(lam(n)=Lambda(n) for all n>=2) AND P(Lambda)`.

Thus full-cone positivity is unnecessary for coefficient rigidity below Lambda:
a countable family, finite at each integer window, already separates every proper
minorant. No sign, growth or summability condition on lam is added.

This is NOT an RH criterion. Equality lam=Lambda plus P(Lambda) does not supply
full-cone positivity. The existing RH corollary must retain its full positivity
hypothesis; do not replace it with P without an independently proved implication.

## Paper proof [PROVED BY SOURCE AUDIT]

The complete source proof at lines 910–1101 was inspected, including its comparison
function and summability arguments. Its single use of `hW : WeilPositiveFull lam`
is `hW f hfd hfc`, where f is exactly the log-shift difference above. The selected
shift m maximizes the nonnegative deficit `(Lambda(m)-lam(m))/sqrt(m)` on
`2 <= m <= floor(exp(2L))`. All subsequent inequalities need only the nonnegativity
of this one test and the already proved kernel/tail estimates.

Replace the selected real L by the natural ceiling of the maximum of the same three
thresholds L1, L2 and log(n0)/2+1. Increasing L preserves all threshold requirements.
The new L is an integer window, and m<=floor(exp(2L)) implies the required real
bound m<=exp(2L). Thus P(lam) supplies the only positivity invocation in the proof.
The original contradiction and exact coefficient equality follow unchanged.

Transport test positivity between coefficient-equal lam and Lambda using the existing
`weilFullFunctional_congr`, which ignores n<2. This proves both directions of the
classification. Conversely, full Weil positivity trivially supplies P(lam), so the
existing theorem can become a short wrapper around the stronger classification.

## Corpus audit and limits

The semantic query `Weil positive minorant rigidity approximate domination`, filtered
to RHTower, returned partial=true with no candidates. Switched to lexical
`WeilPositiveFull` with the per-module cap removed and used exhaustive Lean text search
for the actual log-shift symbol. `logShiftRiemannDifference` occurs only in the source
minorant module. Existing users of the old theorem are in `WeilFullConeRemovedPrimes`
and `WeilConeOrderComparableRigidity`; `WeilFullConeSummableDeficitRigidity` cites it
in prose. Preserve those call signatures.

The neighboring `WeilPrimeMeasureRigidityCountable` treats countably many summable
prime perturbations with a summable logarithmic moment and all-aperture nonnegative
ground energy. Its source statement is distinct from countably many explicit probe
tests for arbitrary pointwise minorants. `WeilFullConeOneSidedCriterion` uses cones
of finite combinations of general test functions, rather than this explicit family.
No matching restricted-test classification was found. Semantic coverage remains
unmeasured; no external novelty claim or external reading.

## Implementation plan

- [x] Audit the full selected proof and distinguish existing countable-perturbation results.
- [x] Paper reduction to cofinal integer windows and exact two-way classification.
- [x] Verify natural-ceiling APIs in the current toolchain using a /tmp scratch file.
- [x] Recheck that the source file remains unmodified by other work before editing.
- [x] Introduce P and extract the stronger classification in the source module.
- [x] Replace the original proof with a statement-preserving wrapper, avoiding duplication.
- [x] Direct leaf and axiom audits for changed/new declarations and existing RH receiver;
  check callers, generated index, umbrella reachability, and authoritative lint.

**[FORMALIZED]** The source-integrated integer-window extraction, both caller leaves
and all seven axiom checks pass. At this increment's final check, the repository lint gate failed on ten unrelated
umbrella-reachability errors, listed below. No RH advancement is claimed.

## Verification checkpoint

The current-toolchain API probe passed: `Nat.le_ceil` gives the required real upper
bound, and the full-functional congruence ignores coefficients below 2 as required.
The scratch proof reported one missing explicit natural-to-real cast in the new
window definition. That cast was corrected before source integration. An exact
byte comparison confirmed the source still matched its audited snapshot before
editing. The countable-test predicate and full iff now contain the original core
argument once; the old public signature is preserved as a short wrapper.
The first direct leaf attempt reached the default 200000-heartbeat limit near the
end of the nested proof. The coefficient-identification argument is now a separate
unconditional set-inclusion theorem, `weilLogShiftMinorants_subset_exact`; the iff
uses it in a short proof. The comparison and final arithmetic tactics use only
their needed inequalities. No heartbeat limit was increased. The direct source audit
passed with exit 0 and no diagnostics after explicitly unfolding the set-membership
goal. The legacy theorem signature is byte-identical, and the existing RH receiver
is unchanged. All fifteen owned `/tmp/hgt-weil-logshift*` scratch files were
removed after the final checks; no matching artifacts remain. All owned jobs exited.
Serena symbol retrieval rejected the formal path as ignored; the edit used a checked,
targeted replacement instead. No heartbeat option was added or changed.

## Final verification

- `lake --old env lean -o <leaf.olean> <leaf.lean>` passed, without diagnostics, for
  `WeilFullConeMinorantRigidity`, `WeilFullConeRemovedPrimes`, and
  `WeilConeOrderComparableRigidity`. Commands were sequential; no full build.
- The final `/tmp` axiom probe passed for the new predicate, both new theorems,
  the original minorant theorem, the unchanged RH receiver, and the two directly
  affected caller theorems. Every dependency list is exactly
  `[propext, Classical.choice, Quot.sound]`. The scratch probe's initial two
  caller-name errors were corrected using their actual source namespaces.
- `scripts/formal_tools.py index` passed. All three new API declarations and both
  existing receiver declarations appear in the generated index.
- The existing RHTower umbrella imports the modified module exactly once.
- `git diff --check` passed. No heartbeat override or proof-debt declaration was
  added. The original minorant statement is byte-identical; the RH receiver's
  statement and proof are unchanged.
- `scripts/formal_tools.py lint` exited 1 solely for the following unrelated
  owned modules being unreachable from their theorem-area umbrellas:

```
RHTower.CCMFullGroundZeroSideEigen
RHTower.ChronologicalBoseDilateCompleteness
HTGeometry.ApertureConeCalculus
HTGeometry.ApertureConeWinding
HTGeometry.ApertureLogTranslation
HTGeometry.ApertureOpenHistoryIdeal
HTGeometry.BoundaryCoronaCStarAlgebra
HTGeometry.PaperFourierLLogL.Compress.Search
HTGeometry.PaperFourierLLogL.Finite.Law
HTGeometry.PaperFourierLLogL.HeightLayers
```

These modules were not edited for this task. Lint was not reported as passing.

## Exposed next conjecture

The same estimates suggest uniform finite separation with a negative margin:
for a fixed coefficient and positive prescribed deficit, all sufficiently large
integer windows should expose a violating probe for every such minorant, with
one cutoff independent of the minorant. The paper argument and precise
quantifier order are recorded in
`docs/drafts/pipeline/3-formalized/weil-uniform-finite-minorant-separation.md`.
That strengthening is now formalized. The shared arithmetic core lives in
`exists_uniform_logShift_minorant_separation`; the countable inclusion is its
short consequence. All public statements from this card remain unchanged.
