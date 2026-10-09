# Generic recovery histories have no finite moments

- **ID:** weil-logshift-generic-moment-divergence
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** local Lean corpus: recovery-domain density, coefficient lift, inward potential transfer, countable open-dense intersection.
- **Statement:** A residual dense set of recovery histories has nonsummable signed, excess, and deficit moments at every real shift. A stronger generic property is arbitrarily large positive and negative origin-weighted terms arbitrarily far out.

## Scope and audit
Only local Lean sources and installed Lean API checks. Prior increment proved density of every realized moment profile. Current search found no existing category classification of these profiles; the corpus already supplies a general countable open-dense intersection theorem in `HTGeometry/CountableResidualIntersection.lean`.

## Dependency-closed paper proof
[PROVED HERE] For each natural threshold K and tail cutoff N, consider histories whose reconstructed coefficient sequence has some n≥N+2 with signed deviation times the paired origin kernel greater than K, and separately less than −K. Each condition is open: it is a union of strict inequalities on continuous individual reconstructed coefficient coordinates.

Each condition is dense. Lift the baseline weights ±(K+1)/P_0(n), and splice an arbitrary finite target-history prefix onto that baseline. At a later index n, the weighted deviation is exactly ±(K+1). As the matched prefix grows, the resulting histories converge coordinatewise to the target. The inverse changes only the invisible coordinates, so reconstruction preserves the relevant deviations.

The countable intersection of these open dense conditions is residual and dense in real sequence space. Its origin-weighted terms have arbitrarily large excursions of both signs in every tail. Summability of excess or deficit would force its nonnegative terms to zero, contradicting the appropriate excursions. Signed summability implies summability of excess (existing corpus lemma), so also fails. If any one of these three series were summable at any real shift, inward transfer would make it summable at the origin. Thus all three domains are empty simultaneously.

Positive survivor: an explicit dense residual family with signed weighted excursions in both directions, stronger than absence of moments. The exceptional set where any of the three moments converges at even one shift is meagre. This describes the product topology on arbitrary coefficient histories, not a probability measure, and asserts neither RH nor boundedness of actual probes at every real cutoff.

## Plan
1. Verify topology/category APIs and Baire instance; prove reconstruction preserves deviation and weighted-coordinate continuity.
2. Prove open dense tail-excursion conditions and combine them over natural thresholds/cutoffs and two signs.
3. Deduce simultaneous nowhere summability, density/residuality, and meagreness of any convergent moment.
4. Compile/export, audit public axioms, wire imports, refresh index, run lint, record memory, and remove scratch.

## Gates
- [x] Corpus audit and closed paper proof.
- [x] Exact Lean results compiled and axiom-audited.
- [x] Imports, index, scoped checks, and global lint recorded.

## Original formal results

Leaf: `formal/GaloisForLFunctions/RHTower/WeilLogShiftGenericMomentDivergence.lean`.
Four definitions and eight public theorems:

- `weilDeviation_recoveryInverse_history`: reconstruction preserves every normalized deviation, including invisible indices.
- `weilLogShiftRecoveryOriginTerm`, `continuous_weilLogShiftRecoveryOriginTerm`: continuous weighted coefficient coordinates on history space.
- `weilLogShiftRecoveryTailExcursion`: either chosen sign exceeds a natural threshold beyond a prescribed cutoff.
- `isOpen_weilLogShiftRecoveryTailExcursion`, `dense_weilLogShiftRecoveryTailExcursion`: openness and constructive density for each sign, threshold, and tail.
- `WeilLogShiftTwoSidedExcursions`, `dense_and_residual_weilLogShiftTwoSidedExcursions`: all signed tail excursions simultaneously, densely and residually.
- `WeilLogShiftNowhereSummable`: signed, excess, and deficit series are nonsummable at every real shift.
- `weilLogShiftNowhereSummable_of_twoSidedExcursions`: exact implication through origin term tests and inward transfer.
- `dense_and_residual_weilLogShiftNowhereSummable`: the nowhere-summable histories are dense and residual.
- `isMeagre_weilLogShift_some_summable_moment`: admitting even one summable moment of any of the three kinds, at any real shift, is meagre.

The category step directly reuses `GaloisForLFunctions.HTGeometry.dense_and_residual_setOf_forall`. Inward transfer handles the uncountable real-shift choice; no uncountable-union category assertion is used.

## Original verification

- Final leaf compile/export exited 0, no diagnostics.
- All twelve public declarations: scratch axiom audit exit 0, exactly `[propext, Classical.choice, Quot.sound]` each.
- Baire instance for `ℕ → ℝ` and all new category APIs verified in scratch Lean.
- Umbrella wired; index refresh exit 0; all twelve API rows verified unique and assigned to the correct module.
- Scoped whitespace/conflict-marker checks and `git diff --check` passed.
- Global lint exited 1 with one unrelated unwired module: `HTGeometry.BandKernelOperators`. No change made to that module. This supersedes earlier lint snapshots.
- Fixed three Boolean/conditional simplifications and removed one redundant tactic; no increased heartbeat or recursion limit.
- No new analytic hypotheses/axioms, proof gaps, numerical experiments, web or external-paper sources, full/umbrella builds, commits, or subagents.

## Interpretation and limits

Every realizable moment profile remains dense by the preceding theorem, while the profile with all three domains empty is residual. Thus profiles with any nonempty convergence domain are topologically small even when dense. Residuality is a category statement, not a probability claim. These are arbitrary real coefficient histories, without added arithmetic constraints; no RH conclusion follows.

The result concerns the entire product space of histories. It does not classify genericity inside a bounded-history cube, and it does not settle boundedness of actual probes at every positive real cutoff.

## Follow-up proved: bounded-cube genericity

[Bounded-cube genericity](weil-logshift-bounded-cube-genericity.md) now proves this conjecture, and extends the generic conclusion to every shift |y|≥log 2. It also proves that signed, excess, and deficit summability at log 2 are equivalent for every unit-bounded history. This leaf now exposes `continuous_weilDeviation_recoveryInverse` and specializes it for origin-term continuity; all prior declarations remain unchanged. The follow-up audits all 35 public declarations across its three touched leaves. Interior shifts remain unresolved.

## Log
- 2026-10-09 — previous goal turn classified verified progress. Replaced partial-sum sublevel approach by stronger signed tail-excursion construction before formalization.
- 2026-10-09 — all twelve public declarations compiled/exported; final leaf check exit 0 with no diagnostics. Reused corpus countable-intersection theorem. Imports wired; index refreshed; all twelve API rows inspected. Axiom audit remains live on owned session 5881. Global lint exited 1 only for unrelated unwired `HTGeometry.BandKernelOperators`.
- 2026-10-09 — axiom audit session 5881 exited 0; all twelve declarations use exactly the standard axioms. Category classification formalized; bounded-cube question recorded separately.
