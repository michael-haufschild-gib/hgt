# Bounded-history cube: generic outer divergence — verified progress

Only local Lean corpus and installed Lean API checks. No web/external papers. Goal remains ACTIVE; previous turn and this turn made verified progress.

## New leaf
`formal/GaloisForLFunctions/RHTower/WeilLogShiftBoundedCubeGenericity.lean` (219 lines), imports GenericMomentDivergence and BoundedRecoveryNoGo. Sixteen public declarations (1 abbrev,4 defs,11 theorems):
- `WeilLogShiftBoundedHistory := ℕ → Set.Icc (-1:ℝ) 1`.
- `weilLogShiftBoundedHistoryValues h k := (h k:ℝ)`; `continuous_weilLogShiftBoundedHistoryValues`.
- `weilLogShiftBoundedHistoryTerm h n := |weilDeviation (Inverse (Values h)) n| * pairedLogKernel (log2) n`; corresponding continuity theorem.
- `weilLogShiftBoundedHistory_probe_bound h n hn`: all visible reconstructed recovery samples have magnitude≤1.
- `exists_weilLogShiftBoundedHistory_prefix_large_terms h M`: exists cube history g matching h at every k<M, with all terms n≥M+2 at least1/2.
- `weilLogShiftBoundedTailEvent N`: some n≥N+2 has absolute weighted term>1/4. `isOpen_weilLogShiftBoundedTailEvent`, `dense_weilLogShiftBoundedTailEvent`, `dense_and_residual_weilLogShiftBoundedTailEvents`.
- `weilLogShiftBoundedHistory_summability_equivalences h`: signed moment summable atlog2 iff excess moment summable; signed iff deficit. NO extra analytic hypothesis on cube elements.
- `WeilLogShiftBoundedOuterDivergence h`: ∀real y, log2≤|y| → signed/excess/deficit moments of Inverse(Values h) all nonsummable.
- `weilLogShiftBoundedOuterDivergence_of_tailEvents`.
- `dense_and_residual_weilLogShiftBoundedOuterDivergence`.
- `isMeagre_weilLogShiftBounded_some_outer_moment`: cube histories admitting any of the three summable moments at any |y|≥log2 form a meagre set.

## Generalized existing leaves (old public statements retained)
`WeilLogShiftBoundedRecoveryNoGo.lean` now6 public theorems,168 lines:
- NEW `exists_antipodal_recovery_after_prefix height M`: exists λ with Qλ(k+2)=height k for k<M; |Qλn|=1 and |aλn|P_log2(n)≥1/2 for n≥M+2. Same adaptive builder/paper estimate; policy uses supplied targets before M, antipodal choices afterward. Original `exists_antipodal_recovery_with_large_terms` now specializes M=0.
- NEW `nonsummable_excess_deficit_of_bounded_recovery lam hbounded hbad`: if all visible Qλn have magnitude≤1 and signed log2 moment is nonsummable, then excess and deficit moments atlog2 both nonsummable. Factored from original counterexample, which now calls it.
`WeilLogShiftGenericMomentDivergence.lean` now13 public declarations,197 lines:
- NEW `continuous_weilDeviation_recoveryInverse n`: continuous h↦a(Inverse h)n. Original origin-term continuity specializes it. All category statements unchanged.

## Mechanism
Bounded finite prefixes extend to bounded antipodal histories with persistent weighted terms. These extensions approach any cube element coordinatewise, so strict tail events are open dense; countable intersection in compact/Baire cube is residual dense. Signed norm terms cannot tend to0. Finite either one-sided moment plus nonsummable signed moment would force actualQ(L)→±∞, contradicting bounded cofinal recovery samples. Inward transfer excludes every outer shift simultaneously.
This does NOT prove anything at |y|<log2, does NOT prove exceptional outer-convergence set nonempty, does NOT bound actual probes between mesh samples, and gives no RH claim. Genericity is category, not probability.

## Verification
Final compile/export of all3 touched leaves exit0/no diagnostics. New cube leaf passed first compilation. All35 public declarations (6+13+16), including type abbrev, have EXACTLY `[propext, Classical.choice, Quot.sound]` in scratch audit; audit exit0. Nineteen new declarations plus sixteen prior retained. CompactSpace and BaireSpace of cube verified; new Continuous.abs API checked using `@Continuous.abs.{0,0}` (raw two-type positional args were wrong). Imports wired, index refreshed, all35 API rows unique/correct. Scoped whitespace/conflict/diff checks passed.
LATEST GLOBAL LINT exit1 ONLY unrelated unwired `RHTower.LeeYangProducerFieldDensity` and `HTGeometry.BandKernelOperators` (two errors; tail output duplicates last). No edits to them.
Cards: `3-formalized/weil-logshift-bounded-cube-genericity.md`; prior generic/divergence and bounded-no-go cards updated, failed bounded-moment receiver card records stronger obstruction and positive equivalence. No subagents, commits, umbrella builds, numerical experiments, increased limits. All jobs terminal; all six owned /tmp hgt-weil-bounded-cube-* scratch files removed and absence verified. Final source/card/diff checks passed.

## Next frontier
What do unit-bounded recovery histories force at interior shifts |y|<log2? In particular, is the origin moment finite for every cube element? Quantitative inverse bounds are a possible route. This remains UNPROVED. Do not infer it from current generic outer-divergence theorem or claim log2 is a sharp full classification. Full positive-real-cutoff boundedness remains open too. Keep research corpus-only.


## Verified follow-up: smooth-edge origin obstruction (2026-10-09)
Earlier statements that origin/interior universal signed summability remained open are historical. The new smooth cutoff edge bound proves exponential growth of the inverse diagonal already at origin. Universal bounded-history SIGNED moment summability now fails at EVERY real shift. Every finite cube prefix has an extension with nonsummable signed moments simultaneously at all real shifts; these histories are dense, and each finite matrix budget is unbounded. No residual-origin, one-sided-origin, every-history, or full-positive-real-cutoff claim follows. Exact positive survivor, 11 compiled/axiom-audited theorems, and current three unrelated lint wiring errors are recorded in `mem:research/weil-logshift-smooth-edge-origin-obstruction-2026-10-09`. Final card is docs/drafts/pipeline/3-formalized/weil-logshift-smooth-edge-origin-obstruction.md; old backlog/in-progress copies removed. Next frontier: residual signed nowhere summability using open tail excursions and origin exponential growth.


## Verified follow-up: product-cube residual origin genericity (2026-10-09)
The origin residual question is now settled by `WeilLogShiftKernelTailOrder` and `WeilLogShiftBoundedOriginGenericity`: absolute moment terms are unbounded in every tail at EVERY real shift on a single dense residual subset of the unit product cube. Even eventual boundedness at one history-dependent shift is meagre; any signed summable moment is also meagre. Positive survivors include arbitrary fixed outward kernel gain, origin diagonal tending to infinity, and finite-prefix bounded extensions with origin norm tending to infinity. All12 new public theorems compiled and axiom-audited with exactly the standard set. This does not assert generic norm convergence to infinity, one-sided origin divergence, or supremum-norm genericity. The latter is the next conjecture. See `mem:research/weil-logshift-bounded-origin-genericity-2026-10-09` and docs/drafts/pipeline/3-formalized/weil-logshift-bounded-origin-genericity.md. Latest global lint has only two unrelated wiring errors, recorded there.
