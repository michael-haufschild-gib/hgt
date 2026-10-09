# Recovery-domain density — verified progress

Source restriction: only local Lean corpus, no web/external papers. Goal remains ACTIVE. Previous bounded-recovery turn and this turn both made verified progress.

## New leaf and exact API
`formal/GaloisForLFunctions/RHTower/WeilLogShiftRecoveryDomainDensity.lean` imports RecoveryHomeomorphism. Two definitions and nine theorems, 169 lines.
- `weilLogShiftRecoverySplice base height N := RecoveryPrefix base (RecoveryInverse height) (N+2)`.
- `weilLogShiftRecoverySplice_tail base height N n hn`: equals base n for n≥N+2.
- `weilLogShiftRecoverySplice_history base height N k hk`: History(Splice)k=height k for k<N.
- `summable_weilLogShiftRecoverySplice_terms_iff base height N term`: Summable(term n (Splice n)) iff Summable(term n (base n)), for ANY `term : ℕ→ℝ→ℝ`.
- `WeilLogShiftMomentEquivalent lam base`: ∀real y, signed summability iff baseline, AND excess summability iff baseline, AND deficit summability iff baseline. All use pairedLogKernel y n.
- `weilLogShiftRecoverySplice_momentEquivalent`: splices retain this whole profile.
- `tendsto_weilLogShiftRecoverySplice_history base height`: as N→∞, histories of splices tend to height in product topology.
- `dense_weilLogShiftRecoveryHistory_momentClass base`: Dense {height | ∃lam, History lam=height ∧ MomentEquivalent lam base}.
- `exists_weilLogShiftRecoveryPrefix_open_domain height N R`: ∃lam, matches every k<N, Summable(deviationExcess lam), all local excess moments summable, and signed summability at y iff |y|<|R|.
- `exists_weilLogShiftRecoveryPrefix_closed_domain height N R`: same, iff |y|≤|R|.
- `exists_weilLogShiftRecoveryPrefix_entire_domain height N`: exact prefix and signed moments summable at every real shift.
All public main results have no new analytic premise. Radius represented by |R| avoids a positivity hypothesis. Open R=0 yields nowhere convergence; closed R=0 yields singleton origin.

## Mechanism and significance
Only finitely many coefficients change. All coefficientwise summability predicates are tail invariants. Triangular recovery exactly preserves prescribed finite history, and eventually exact coordinate matching proves convergence to any history. Thus every realizable triple of moment domains is dense. Arbitrary finite data determine neither radius nor endpoint inclusion even with finite total excess. Whole positive-real-cutoff boundedness remains OPEN; this result does not answer it. No RH claim or external novelty claim.

## Verification
Leaf final compile/export first attempt exit0, no diagnostics. All11 public declarations #print axioms exactly `[propext, Classical.choice, Quot.sound]`, scratch audit exit0. Umbrella wired; index refreshed; all11 API entries verified unique/correct module. Scoped whitespace/conflict and diff checks passed. Current GLOBAL LINT exit1 only unrelated unwired `RHTower.PaperSuzukiCarrierNullSets` and `RHTower.PaperSuzukiCayleySynthesis` (two errors; tail command can duplicate last line). Supersedes previous two-module snapshots.
Card: `docs/drafts/pipeline/3-formalized/weil-logshift-recovery-domain-density.md`. Bounded-recovery card links this follow-up. No subagents, commits, umbrella builds, numerical experiments, or raised limits.

## Toolchain notes
Verified scratch APIs: `summable_nat_add_iff`, `tendsto_pi_nhds`, `mem_closure_of_tendsto`, `Filter.Tendsto.congr'`, `Filter.eventually_atTop`, `dense_iff_closure_eq`, `Dense.mono`, `summable_zero`, `tendsto_const_nhds`.
For scratch universes use concrete types: `@tendsto_pi_nhds ℕ ℕ (fun _ => ℝ)`; `@mem_closure_of_tendsto (ℕ→ℝ) inferInstance ℕ`; `@tendsto_const_nhds ℝ inferInstance ℕ` (target space first, topology next, source type third). For rewriting arbitrary tails, give named `htail (n)` first; avoid unresolved `n` metavariables inside omega. Function zero equality is reliably rewritten via `funext hzero`.

## Next conjecture, NOT proved
Are histories with nowhere-convergent signed, excess, and deficit moments residual, although all competing realizable profiles are dense? Candidate mechanism: nonnegative partial-moment sublevel sets are closed; finite-prefix freedom should force empty interior. Countable unions may show finite-moment histories meagre. Check current corpus and exact APIs before coding. Inward-transfer to shift0 may reduce all real shifts to one test. Do not claim meagreness or residuality yet.

Session-init efficiency: Serena list_memories result is huge; filter its returned names before printing instead of dumping all research memories. No owned jobs should remain after final cleanup.


## Category conjecture now proved
See `mem:research/weil-logshift-generic-moment-divergence-2026-10-09`: a dense residual family has arbitrarily large signed origin-weighted excursions of both signs in every tail. All three moment domains are empty residually; existence of any summable moment at any real shift is meagre. Twelve new declarations compiled and standard-axiom audited. Latest lint snapshot is one unrelated unwired HTGeometry.BandKernelOperators. Bounded-history cube genericity at log2 remains a separate next conjecture.
