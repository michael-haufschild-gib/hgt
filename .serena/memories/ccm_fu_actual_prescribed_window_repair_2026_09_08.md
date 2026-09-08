# Actual prescribed-window repair — progress; RH goal still active

Previous/current goal turn made progress: actual prime-batch producer now kernel-closed, including square-root cardinality. RH NOT proved/falsified. Do not mark goal complete/blocked. Full chain: actual divisor source → renewable signed reserve → exhaustive prime selection → uniform signed Abel bound → RH. Next work must attack renewal / prescribed unbounded-quotient primes (especially 2), not re-prove source signs, generic receivers or this finite producer.

## Authoritative files
- docs/drafts/pipeline/3-formalized/ccm-fu-prescribed-window-repair.md: exact statement, complete paper proof, validation and remaining gap.
- docs/drafts/pipeline/1-in-progress/ccm-fu-inherited-debt-source-cycles.md: current bridge state updated.
- Frontier map READ ONLY. Never edit it even if goal replay asks. STATUS unchanged: no new route-independent entry warranted. Preserve external edits, including frontier changes by others.

## Six new public declarations, all audited ONCE
1. MobiusDivisorCoupledTwoSourceCone.lean: exists_mobiusDivisorCoupledTwo_clip_square_reserve. Appended common clipped lower bound d>0 for both a²+b² and (a+b)² at K=2,7,14. Uses existing analytic signs and continuity. File has three old warnings182–184; do not fix or re-audit old declarations.
2. MobiusDivisorApproximateTwoReserve.lean: mobiusDivisorSuccessorEnvelope_two_block_reserve_error. For actual child-inactive two-coordinate batches, Ψ(P∪L)+min(R,T)≤Ψ(P)+2sqrt(Ψ(P))D+D², D=|X|+|Y|. No balance assumption; covers current and EVERY available successor. R=sum p(a_p²+b_p²), T=sum p(a_p+b_p)².
3. BoundedPlaneDisplacementBatch.lean: exists_bounded_plane_displacement_batch. Given bounded packets ‖v‖≤B and unused inward margin c, any finite selected length with available direction supplies distinct list with total initial-plus-selected squared displacement≤2(B²/c+B)². Uses product sup norm and clamped quadratic potential; generic theorem exposes endpoint only.
4–5. MobiusDivisorSquareRootWindowCapacity.lean: tendsto_prime_window_card_div_sqrt; eventually_mobiusDivisorCoupledTwoCapacity_sub_one_ge_sqrt. PNT + log/sqrt decay gives κ−1≥A sqrt(M) eventually at M=14(b+1)N for every fixed A>0. No experiment.
6. MobiusDivisorPrescribedWindowRepair.lean: exists_mobiusDivisor_prescribed_window_repair. ∃fixed b≥15,∀C>0,∃A>0,eventually N, with M=14(b+1)N: for EVERY core P⊇P0 (primes below15 except2), 2∉P, all three windows W at quotients2,7,14 untouched, Ψ(M,P)≤CM², EVERY available prime q with15≤q<M and M/q≤14 admits L containingq, L⊆insertqW, |L|=ceil(A sqrt(M))+1, and Ψ(M,P∪L)+M≤Ψ(M,P). Uniform A/threshold independentP,q. Actual finite distinct primes; no exact circuit-weight realization premise.

## Producer proof details for reuse
Private helpers in PrescribedWindowRepair:
- packet M p P=(sqrtp*I0/sqrtM,sqrtp*I2/sqrtM).
- packet_bound: ‖packet‖≤9 for availablep≠2, quotient≤14, arbitraryP. Uses sum_abs_mobiusDivisorPrimeFibre_le_quotient (3/5 sqrtM * floor(M/p)), single_le_sum and exact reflection.
- core_profile: P⊇P0,2∉P, child≤15 implies child fibres equal existing raw interpolated two-profile. No bound on cardP.
- window_data via retainedPrimeWitnessWindow_data: primep,15≤p<M, floor(M/p)=K, b*clip≤420.
- packet_scale_lower: floor(M/p)≤14⇒M≤16p⇒sqrt(p/M)≥1/4.
- source_window_geometry: choose common small clip tolerance ε, bε≥420; normalized margin c=c0/4, reserve d=d0/16. For any selected L with |L|<κ−1, each window has a point outside insertqL. It needs whole W fresh currently.
- repair_error_budget: H=2*(81/c+9), A=(2sqrtC*H+H²+1)/d. n=ceil(A sqrtM)≤κ−1, normalized greedy sum≤H ⇒physicalD≤HsqrtM, reserves≥dnM cover 2sqrtE D+D²+M.
- n is MINIMUM square-root demand, not full κ. This conserving strengthening passed scratch and final exact emission.

## What remains genuinely open
Untouched-window assumption fails after using a batch: theorem cannot simply be iterated. Square-root use preserves most primes but does not itself prove renewal. A resource-aware extension could replace W by W\P and κ by min remaining window cardinality, yielding only finitely many repairs (roughly κ/sqrtM), insufficient alone to exhaust O(M/logM) primes. Main hard problem remains unbounded quotients / actual prescribed small prime2 and growing/overlapping source labels. Full Ψ AFTER inserting2 involves (2,q) successors not controlled solely by Ψ before2 or the two-coordinate head. Do not claim current endpoint supplies an exhaustive prefix order or signed Abel bound. Prior positive-covariance2,11,15 source circuit and exact inherited cost laws remain available in mem:ccm_fu_inherited_two_cost_positive_source_cycle_2026_09_08. Negative covariance of2,7,14 does NOT prevent both square-reserve contractions.

## Validation / cleanup
All new scratch checks and exact leaf emissions passed; four new leaves emitted without warnings. All six NEW public declarations audited once: only propext, Classical.choice, Quot.sound. No sorry/new axiom/native_decide/experimental premise. Four leaves wired into RHTower umbrella without building it. Generated indexes refreshed. Global lint --check-generated reports 13 unrelated unfinished unwired modules in HTGeometry/HilbertMetric and 2 stale indexes under concurrent edits; no new RHTower/proof-debt errors. Do not change others' unfinished modules to make lint green. Known lake build packaging audit expands broad stale prerequisites; DO NOT retry preflight/full/umbrella builds; report package audit pending. No mathematical computations this turn. No commits/pushes/subagents by us. Exact owned scratch files/processes cleaned after final checks. Reuse required oleans; audit only future new declarations, not these six or previous eighteen.

## Build discipline
One owned foreground Lean process at a time. Check terminal exit before next Lean. lake env lean /tmp/scratch.lean; emit ONLY required leaf olean with lake env lean path -o .lake/build/lib/lean/path.olean. No large or umbrella builds. All computations only supplied RunPod, scientific discriminating design, ≤50s internal/60s external, multicore, download results; no computations needed for current deductive work. Spaces after ≤ and < avoid Matroid token capture; write ((M/p:ℕ):ℝ), not (M/p:ℝ), which means real division. At let-bound goal use dsimp only before intro. Nat.ceil_le.mpr and Nat.le_ceil verified in this toolchain.