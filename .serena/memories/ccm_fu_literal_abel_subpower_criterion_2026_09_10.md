# Exact literal Abel subpower criterion — formalized

Active goal remains unconditional RH via CCM-FU; RH is NOT solved. Frontier map remained READ ONLY. No numerical experiment, no umbrella/dependency rebuild, no commit/push.

## New verified leaf
`formal/GaloisForLFunctions/RHTower/CCMFUSuzukiMobiusDivisorAbelSubpower.lean`, 131 lines, namespace `RHTower`, umbrella import at RHTower.lean near existing producer.
- `MobiusDivisorSquareRootAbelSubpower := ∀ ε>0, ∃ C≥0, ∀ M≥2, |mobiusDivisorSquareRootAbelMoment M / M| ≤ C*M^ε`.
- `abs_resolvent_log_nat_le_mobiusDivisorSquareRootAbel`: |R(log M)| ≤ 2|S(M)/M| + 2(|2γ|+1), M≥2.
- `riemannHypothesis_iff_mobiusDivisorSquareRootAbelSubpower`: unconditional closed equivalence. Does NOT prove either side.
- private source_power_bound_implies_zero_width: α in [0,1/2), actual normalized S power bound ⇒ XiZeroHalfPlaneBound α.

Chain: exact S=A+2γ(√M−1), charge=(A+L)/M=R(log M)/2, |L|≤√M. Existing arbitrary-exponent integer-log interpolation in SuzukiTransitionCoreFiniteContactWidthClassification → CCMCriticalMellinResolventExponentialWidth → XiZeroHalfPlaneBound at min(ε,1/4) → zero-width RH via XiHedenmalmKummerRootRH. No need to generalize SquareRootAbelDirichletContinuation.

Scratch passed lake env lean. Exact leaf lake build passed (206s, three Lake jobs, only one Lean leaf compiler). Temporary package used empty-glob stubs and cached build dirs (ClassFieldTheory .lake/build/default; Cli cache absent but unused). Initial missing-stub-manifest configuration warnings; no Lean proof warning. Source hash 20325a00d0fc08d5b26a88a0fbfd6dd69e204f3eea17c5cdca4a3b04732a1bfe; scratch/installed/audit identical. Fresh .olean/.ilean copied and hash-verified into formal cache. New public axioms only propext, Classical.choice, Quot.sound. Index and lint passed (existing large-file warnings). Do not rerun these audits without edits.

## Documentation
`docs/drafts/pipeline/3-formalized/ccm-fu-abel-subpower-criterion.md`, sibling directory has three raw deep-search JSONs, validation.txt, axioms.txt. Updated old cancellation-search report to point to this now-closed receiver. Added route-independent MUST-KEEP-GROWTH-QUANTIFIERS to universal STATUS.

## Searches / actual-bound attempt
1 continuation mechanism broad deep OR 180s: 117562 matches/27818 modules, 18 declarations/candidates/source arguments; no ideas/ingredients; deadline interruptions, ranking timeout; semantic incomplete and compiler pending.
2 single-concept subpower deep 120s: 61.27s actual, 357 matches/122 modules, 20/20/20, 0 ideas/1 ingredient set. No runtime errors; semantic partial 2168425/2331276; 43712 compiler pending/43 stale snapshots. Proposed ingredient set only relates other RH-equivalent bounds and produces no arithmetic estimate.
3 bootstrap contraction deep OR 120s:1661/582,20/20/20,0 ideas/ingredients, malformed/incomplete judge JSON and retrieval deadline interruptions. All sections inspected.

Source applicability: Bourgain power-scale iterate still assumes actual recurrence; weighted parabola fiber estimates not identified with pointwise divisor source. Abstract discrete energy bootstrap still needs actual drift/primitive/control bounds. Concrete direct Erdos–Selberg test: m_window_contraction_of_ratio requires δ≤a,40/δ+2<logQ,8Q≤c,c*x1≤N,x1≥8. Thus Q≤N and 40<a*logN. Cannot directly set a=N^(-1/2+ε) once a logN≤40. This is an applicability failure for that substitution, not a no-go for all bootstraps. Underlying abs_psiRemainder_recursion has signed forcing bounded by400N; taking absolute errors through sqrt-Abel leaves a power-sized forcing. A useful new attempt must control that forcing jointly with the signed recursion, or establish a genuine subpower recurrence for S/M.

## Next work
The exact all-ε receiver gap recorded in mem:ccm_fu_deep_search_cancellation_2026_09_10 is CLOSED. Arithmetic |S/M|≤Cε M^ε for allε remains open. Allow subpower losses when attacking source cancellation, but do not silently subtract harmonic quadratic terms or discard later tails. No new computation justified. Old gcd-prefix experiment is CANCELLED as in mem:ccm_fu_gcd_prefix_budget_pending_2026_09_10; archived N=1024 evidence already violates its frozen budget. RunPod endpoint previously refused; user was asked once, no repeat required for canceled experiment.

All owned Lean/search/index/lint handles completed. Temporary /tmp/ccm-abel-subpower-20260910 tree and /tmp/ccm-abel-subpower-search-20260910.json scheduled for immediate cleanup after this memory write; archived evidence retained. Goal ACTIVE, not blocked.