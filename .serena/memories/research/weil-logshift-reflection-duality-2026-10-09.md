# Reflection duality and all-probe lower-bound no-go

OUR LEAN CORPUS ONLY. No web or external papers. Goal active; last increment verified progress.

New leaf formal/GaloisForLFunctions/RHTower/WeilLogShiftReflection.lean imports WeilLogShiftLocalExcessDomain.
Positive card docs/drafts/pipeline/3-formalized/weil-logshift-reflection-duality.md.
Closed failed-route card docs/drafts/pipeline/5-failed/weil-logshift-lower-bounds-alone-no-go.md records BOTH counterexample and formalized positive survivor.

Define weilCoefficientReflection lam n=2*vonMangoldt(n)-lam(n). It is an involution; normalized deviation negates including n=0,1; positive excess/deficit exchange. Every truncated potential negates. Exact unconditional identity: Q_lam(L,c)+Q_reflected(L,c)=2*W(L,c). Since W(L,log m)->0, local-excess minus-infinity divergence dualizes to local-deficit plus-infinity divergence.

For EVERY m>=2, finite local deficit moment plus nonsummable signed sample forces actual real-cutoff probe -> plus infinity. Exact new criterion: signed sample Summable iff local deficit moment Summable AND eventual upper bound on integer-cutoff probe. This is dual to preceding excess+lower-bound criterion. No unweighted/global moment assumption.

Explicit obstruction: lam(n)=Lambda(n)+sqrt(n)*exp(2*pi*n) majorizes Lambda and has identically zero deficit. For EVERY m>=2 its sampled signed potential is nonsummable, yet actual real-cutoff Q_m->plus infinity and eventually Q_m(k)>=0. Thus even lower bounds at ALL nontrivial probes cannot imply convergence when excess moment control is removed. General exponential_majorant_logShift_probe_atTop proves same +infinity for rho>2*pi/m. No claim at critical equality.

11 public declarations (1 def+10 theorems): weilCoefficientReflection; weilCoefficientReflection_involutive; weilDeviation_reflection; deviationExcess_reflection; deviationDeficit_reflection; truncatedDeviationPotential_reflection; logShift_probe_reflection_sum; tendsto_logShift_probe_atTop_of_nonsummable_sample_of_local_deficit; summable_potential_iff_local_deficit_and_probe_upper_bound; exponential_majorant_logShift_probe_atTop; exists_majorant_all_logShift_probes_atTop_not_summable.

Verification: leaf lake --old env lean ... -o local olean exit0/no diagnostics. All11 scratch #print axioms only propext/Classical.choice/Quot.sound. Umbrella wired, index refresh succeeded,all11 API rows inspected,scoped diff-check passed. GLOBAL LINT FAILED on three unrelated unreachable modules: RHTower.PaperCircleSplitCharacterPosterior, HTGeometry.DiscreteCrossedProductCStar, HTGeometry.PrimeTranslationModularFlow. Prior CCMRestrictedWeilCrossFormBound error no longer appears. Do not edit unrelated sources/imports or rerun without state change. All owned jobs terminal; eight /tmp/hgt-weil-probe-reflection scratch files removed. No new analytic inputs/axioms, computations/numerical experiments, heartbeat changes, full builds, commits or subagents.

Remaining boundary: both local excess and deficit moments divergent. Current one-sided classifications make no claim about resulting behavior and do not produce bounded probes with nonsummable potential. Any conjecture there needs fresh corpus/paper audit. Also critical growth equality remains open; uniform positivity receiver still uses global finite excess (not discharged by these domain results).

Prior memory: mem:research/weil-logshift-local-excess-domain-2026-10-09. Tool output improvement: read_memory results contain duplicate text/content and structuredContent; print only structuredContent.result when possible. Never zsh variable path (alters PATH); use task_doc. update_plan unavailable; plans in cards.
