# Replica depth/radius proof optimization — 2026-09-28

Latest user request was **optimize Lean code, no raising heartbeats**. Completed bounded proof-maintenance task; NO mathematical frontier advance claimed. Brown–Susskind research goal remains active/unsolved, especially complete-circuit incidence-action producer.

Changed only two existing leaves, statements/imports unchanged:
- formal/GaloisForLFunctions/HTGeometry/TwoLocalPauliReplicaJetDepthLaw.lean:154 pauliReplica_logarithmic_jet_detection — replace finite-set ext/congr and subtraction arithmetic with Finset.card_subtype, Finset.filter_ne', Finset.card_erase_add_one. :248 pauliOrderedReplica_uniform_logarithmic_jet_detection — use le_mul_of_one_le_left/one_le_pow₀ for power lower bound instead of linarith.
- formal/GaloisForLFunctions/HTGeometry/TwoLocalPauliReplicaJetRadiusLaw.lean:71 private detectorJet_uniform_linear_variation — explicit f/g arguments to DifferentiableAt.comp avoid expensive metavariable/typeclass inference. :163 pauliOrderedReplica_inverse_height_jet_detection — explicit positivity witnesses, le_add inequalities, direct mul_le_mul replacing gcongr, restrict final linarith to its three relevant facts.

Measured native profiler Elab.definition.value raw heartbeat counters, same combined source scratch and options both runs:
pauliReplica_logarithmic_jet_detection 3,597,428 -> 3,316,583 (-7.81%)
pauliOrderedReplica_uniform_logarithmic_jet_detection 5,687,670 -> 5,144,194 (-9.56%)
detectorJet_uniform_linear_variation 8,220,012 -> 6,444,794 (-21.60%)
pauliOrderedReplica_inverse_height_jet_detection 14,099,319 -> 5,942,338 (-57.85%)
Total four proof bodies31,604,429 ->20,847,909 (-34.03%). Not whole-project or wall-clock speedup. Main old gcongr alone5,390,858; differentiability inference improved by explicit function arguments.

Verification:
- Baseline combined source passed session79326. Optimized combined source passed16402, including mathlib name checks.
- Final combined source + four changed proofs #print axioms passed93818 exit0, no warnings/errors. All four axioms only [propext,Classical.choice,Quot.sound].
- Combined scratch uses full depth source followed by radius source with its now-redundant import omitted; does not silently rely on cached depth proof. External cached imports unchanged. Repository sources byte-identical to checked component strings. All13 theorem signatures (8+5, including privates) byte-identical. Exhaustive rg references only these two leaves. Existing HTGeometry umbrella imports11683–4 confirmed unchanged.
- No new/updated oleans, no full/umbrella builds, no git, no agents. Elab.async=false only in measurement/audit scratch. Used -Dtrace.profiler=true -Dtrace.profiler.useHeartbeats=true -Dtrace.profiler.threshold=1000000; threshold only controls log filtering. NO maxHeartbeats/maxRecDepth changes or disabled limits.
- Custom hybrid corpus search before edits: partial, semantic_coverage_unavailable, candidate/source method data inspected, verified source directly. Serena Lean symbols unavailable (active language Python), used rg/read/apply_patch fallback. L7 skill fully read and all three planning phases delivered before edits.
- Global lint76491 exit1:20 unrelated unwired leaves, no failures in edited modules; unrelated file-size warnings. Do NOT claim global lint green. Leave other agents' modules untouched.
- All owned Lean/search/lint sessions terminal. Temporary /tmp/hgt-replica-opt.ktLkUA files scheduled for explicit cleanup immediately after this memory write.

Original theorem content remains mem:quantum_recurrence/replica_logarithmic_jets_inverse_height_radius_2026_09_28. This turn does not resolve the return-excised action estimate or residual target-span scaling issue raised in earlier research.