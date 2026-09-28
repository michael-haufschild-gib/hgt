# Weighted sublevel proof optimization — 2026-09-28

Latest explicit user request: optimize Lean code, no raising heartbeats hacks. Completed optimization only; not new mathematics and does NOT close Brown–Susskind/coarea goal.

Changed only formal/GaloisForLFunctions/HTGeometry/TwoLocalPauliWeightedSublevelLaw.lean:
- private pauli_character_near_measure_le (:81): zero-character case uses explicit simp only list instead of unrestricted simp.
- pauliWeightedNearMass_quenched (:118): intersection indicator equality uses Set.indicator_indicator + congrFun + indicator_of_mem instead of repeated cases.
- pauliWeightedNearMass_quenched_envelope (:153): intersection indicator and indicator_le_indicator replace cases.
A proposed replacement inside weighted_indicator_outer_tail measured no improvement (1182926 ->1184101 raw heartbeat counter), so REVERTED before integration.

Per-declaration native-profiler raw heartbeat counts (before -> final):
pauli_character_near_measure_le: 3259748 ->2050207 (~37.1% less)
pauliWeightedNearMass_quenched:1508570 ->1379471 (~8.6% less)
pauliWeightedNearMass_quenched_envelope:1408742 ->1255779 (~10.9% less)
Combined ~24.15% less elaboration-allocation work for these3 declarations, NOT whole-project/wall-clock speedup.
Unchanged helper baseline/final precisely1182926; profiling stable.

Checks: lake env lean scratch baseline, candidate and final all exit0; same cached dependencies; no umbrella/full/module builds, no oleans generated. Native flags -DElab.async=false -Dtrace.profiler=true -Dtrace.profiler.useHeartbeats=true -Dtrace.profiler.threshold=1000000. Profiling filter only; no resource limits raised or disabled. All10 declaration statements byte-identical before/after. Final repository source byte-identical to checked scratch body. All3 changed proofs #print axioms exactly [propext,Classical.choice,Quot.sound]. Exact caller search: only intra-leaf theorem consumers and HTGeometry umbrella import at11684; existing wiring sufficient. No git or subagents. L7 skill review rejected unmeasured change.
Formal lint exit1: 19 unrelated RHTower modules unreachable from umbrella (CCM, Chebyshev short-window, Moebius mollified, PrimeShortIntervalsFiveEighths, XiZero short-weight/height, ZetaZeroDensityPowerSaving); no errors in modified leaf. Existing large-file warnings also unrelated. Do not claim global lint passed.
Custom hybrid weighted-sublevel search succeeded with source-only compiler coverage; deep indicator-method search partial with reranking deadline. Actual mathlib indicator APIs verified in candidate scratch.
All owned Lean/search/lint sessions terminal. Scratch /tmp/hgt-weighted-opt.5kUEud and3 temporary Lean files deleted. No owned stale processes. Previous8-proof performance pass remains in mem:quantum_recurrence/pauli_jet_proof_performance_no_limit_changes_2026_09_28.

RESEARCH HANDOFF, NOT VERIFIED:
Before this optimization request interrupted research, /tmp/hgt-replica-depth.lrH8Zo/ReplicaDepth.lean was developing a logarithmic-in-replica star-to-full-Pauli jet detector. Preserved, not deleted or integrated. Its session36307 was polled and finished exit1; only remaining error line91: Int.natAbs_pow leaves Int.natAbs 2 instead of2 because Int.natAbs_natCast does not simplify numeral2. Likely fix use explicit (show (2:ℤ).natAbs=2 from rfl) in simp list. All other original draft errors disappeared in that check. Do NOT claim theorem verified yet.
Draft chain: minimal nonzero integer Walsh coefficient at degree d divisible by2^d via exact subcube marginal identity; order-r replica character coefficients ≤2r; balance gives nonemptyB; choose i∈B, S=B\\{i}; 2^|S|≤r, actual full-Pauli derivative order≤min(n+1, Nat.log2r+2), magnitude≥2^(|S|+1). Main pauliReplica_logarithmic_jet_detection explicitly retains zero-character alternative. Combinatorial trade minimum-mass mechanism KNOWN: arxiv1810.02296, not our novelty. Still no growing-replica coarea bound, no source-chart uniform radius/typical-global ensemble bound, no continuous first-circuit-return exclusion. If continuing, first read draft and current source; custom search precedes new code.
