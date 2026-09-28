# Pauli spectral-jet proof optimization — 2026-09-28

User asked optimization, explicitly no heartbeat hacks. Eight existing proofs optimized in THREE existing leaves; no mathematics/theorem statements strengthened, no new theorems, no hypotheses added. Goal remains ACTIVE/UNSOLVED; decisive complete-circuit incidence-action inequality still missing. This is a proof-maintenance turn, not a scientific breakthrough.

Changed files (formal/GaloisForLFunctions/HTGeometry):
- TwoLocalStarSpectralJetFrame.lean:68 sum_sq_realStarWalshPacket uses congrArg scaling + exact inverse cancellation instead of field_simp/nlinarith. :164 one_le_abs_commonReferenceStarJetAmplifier uses one_le_inv₀ and one_le_mul_of_one_le_of_one_le. :217 commonReferenceSpectralJet_parseval restricts simp to sum_add_distrib, Fintype.sum_ite_eq', card_fin. :262 balanced_real_character_commonBase_starJet_detection restricts card_subtype simplification and uses le_mul_of_one_le_left instead of nlinarith.
- TwoLocalPauliSpectralJetLaw.lean:198 starPauliDirectionMap_apply uses congrArg₂ instead of generic congr (avoids failed definitional equality unfolding entire finite sum). :228 commonReferenceStarMatrix_eq_pauli uses fixed entrywise simp set instead of global simp in four blocks. :357 balanced_real_character_fullPauli_jet_detection uses exact list-length simp set.
- TwoLocalPauliSpectralSublevelLaw.lean:276 pauliBalancedIntegerAction_uniform_smallBall uses Int.one_le_abs (cast to real), replacing integer sign cases + omega + linarith.
WeightedSublevel leaf and CommonSpectralChart leaf UNCHANGED. Existing umbrella wiring confirmed, no edits needed.

Measured per-declaration native-profiler heartbeats, raw counter divided by1000 (approx):
sum_sq_realStarWalshPacket: 3308.2 -> 939.8 (-71.6%)
one_le_abs_commonReferenceStarJetAmplifier:3483.9 ->1411.1 (-59.5%)
commonReferenceSpectralJet_parseval:3463.0 ->779.8 (-77.5%)
balanced_real_character_commonBase_starJet_detection:11177.5 ->1495.4 (-86.6%)
starPauliDirectionMap_apply:5487.5 ->1057.2 (-80.7%)
commonReferenceStarMatrix_eq_pauli:18881.7 ->8896.8 (-52.9%)
balanced_real_character_fullPauli_jet_detection:3212.9 ->822.6 (-74.4%)
pauliBalancedIntegerAction_uniform_smallBall:6982.4 ->5777.0 (-17.3%)
Total55997.1 ->21179.7 (~62.2% less). These are elaboration-allocation measurements, NOT whole-project/wall-clock speedups. Imports dominate and concurrent unrelated processes made import times33–141s. Before/after profiles differ in thresholds500k–2M raw (filter only); stable unchanged declarations show small counter variation. Reverted smoothness rewrite (<1% improvement).

Validation: scratch leaf + bounded scratch source integration (StarFrame -> unchanged CommonSpectralChart -> PauliJet -> Sublevel -> unchanged WeightedSublevel), only cached external dependencies; lake env lean exit0, no warnings/errors. All8 changed public theorem statements checked byte-identical. All8 #print axioms only [propext,Classical.choice,Quot.sound]. No resource limits changed or disabled: native -Dtrace.profiler=true -Dtrace.profiler.useHeartbeats=true used; Elab.async=false only in measurement scratch. Avoid #count_heartbeats wrappers because THIS toolchain wrapper temporarily sets maxHeartbeats0. No computations as proofs, no new axioms, no new oleans, no full/umbrella builds, no git/subagents. Repository edited files byte-identical to checked scratch copies. Exhaustive rg callers inspected; extra uniform-star consumer uses unchanged Parseval signature.

Scoped antagonist verdict PASS: all8 proof costs improved, statements unchanged, closed checks; no global performance certification. Formal lint exit1 with25 unrelated unwired modules (RHTower CCM/short-window/Moebius/zero-density routes; HTGeometry AbelianZetaGas socle routes), none in changed leaves. Do NOT claim global lint passed or modify other agents' modules. All owned Lean/search/lint handles terminal. Scratch /tmp/hgt-lean-opt.ny5kna and temporary logs/task_state_20260928_205121.md to be removed after this memory write.

Prior research remains in mem:quantum_recurrence/countable_weighted_pauli_quenched_sublevel_2026_09_28. Unproved next idea from prior turn: minimal-support nonzero integer Walsh coefficient is divisible by2^degree if all lower subsets vanish; replica l1≤2r then forces detector order≤2+floor(log2r). Existing star-to-full-Pauli jet identity could transfer this. Generic combinatorial minimum-volume Boolean-trade bound KNOWN (arxiv1810.02296 /1811.00015), not novel; never claim invented. Not formalized this optimization turn. Does not close coarea/first-return bound.