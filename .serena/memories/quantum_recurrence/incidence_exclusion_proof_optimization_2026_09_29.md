Latest user request: optimize Lean code, no raising heartbeats. Completed bounded optimization; not scientific frontier advance. Persistent Brown–Susskind same-draw goal remains unsolved.

Changed four proof bodies only, all statements/imports unchanged:
- formal/GaloisForLFunctions/HTGeometry/PauliReturnExcisedCircuitContinuumLaw.lean:63 stdGaussian_twoLocalPauli_measure_returnExcisedCircuitPolynomialWindowReturnEvent_le: replace two nlinarith calls with mul_le_mul_of_nonpos_left using div_nonneg/sq_nonneg; replace gcongr with mul_le_mul_of_nonneg_right, explicit Nat.cast_le; replace ring calc with mul_assoc-only simp and order lemma; restrict constant-sum simp.
- formal/GaloisForLFunctions/HTGeometry/PauliAllTimeCircuitExclusionLaw.lean:101 stdGaussian_twoLocalPauli_measure_returnExcisedCircuitAllTimeReturnEvent_le: restrict constant-sum simp only.
- Same leaf:193 incidence ceiling: restrict final sum-of-ones simplification.
- Same leaf:223 certificate floor: restrict constant-sum simplification.

Profiler revealed broad simp tried costly failed typeclass searches for IsEmpty/Nonempty and group/semiring structures on unitary endpoint subtypes. Restricting to Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc/mul_one removes those searches.
Same combined-source scratch (full continuum followed by all-time minus redundant import), set_option Elab.async false only scratch, CLI trace.profiler true / useHeartbeats true / threshold 1000000 (log filter only). Default proof limits unchanged:
continuum Elab.definition.value 51,509,745 -> 4,703,540
all-time return-excised 36,505,575 -> 3,085,771
total dominant two88,015,320 ->7,789,311 (-91.2%)
incidence ceiling5,271,834 ->1,144,590
certificate floor6,268,558 ->below1,000,000 trace filter, do NOT report an exact optimized floor count.
These are raw proof-elaboration profiler ticks, NOT project wall-clock speedup.
Intermediate candidate passed; final profile session99046 exit0. Final integrated sources exactly matched measured combined scratch. All original theorem/definition signatures checked unchanged. Final combined scratch audit74100 exit0 no warnings; exactly four changed proofs #print axioms all [propext, Classical.choice, Quot.sound]. Existing umbrella imports11771–2 unchanged, no new oleans/builds needed, no full/umbrella builds, no git, no subagents. Custom corpus hybrid/any search before edits partial, coverage_snapshot_older_generation and semantic_coverage_unavailable; direct source used as authority. L7 skill fully read, three planning phases delivered before edits. Exact hgt-fields-medalist file unavailable; backup hgtl7 research protocol read earlier this turn but this optimization pass does not claim research novelty.
Global lint18722 exit1 due15 unrelated unwired RHTower modules; no edited-leaf proof debt/wiring errors. Do not change other agents' WIP.
Working log docs/reports/quantum-recurrence-working-log.md updated. Owned search94489, baseline11183, candidate12033, profile99046, audit74100, lint18722 all terminal. All /tmp/hgt-incidence-opt.5n1LiX files to be deleted immediately after memory write and directory removed. Never kill unrelated Lean processes.