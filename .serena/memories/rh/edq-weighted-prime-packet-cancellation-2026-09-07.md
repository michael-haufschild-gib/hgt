# EDQ weighted prime-packet cancellation — complete bridge, RH open
Full chain: Euler deletion → exact complex zero balance → signed arithmetic separation → off-line exclusion → RH.
Persistent goal ACTIVE; no unconditional RH proof/falsification. This turn made verified progress; do not mark goal complete/blocked. No numerical experiments (deductions already predicted by paper reasoning).

## New audited leaf
formal/GaloisForLFunctions/RHTower/EulerDeletionWeightedPrimeCancellation.lean
265 lines, imports EulerDeletionPeriodAveragingObstruction, namespace RHTower.DeletionPrimePacket, autoImplicit false. 2 definitions, 11 public theorems.
- packet N = sum p in DeletionPeriodGrowth.upperPrimes N of bdGen(1/p).
- remainder N = bdMobiusModularApproximantVec N - packet N.
- remainder_eq_remaining_sum: remainder is EXACT actual negative-Möbius generator combination on Icc 1 N minus upperPrimes N. No arbitrary replacement coefficients.
- gram_lower_of_common_head: positive m,n and K<m,n give bdGram(1/m,1/n) >= K/(2mn), by first K genuine discrete Gram summands and positivity of full remaining tail.
- packet_norm_sq_lower: norm(packet)^2 >= floor(N/2)/2 * (sum upper primes 1/p)^2, all N.
- upperPrime_card_eventually_lower: card upperPrimes >= N/(32768 log N), unconditional eventual. Re-derives from public primeShellCard_bounds and Sieve.exists_theta_window_lower alpha=3/4; old private helper proof copied into new private helpers rather than altering old leaf.
- packet_norm_sq_eventually_lower: norm(packet N)^2 >= N/(8*32768^2*(log N)^2), eventual.
- packet_norm_eventually_pos.
- source_relative_energy_log_pow_tendsto_zero q: norm(rawVec N)^2*(log N)^q/norm(packet N)^2→0, every fixed q, unconditionally, using full-source saving at q+2.
- source_relative_norm_tendsto_zero: norm(rawVec)/norm(packet)→0.
- remainder_relative_norm_tendsto_one: norm(remainder)/norm(packet)→1.
- packet_remainder_inner_div_energy_tendsto_neg_one: Re inner(packet,remainder)/norm(packet)^2→-1.
- packet_remainder_normalized_inner_tendsto_neg_one: Re inner(packet,remainder)/(norm(packet)*norm(remainder))→-1.

## Mathematical meaning and next frontier
Upper-half primes are orthogonal under uniform period covariance (previous turn), but strongly reinforce one another in ACTUAL weighted carrier. Their actual Möbius complement cancels their growing packet; asymptotically equal magnitudes and opposite directions already hold unconditionally. All fixed logarithmic orders of relative squared residual saving also already hold. This does NOT yield absolute cofinal polynomial-log source norm/current/cross ceiling: multiplying relative residual by growing packet energy retains the cutoff factor. Next work must produce more precise absolute cancellation, retain actual weighting and all tail, and avoid presenting relative alignment as RH closure. No new primary conjecture introduced, no new route retired; this is [BRIDGE].

## Documentation
Moved new card from 1-in-progress to docs/drafts/pipeline/3-formalized/edq-weighted-prime-packet-cancellation.md.
Dependency-closed paper proof, corpus basis/scientific-method classification, full final Lean validation; no pending markers.
Frontier updated current state ONLY: top summary line44, paragraph after period-averaging obstruction, EDQ row. No new route labels/history.
STATUS appended route-independent MUST-CONTROL-CANCELLATION-AT-THE-ABSOLUTE-SCALE: track growth and relative precision together; angular alignment/norm ratios cannot replace absolute energy control; exact product scale required. Card links valid.

## Validation complete — do NOT repeat old/new audits without new changes
- All scratch Lean passed, final /tmp/edq_packet.scratch.log empty; terminal session69911 exit0.
- Final targeted LEAN_NUM_THREADS=1 lake build --old GaloisForLFunctions.RHTower.EulerDeletionWeightedPrimeCancellation session55597 exit0, ONLY new leaf Built,22s (13614 graph jobs mostly cached/replay).
- New-only axioms session67258 exit0: all13 public declarations EXACT propext,Classical.choice,Quot.sound; private helpers transitively covered. No sorryAx/admission/added axiom/computation certificate.
- Umbrella import wired once into RHTower.lean, NO umbrella/full builds.
- ONE formal lint session7958 exit0, formal lint passed (large-file warnings only).
- ONE search-index exit0,6 changed0removed;33088files403749decl3952gaps.
- Scoped checks passed exact scratch/source match, declaration coverage, forbidden token scan, unique umbrella import, docs links/stage, whitespace.
- All owned Lean/lake processes exited; removed /tmp/edq_packet.lean, /tmp/edq_packet_api.lean, /tmp/edq_packet_axioms.lean. Logs retained /tmp/edq_packet.{scratch,api,build,axioms,lint,index}.log.
- Preserve concurrent work: CCM/HTGeometry/lag/ConstrainedWeil etc present; no commits/push.

## Useful exact APIs/lessons
sum_le_hasSum (Finset.range K) (fun j _ => nonneg) genuineHasSum.
Finset.sum_sdiff needs hsub explicitly typed upperPrimes N ⊆ Icc1N before rewrite; raw filter expression does not rw with folded packet sum.
inner_self_eq_norm_sq is REAL PART theorem; inner_self_eq_norm_sq_to_K is complex equality.
tendsto_iff_norm_sub_tendsto_zero states norm(f-b)→0.
eventually_gt_nhds (0<1) supplies eventual 0<f for f→1; eventually_lt_nhds is the opposite direction.
Real.sqrt_div (sq_nonneg _) then Real.sqrt_sq (norm_nonneg _) handles relative norm, no denominator-positive premise for this identity.
field_simp sometimes leaves additive ring goal (inner minus norm² minus negative norm²); use ring after.
Do not put formal/ prefix in commands whose workdir is already formal.
Process ownership: parse ps args basename lean/lake plus exact owned path/module; PPID shared, comm truncates full paths. Never kill foreign processes.
