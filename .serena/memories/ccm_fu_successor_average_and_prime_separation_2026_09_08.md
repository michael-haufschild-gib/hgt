# CCM-FU: successor averaging refuted, persistent source separator proved

Goal remains active and unmet: unconditional RH proof/falsification via CCM-FU. Read the frontier map only; user explicitly forbids updates. Do not edit STATUS with route-specific claims. No subagents authorized. Preserve concurrent work; no commits/pushes.

## Exact new result
At M=22, P={3,7,11,17,19}, available primes exactly {2,5,13}, B=Q_empty:
- Psi(P)+1/250<=B.
- Mean_p Psi(P+p)>B+1/75, analytically certified, so universal uniform successor-average admission law is false.
- Prime 2 uniquely minimizes immediate energy.
- Every 2-free signed fibre is nonpositive and every 2-containing fibre nonnegative.
- Other mergers preserve this separation. For EVERY finite T with 2 notin T, Q_(P union T+2)<=Q_(P union T), retaining overlap.
- Therefore Psi(P+2)<=B.
Exact extension, greedy extension, SD1, PE4, uniform signed Abel bound, RH remain open. No universal separating-prime producer; cutoff-seven final increases already rule out persistent contraction everywhere.

Five actual coordinates:
a=K1-K3-K7-K11-K17-K19+K21 in[-.480,-.479];
b=-K2+K6+K14 in[.182,.183];
c=-K5+K15 in[-.127,-.126];
d=K10 in[.202,.203];
e=-K13 in[-.168,-.167].
All other fibres zero. B in[.550,.553]. QP<=.546; QP2<=.123; QP5 in[.540,.546]; QP13 in[.505,.546]; QP2,13>=.219; QP5,13>=.743. Thus sum successor envelopes>=1.705>3B+.04.

## Formal modules, checked and wired
formal/GaloisForLFunctions/RHTower/DivisorTwentyTwoAnalyticBounds.lean
formal/GaloisForLFunctions/RHTower/MobiusDivisorPrimeSeparation.lean
formal/GaloisForLFunctions/RHTower/MobiusDivisorSuccessorAverageObstruction.lean

All exact files passed lake env lean with needed oleans emitted. Main exact emit97976 exit0. All 13 new public proof declarations audited ONCE via external scratch; only propext, Classical.choice, Quot.sound. Do NOT re-audit these. Generated indexes refreshed; formal lint passed with existing file-size warnings. Three umbrella imports added, NO umbrella build. Targeted Lake packaging remains pending from earlier turns; do NOT repeat known expensive lake build --old prerequisite rebuild path. Do not claim lake build succeeded.

Main capstones RHTower:
mobiusDivisorPrimeSeparated_twentyTwo
mobiusDivisorSelectionEnergy_twentyTwo_two_persistently_contracts
mobiusDivisorSuccessorEnvelope_twentyTwo_admitted
mobiusDivisorSelectionEnergy_twentyTwo_two_unique_minimum
mobiusDivisorSuccessorEnvelope_twentyTwo_two_admitted
mobiusDivisorSuccessorEnvelope_twentyTwo_average_exceeds
not_mobiusDivisorSuccessorEnvelope_average_law
Generic exact envelope def and le_iff included in main. General sign-separation insert/union/energy theorems in PrimeSeparation.

## Documents and experiment
Failed card (moved from1-in-progress):
docs/drafts/pipeline/5-failed/ccm-fu-successor-average-reserve.md
Contains frozen question, full analytic paper proof, positive survivor, theorem list and audit limitation.
Exact-successor-extension.md and greedy-envelope-extension.md updated with result and remaining signed reserve problem. Frontier map and STATUS untouched by this turn.

Artifacts:
docs/drafts/pipeline/2-fully-proven/computations/ccm-fu-successor-average-2026-09-07/{screen.py,summary.json,README.md}
One RunPod screen, NOT to repeat: reads all8860 states through32, tests8176 admitted proper states, 262 failures all independently reconstructed/confirmed at80digits. None on saved deterministic greedy path. First M22 state above. Eight workers, one-thread numerical libraries, deadline60sec, successful elapsed0.10254687815904617sec. First Python3.8 bit_count failure corrected without changing experiment. Inputs unmodified; hashes inREADME. All owned remote files removed and no workers remained. Experiment is guidance only, no computed proof premises.
Predictably false stronger claim that greedy prime contracts after every alternative was rejected by existing cutoff-seven theorem WITHOUT experiment.

## Cleanup and practical Lean lessons
All owned Lean sessions terminal; ps confirmed no owned process. Removed ten explicit /tmp ccm_fu_successor*/ccm_fu_prime_separation scratch/log files. Needed installed oleans retained. Local markdown links/own whitespace checked.
- Always spaces in 0 <= mobius... (Unicode ≤m parses Matroid notation, yielding obius...).
- Finset.range_add_one exists; Finset.range_succ does NOT.
- Finset.sum_range_succ must be qualified; RHTower shadow can leave sums unexpanded.
- Do not put set_option between doccomment and theorem; before doccomment.
- For hc.trans hqbase with union-singleton mismatch: rewrite hc FIRST with Finset.union_singleton and explicit Finset.insert_comm 2 q. Asking simpa to elaborate hc.trans before rewriting caused needless timeout.
- Analytic bounded sums: expand finite Icc sums BEFORE unfolding term definitions. Monolithic norm_num expensive.
- norm_num only can leave Icc1 0 sums. Avoid giant diagnostics.
- pp.maxDepth unavailable.
- Source profile powerset enumeration needs powerset_insert,image_union,image_insert, then simp only[or_assoc] and cases; set equality simp uses ext_iff,iff_def,or_imp,forall_and.
No need to rerun completed verification.

## Next hard work
Full chain: actual divisor source -> simultaneous signed prime selection for growing mixed fields -> uniform signed Abel bound -> CCM-FU RH implication.
The missing comparison for admitted P remains one actual p satisfying
Delta_p+Delta_q+2*C_pq<=B-QP for EVERY alternative q.
New average counterexample forces discrimination among choices; persistent separation explains one actual failure but is not a universal solution. Next work must attack this all-cutoff arithmetic comparison (including states with reserve-paid positive gains), not launch another finite repeat or add generic conditional receivers.
Prior global unsigned envelope and small-core results remain proved; see mem:ccm_fu_global_unsigned_envelope_2026_09_07 and mem:ccm_fu_small_core_first_gains_and_greedy_envelope_2026_09_07.
