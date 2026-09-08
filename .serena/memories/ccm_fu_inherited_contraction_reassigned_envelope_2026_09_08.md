# CCM-FU: matching contraction fails, different successor supplies repaired envelope

Goal ACTIVE: unconditional formal RH proof/falsification not achieved. Previous goal turn classified PROGRESS (new boundary-greedy evidence); this turn adds a new discriminating experiment and 3 closed Lean declarations. User frontier map READ ONLY; no edits by this agent. No STATUS entry: no new route-independent RH law. No subagents, commits or pushes. Preserve all external worktree changes.

## New closed theorem and exact mathematical result

formal/GaloisForLFunctions/RHTower/MobiusDivisorSeventeenRepair.lean:251 `mobiusDivisorSeventeen_repair_certificate` is a closed conjunction. M=17, P={3,5,7}, S=P+11, E=S+2, B=Q_empty:
1. Psi(P)+1/20<=B.
2. B+1/200<=Psi(S).
3. 2 uniquely minimizes immediate energy among every available prime at S (only2,13).
4. Psi(E)+1/200<=Q_S.
5. Q_P+1/100<=Q_E.
6. Q_(P+13)+1/50<=Q_(E+13).

This refutes inherited matching-energy contraction of a prescribed repair pair even at an actual forced exit from admission. Strong positive survivor: both repaired branches lie below a DIFFERENT parent successor Q_S, already included in Psi(P). Thus Psi(E)<Psi(P) despite both matching energy increases. Do not infer from the negative comparison that full-envelope contraction fails or that no reassignment is possible. No general repair theorem, exhaustive order, or RH proof follows from this one actual cutoff.

Literal full source at P has exactly coordinates empty,{2},{11},{13}:
a=K1-K3-K5-K7+K15; b=-K2+K6+K10+K14; c=-K11; d=-K13.
Analytic boxes a[-.402,-.401],b[.076,.078],c[-.125,-.124],d[-.080,-.079],B[.360,.365]. Actual nonsquarefree and terminal source channels vanish. Every source label, alternative, and endpoint retained.

Two new declarations appended to existing DivisorTwentyTwoAnalyticBounds.lean, reusing its private analytic machinery (not copying its tables):
:397 divisorUnsignedDilationChannel_seventeen_profile_boxes
:434 sum_divisorUnsignedDilationChannel_seventeen_sq_bounds
Header now covers17and22. The bounds come from original logarithm series, harmonic Euler-constant correction, rational sqrt sandwiches and signed interval products. Experiment values are guidance only, no numerical premise.

## Validation completed; do not repeat

Both phases checked in /tmp with lake env lean. Then exact files emitted with lake env lean <path> -o .lake/build/lib/lean/<path>.olean, sequential foreground processes. New leaf imported by RHTower.lean:1521. Audit of ONLY these 3 new declarations reports [propext,Classical.choice,Quot.sound]. No computational axiom/sorry. Index refreshed. scripts/formal_tools.py lint --check-generated ultimately passed with existing large-file warnings. It was rerun only after an external new SelbergCuspHardyBoundary import fixed the first wiring failure and a subsequent index refresh fixed stale generated files. Do not re-audit older declarations. No large or umbrella builds.

Known lake build packaging audit remains pending because it expands broad stale prerequisite graph; do not retry broad preflight/build. Exact kernel checks are not Lake packaging completion. All scratch files (/tmp/ccm_seventeen_bounds_addition.lean, ccm_seventeen_bounds.lean, ccm_seventeen_repair.lean, ccm_seventeen_audit.lean, ccm_seventeen_lint.log) removed. New needed oleans retained. All owned Lean/exec sessions terminal, including finalemit5560,audit79383,index83608,lint53714/87947/83990; owned process scan empty.

## Discriminating experiment

Frozen inherited-contraction mechanism: at each saved admitted P forced r exiting admission, choose established immediate-energy minimizer q and ask Q_(P+r+q+T)<=Q_(P+T) for T empty or any available singleton other than r,q. Distinct question from prior repair underB. Reused all previous boundary cases+full original CSV through32, no range extension.

8805 comparisons,1083 positive increases. Failing cutoffs17,19,23,25,27,28,29,30,31,32. All flagged positive increases reconstructed and confirmed at80 digits from defining Mobius/divisor/Abel source, every alternative/order and all relevant successor fields retained. First M17,Pmask14={3,5,7},forced11,repair2. B=.36217844460095..., PsiP=.28896785677857...,PsiS=.37305158820797...,PsiE=.27998699043534..., matching gains .01921164958134... and .02684486136853.... Numerical evidence not a Lean certificate; the first witness is independently proved as above.

Artifacts docs/drafts/pipeline/2-fully-proven/computations/ccm-fu-repair-inherited-contraction-2026-09-08/{screen.py,summary.json,README.md}. Script sha cc0a3b53bc678ac0eb7bdbaf1dee8fab2483923b8e73f85dc03238ca08ef1e1d; output sha3c4602d35db5729e29302df7005c80b9c7cb93d9eb4eeaa127eae2c05adeb57a. Inputs previous boundary output hash4cdaf037... and CSVba22442.... Local/remote hashes match.

RunPod only supplied ssh root@157.157.221.29 -p27094 -i ~/.ssh/id_ed25519. Eight cutoff workers, one-thread BLAS, internal50s/external60s deadlines, full run0.10968971997499466s including80-digit audit. First attempt exited with Python3.8 int.bit_count unavailable; fixed current script to bin(mask).count('1'), same inputs/question/precision, completed rerun. Historical previous frozen script has same untriggered audit-branch compatibility issue; don't reuse bit_count on this host. No math computation locally.

Remote directory /tmp/ccm-inherited-repair-ZF8Leu and exactly4files screen.py,subset-states.csv,boundary.json,summary.json removed after download. No worker remained. All SSH/SCP sessions terminal. No larger or repeated experiment scheduled.

## Documentation

Stage3 docs/drafts/pipeline/3-formalized/ccm-fu-seventeen-repair-envelope.md contains exact proof and validation/scope.
Frozen mechanism card moved from1-in-progress to docs/drafts/pipeline/5-failed/ccm-fu-repair-inherited-contraction.md after both negative claim and stronger positive survivor checked. Computation link updated. This retires ONLY matching contraction, not greedy repair or CCM-FU.
Updated docs/drafts/pipeline/1-in-progress/ccm-fu-greedy-forced-prime-repair.md: comparison with a separately successful repair is sufficient, not necessary; different admitted parent successors can supply bound. General uniform control remains open.

## Remaining mathematical attack

Need actual-source simultaneous repaired-envelope comparison for arbitrary changing core, overlapping primes, allcutoffs; finite point cannot establish it. New source witness suggests comparing every repaired branch to a possibly different admitted parent successor, rather than requiring each to contract its matching original energy. Stronger Psi(P+r+q)<=Q_(P+r) holds at17 but is NOT established generally or across saved cases; do not silently assume it. No experiment on this stronger full-envelope comparison has been frozen or run.

Fixed-core renewal/correlation reread this turn: W_(P+p)(Y)=(1+1/p)W_P(Y)-sqrtp/p² W_P(pY)-sqrtp W_P(Y/p). Core-energy Hilbert/autocorrelation bounds considered but no new result implemented. Do not substitute more fixed-core asymptotics or generic receiver lemmas for changing-core source selection.

Serena find_symbol for the analytic Lean file returned ignored path; used read-first text edits as fallback. Source lexer can consume <=s or <=m as graph notations; use spaces. Explicit change needed before linarith to align literal core with private definition repairCore. Existing source_profile simp closed b case; extra ring caused no-goals. All repaired and exact checked.