# Exact successor prediction and arithmetic phase loss (contribution010)

Verified as one connected contribution on2026-10-18. Goal count10 / 250; goal ACTIVE. Card: `docs/drafts/pipeline/3-formalized/bvi-successor-compression-and-arithmetic-phase-loss-2026-10-18.md`.

Field leaves: `CoprimalitySuccessorPredictorAndSquarefreeInformation.lean` (266lines,10named/5public), `OptimalSuccessorPredictionAndExactPhaseLoss.lean` (273lines,22named/9public), `SharpSuccessorPhaseLossAndClosureClassification.lean` (255lines,15named/9public).

For every natural N and arbitrary real weights, Kc(d)=μ(d)Σ[d|m≤N]c(m)/φ(m). Its actual signal is the weighted coprimality sum Σ[m≤N,gcd(m,k)=1]c(m)/φ(m). Its Selberg coordinates are μ(q)Y_c(q)/φ(q). The explicit raw formula uses the existing `TotientMulMoebius.totient_mul_eq` and Möbius coprimality indicator, not a renamed finite inverse.

Actual internal-factorial-cycle mean squared error obeys Err(c,b)=L(c)+Q(b-Kc), where L(c)=Σ[3≤q≤N](φ(q)-μ(q)^2/φ(q))Y_c(q)^2. K is the unique minimizer on active raw coefficients. Zero cycle error iff actual shifted signals agree for every natural input, including0.

Kc=Kb iff their squarefree Selberg coordinates agree. Exact range: zero extension outside[1,N], and zero raw coefficients on nonsquarefree divisors. All nonsquarefree spectral modes are erased; no additional range compatibility condition remains.

With W=Σ[q≥3]φ(q)Y_q², 3W/4≤L≤W. Lower equality permits exactly modes3,6 above parity; upper equality iff every squarefree coordinate above2 vanishes. Pure3 and pure4 inverse modes establish complete uniform lower/upper constant classifications. L=0 iff raw weights above2 vanish. Equivalently, the actual successor belongs to the same divisor-sieve model exactly for constant+parity responses.

Do not count generic multiplier/iteration corollaries as separate contributions. Powers of K must NOT be identified with projection of true multi-step translation; no such semigroup claim was proved. Unit averaging was not asserted. No prefix cancellation or asymptotic claim.

Three exact original-source checks passed without diagnostics using isolated cache and sequential `lake --old env lean -j 1 --root=... -o ... <original source>`. All23 public declarations (19theorems,4defs) audited in /tmp; exactly propext,Classical.choice,Quot.sound. All47 named declarations match lexical index; all23 public rows match cache/API. All3 leaves wired once and verified artifacts installed atomically. Raw axioms: `logs/bvi-root-2026-10-18-successor-prediction-axioms.txt`. Source/olean/log hashes on card.

Local deep searches: successor projection (partial reranking timeout/judge disconnect), Ramanujan compression and Möbius/totient divisor sums (complete); all returned sections inspected. Older coverage snapshots and unavailable semantic coverage disclosed. Lexical unit and projection searches fully paged. No equivalent result in returned local material; no global novelty claim.

Final lint snapshot:381 foreign large-file warnings,16 foreign umbrella omissions, no owned or proof-debt finding. During concurrent wiring, only JordanUpperBoundAndGcdOrbitPrimitiveEnergy and RenormalizedMobiusDefectAndFirstOctaveCancellation remained unwired among29 field leaves at artifact audit. Concurrent new martingale, all-octave sibling, radical-invariance files have different scopes. README was not edited by this task; another writer appended22 lines describing pillarsXIII–XV, all read and preserved. README now363lines, SHA b5a00a91eacf4d089368efb22a871ed4d5a751a7041fcdf66a48b7d92e924760.

Temporary prefix /tmp/bvi10-*; cleanup status on card. One owned Lean process at a time; require terminal exit_code before next launch. No subagents, web, hgtl7, experiments, full builds, heartbeat changes, commits or pushes.
