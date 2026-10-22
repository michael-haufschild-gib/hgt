# WL upper-lag excursion block

- **ID:** WL-UEB-20260929
- **Stage:** 1-in-progress
- **Type:** THEOREM candidate
- **Source:** Newly audited actual upper-curvature interpolation and current corpus lag dichotomy.
- **Statement:** Let integers k>=4 and h satisfy 2h<=k. For every M,delta>=0 with `h^2<=delta*k*sqrt(k)`, if `a_k>M+delta`, then either every integer n in `[k-h,k]` has `a_n>M`, or every integer m in `[k,k+h]` has `a_m>M`. Delta=1 gives the initial k^(3/4) scale candidate.

## Plan
1. [ ] Corpus/public novelty audit of thick positive excursions and low-quantile receivers.
2. [x] Dependency-closed paper proof from exact upper interpolation.
3. [x] Lean formalization of height-scaled propagation and delta=1 corollary. Full population dichotomy is the next independent candidate.
4. [ ] Targeted artifact, axiom/source/lint audits, wiring and frontier update.

## Paper proof
Assume each side has a point at or below M: `k-h<=n<=k<=m<=k+h`. Then n>=k/2>=2, `m-n<=2h` and
`(m-n)^2/(8*n*sqrt(k)) <= h^2/(k*sqrt(k)) <= delta`.
The actual interpolation law gives `a_k<=M+delta`, contradicting the specified central excursion. Therefore one entire side is above M. The argument uses signed actual lag values and remains valid across every prime-power jump. For delta=1 the entire original proof is recovered.

The radius may be on the k^(3/4) scale. Thus upper excursions cannot be isolated sparse exceptions on both sides at this scale. The next producer test is whether actual arithmetic yields sufficiently frequent low lag points on both sides. That low-point statement is not assumed proved; no RH conclusion is asserted yet.

## Log
- 2026-09-29: Recorded paper candidate before Lean code. Corpus hybrid search in `/tmp/wl-lag-excursion-block-search-20260929.json`; exact source `rg` found older continuous-to-integer interval bounds but no thick upper excursion statement. C10 final source audit is the only owned foreground Lean process.
- 2026-09-29: Paper audit strengthens the radius to the exact height-scaled budget `h^2<=delta*k*sqrt(k)` for any delta>=0. This is a new strengthened conjecture, with the full paper proof recorded above before Lean transfer. Scratch now contains the height-scaled law and its delta=1 corollary; neither checked yet. Hybrid corpus search completed (full inventory snapshot, pending compiler coverage); relevant old source bounds concern a single gap or recurrence, not an entire high-lag side. Public searches returned no exact collision, insufficient to certify unseen public/training absence.
- 2026-09-29: Scratch both closed actual-lag propagation laws passed. Only warning: `push_neg` deprecated; production uses the current `push Not` spelling already verified in existing source. New leaf `formal/GaloisForLFunctions/RHTower/WeilLagExcursionBlocks.lean` contains exact proved bodies and documentation, own umbrella import wired. Targeted artifact build running. Public names: `integerLag_upper_excursion_has_height_scaled_block`, `integerLag_upper_excursion_has_one_sided_block`. All-public axiom and final direct-source audits still pending. No low-lag density producer or RH conclusion asserted.
- 2026-09-29: Targeted `lake --old build +GaloisForLFunctions.RHTower.WeilLagExcursionBlocks` exited 0; 8829 dependency jobs, new leaf reported 14 seconds, no own warnings. All-public axiom audit running. Production has 73 lines and no heartbeat setting. C14 finite prime tile count has a separate paper proof and scratch, pending Lean check.
- 2026-09-29: Both public excursion declarations passed axiom audit, exactly `[propext, Classical.choice, Quot.sound]`; closed height-scaled signature captured in `/tmp/wl-excursion-blocks-axioms-final.txt`. Final `lake --old env lean GaloisForLFunctions/RHTower/WeilLagExcursionBlocks.lean` exited 0, empty output (`/tmp/wl-excursion-blocks-source-final.txt`). Own whitespace/proof-debt scan passed; umbrella import present. Frontier/index/lint registration update remains pending. New geometric consequence is proved; actual low-lag population producer remains open.
- 2026-09-29: Frontier updated; index refresh exited 0 (`/tmp/wl-excursion-blocks-index-final.txt`). Authoritative global lint exited 1, exactly 14 unrelated unreachable modules (`/tmp/wl-excursion-blocks-lint-final.txt`), no own module or forbidden declaration error. Own registration and audits complete, global gate remains failing outside scope. C15 now audits a stronger actual prime population consequence using already-proved every-base proportional theta mass at alpha=3/4; do not recreate that old mass theorem as new knowledge.
