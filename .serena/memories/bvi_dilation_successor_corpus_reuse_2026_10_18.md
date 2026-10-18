# Problem 2: physical Bézout jumps in the actual dilation profile

Active unbounded goal; never mark complete merely at a checkpoint. Read the objective attachment at each goal continuation: `/Users/michael/.codex/attachments/dc8dff0d-0b26-4db3-814f-cd2c8c3438d5/pasted-text-1.txt`. No hgtl7, no RH work, no numerical experiments. Work on problem 2 of `docs/reports/walls/bezout-wall1-programme.md`. User correction is binding: use `python3 scripts/formal_tools.py research ...` for the Lean corpus, inspect candidates/source arguments and freshness, then verify APIs in a /tmp Lean scratch. Do not infer novelty from missing hits.

One owned Lean process at a time; await actual terminal handle. Other independent threads modify/build this worktree. Never kill or reset their jobs/files. Final audits use `lake --old env lean -j 1` on the original module, with explicit -o/-i for importable artifacts. No full/umbrella builds, no heartbeat increases, no sorry/admit/axiom/opaque/unsafe declarations, no commits/pushes. #print axioms only in /tmp. No subagents used/authorized. Architecture/testing docs absent. Plan tool unavailable; track in the card. Serena ignores these Lean paths; established read/patch fallback.

Authoritative card: `docs/drafts/pipeline/1-in-progress/bvi-dilation-successor-jump-coupling-2026-10-18.md` (now >1000 lines: use tail/offset, not full reread). Last continuation outcome PROGRESS. C9-C11 completed. No owned Lean/search/index/lint/profile process remains. Goal remains active; next is C12 below.

## Completed C1-C8

Ten-module total after C11 is 101 public declarations, plus one exported existing gcd-divisor interface. Earlier seven modules contained 82 declarations, all original-source checked and individually audited with only propext, Classical.choice, Quot.sound:
1. `ReciprocalJumpKernelAndDilationLagSectors.lean` (16)
2. `DilationProfileIntegerJumpCoupling.lean` (8)
3. `DilationSuccessorFiberReciprocity.lean` (9)
4. `DilationSuccessorSectorHarmonicClassification.lean` (17)
5. `DilationSuccessorDigammaRenormalization.lean` (10)
6. `DilationSuccessorLeastSeedResonance.lean` (11)
7. `DilationJumpValuationClock.lean` (11)
All live in `formal/GaloisForLFunctions/BezoutValuationIncidence/` and are wired. See prior original/axiom logs under `logs/bvi-dilation-successor-*` and `logs/bvi-dilation-jump-clock-*`.

C8 also exported the existing private gcd-sum proof through public `ramanujanLagCoefficient_eq_gcd_divisor_sum` in `RamanujanLagCoefficientAndTotientQuotient.lean:57`; additive wrapper preserves private constant names for compiled dependents. Separately source/audit checked. C3 `ramanujanNaturalCoefficient_one` now delegates existing `RHTower.pm_ramanujan_at_one` instead of duplicating the proof; separately rechecked.

Use existing digamma/Abel results rather than new analytic machinery: `RHTower.sum_gaussDigammaSeriesTerm_eq_digamma_shift`, `HTGeometry.norm_digamma_shift_sub_le`, `RHTower.hasSum_digamma_sub`, `abs_sum_range_mul_antitone_le`. Superseded standalone convergence drafts were removed.

## C1-C8 core interfaces

Let c_r(n)=Re(d4BMRamanujanNaturalCoefficient n r), A_r(N)=Re(pmRamanujanPrimitive r N), B_r=pmRamanujanPrimitiveBound r. `dilationJumpPairs H p q = Icc 1 (H/p) ×ˢ Icc 1 (H/q)`; gap = p*a-q*b as an integer. The lag set is the IMAGE of actual pair gaps, not an arbitrary interval. All pairing is at one finite physical horizon; no infinite lag rearrangement.

`reciprocalJumpKernel_eq` gives 1/max(pa,qb)-1/(H+1) for feasible positive pairs. `ramanujanDilationLagSector` is the signed pair sum at one exact gap. C2: `pmRamanujanDilationProfile_eq_integerDilationGram hr hp hq` gives Phi_r(p/q)=sqrt(p)*sqrt(q)*G_r(p,q), where G is the original pronic integer-cell series. `abs_dilationProfile_sub_finite_lag_sectors_le` has error sqrt(pq)*B_r^2/(H+1).

C7: the intrinsic least positive seed `leastSuccessorSeed p q` is zero for forbidden/noncoprime scales. `successorLeastSeedResonance r p q = c_r(a)c_r(b)/a`. `abs_normalized_successor_sector_sub_leastSeed_le` at positive modulus r bounds |sqrt(pq)*S_r(1,p*q*r)-sqrt(q/p)*seed| by r*phi(r)^2/sqrt(pq). `dilation_profile_least_successor_seed_uniform` retains the FULL signed complement and has O(1/(k+2)) for p=k+n+2,q=k+m+2.

C8 identifies c_r(n) with the existing lag coefficient and proves support iff r≠0 and clock(r)|n. Nonzero pair iff r≠0 and clock(r)|gcd(a,b). Nonzero physical pairs have clock(r)*gcd(p,q) dividing their gap. Forbidden sectors vanish at every cutoff. On a successor pair, nonzero coefficient product iff Squarefree r; hence nonsquarefree lag-1 sectors vanish. Allowed signed sums may still cancel.

## C9: exact radical reduction (complete)

`RamanujanRadicalDilationReduction.lean`, 179 lines, seven public theorems, capstone `dilation_profile_radical_reduction` at line171.
Uses existing `primeRadical` in `TranslatedWindowStrideAnnihilationAndLcmReturnObservability.lean:163` and existing totient quotient. No duplicate radical definition.
For s=rad(r), v=clock(r)=r/s:
- c_r(v*n)=v*c_s(n)
- c_r(n)=v*ramanujanDilationJump s v n
- A_r(N)=v*A_s(N/v)
- G_r(p,q)=v^2*G_s(v*p,v*q)
- Phi_r(p/q)=v*Phi_s(p/q) for r>1 and positive integer p,q.
Capstone uses r+2,p+1,q+1 and has data only. Private helpers establish radical positivity, same prime factors, r=s*v, radical>1, phi(r)=v*phi(s). Mathlib reuse: `Nat.totient_eq_div_primeFactors_mul`, `Nat.gcd_mul_left`, `Nat.mul_div_mul_left`, `Nat.div_div_eq_div_mul`. `tsum_mul_left` is unconditional for real scalars; probe must instantiate universes as `@tsum_mul_left Nat Real`, not bare `@tsum_mul_left` in a have.

Log `logs/bvi-radical-dilation-reduction-original.txt`: original source exit0, no diagnostics. `logs/bvi-radical-dilation-reduction-axioms.txt`: all seven standard three axioms. Replay `/tmp/bvi-c9-radical-axioms.lean`. Initial extended scratch failed only on universe-unspecified probe; actual proofs elaborated. A preceding recursive-simp-risk run was cancelled by owned PID, confirmed exit143 before replacement. Canonical source specializes primitive rewrite to the original modulus so simp cannot recurse into successive radicals.

## C10: finite sector transport and boundary (complete)

`DilationClockSectorBoundaryAndSuccessorTransport.lean`, 231 lines, seven public theorems plus one definition. Capstone `dilation_clock_successor_transport` line222.
Reuse `RHTower.sum_Icc_filter_dvd_reindex` from `EulerDeletionQuasiShuffleConvergence.lean:95`; no new divisor bijection. New weighted-sum reindexing is unconditional for all r,N,F. Reindex actual supported pairs as (v*a,v*b), retaining the physical gap and cutoff.
Define `ramanujanDilationLagMass` as signed coefficient mass on exactly the same finite fiber. With T=floor(H/v), the exact law is
S_r(v*h,H)=v*S_s(h,T)+v*(1/(T+1)-v/(H+1))*M_s(h,T).
At H=v*(T+1)-1 the correction vanishes. The radical successor is transported to original physical lag v. Helper statements use intrinsic nonzero/positive domain data; data-only capstones shift r+2,p+1,q+1.

Original source session98982 exited0 with no diagnostics, log `logs/bvi-clock-sector-transport-original.txt`. All eight axiom prints passed in C11 scratch69379; log `logs/bvi-clock-sector-transport-axioms.txt`, replay `/tmp/bvi-c10-clock-sector-axioms.lean` (minimal import only C10). First C10 scratch had only residual 1-1=(T+1)*0 after field_simp; final ring fixed it. `Nat.add_mul_div_left` installed-core signature was read and verified in scratch; exact lexical search missed it, rephrased deep search mainly returned related quotient methods. No new API guessed.

## C11: actual profile with a nonzero radical seed (complete)

`DilationClockSuccessorSeedCoupling.lean`, 139 lines, four public theorems:
- `successorLeastSeedResonance_radical_ne_zero_iff_coprime`: for r≠0,p,q>1 the radical seed is nonzero iff p,q coprime. Uses existing least-seed spec, C8 squarefree pointwise criterion, and `squarefree_primeRadical`.
- `abs_normalized_clock_successor_sector_sub_radicalSeed_le`
- `abs_dilationProfile_sub_clockSeed_and_other_sectors_le`
- `dilation_profile_clock_successor_seed_coupling` line117, data-only combined bound and seed iff.
For s=rad(r),v=clock(r), H=v*(p*q*s+1)-1:
|sqrt(pq)*S_r(v,H)-v*sqrt(q/p)*seed_s| <= v*s*phi(s)^2/sqrt(pq).
The actual profile minus sqrt(pq)*(sum_h S_r(h,H)-S_r(v,H)) minus that seed has error at most sqrt(pq)*B_r^2/(H+1) plus the sector error. Full signed complement retained; no lower bound or control of it asserted.

Scratch69379 passed. Original source56350 exited0, no diagnostics; log `logs/bvi-clock-successor-seed-original.txt`. All four axiom prints23283 exited0 with exactly propext, Classical.choice, Quot.sound; log `logs/bvi-clock-successor-seed-axioms.txt`, replay `/tmp/bvi-c11-clock-seed-axioms.lean`.

All C9-C11 sources wired once. All 19 new public declarations source checked and individually axiom audited. Merged C9/C10/C11 scratch drafts removed; complete logs, research JSON and replay files retained. No owned process remains.

## Index/lint and shared README

Index45826 exit0, log `logs/bvi-clock-radical-seed-index.txt`; API/gaps/overview refreshed, lexical cache already up to date. Exact quoted search `/tmp/bvi-c9-c11-discoverability.json` returns exactly three capstones (C9line171,C10line222,C11line117). Quoted underscore identifiers matter: unquoted --any can OR all words and produce huge unrelated results.
Final lint55115 exit1: 381 large-file warnings and sole unchanged unrelated error `research leaf module at package root: TransHorizonIncidenceMechanics.lean; move it into an owned theorem area`. Log `logs/bvi-clock-radical-seed-lint.txt`. Do not claim global lint passed or move unowned file. Scoped whitespace and forbidden-declaration scans passed.
README was concurrently rewritten into a thematic guide and then expanded again. Preserve that rewrite; do not restore old long section10. Read current guide fully at session start (done for initial rewrite this continuation). Added only three narrow new thematic entries and corrected two proven errors: arbitrary prime-square revival is at its clock p^a, not universally lag2; squarefree support does NOT restore lag composition (modes3 and6 defect -3/4). Existing theorems `sieveLagMultiplier_prime_pow_revival_at_clock` and `nonMarkovianLagDefect_first_octave_table` were probed successfully. Removed an extra EOF blank line, preserving concurrent entries. The old file count remains unedited.

Concurrent work is not ours: `OrderedPronicGapCellsAndCollectivePrefixEnergy`, `RamanujanOrderedGapCollectivePrefixEnergy`, `AsymmetricAdjacentDivisorTruncation`, `UniformActiveDeletedCompensatedRemainder`, `ClockWaveletTensorBuchstabL2TelescopeAndShortWindowBridge`, new WallOneBridge packaging modules, and unrelated RH files. The new Ramanujan gap-chain module already gives actual signed collective PREFIX and bilinear bounds; its later signed tail remains unresolved. Do not reinvent it. `BeurlingGibbsCotangentTransportAndSchurCollarWallOneBridge` Tool2 directly packages existing C2/C7; its radical-fibre damping result is a different observable. Separate problem4 memory does not govern our task's README permissions.

## C12 next: seed size, nearby primes, and the positive signed complement

No C12 Lean code yet. Paper target and prior-work audit are recorded in the card. Do not confuse C11 nonzero with a uniform lower bound.
If p*a=q*b+1 and q>p, then a>b and (q-p)*a=q*(a-b)-1 >= q-1. If p>q and p-q>1, then b>a and (p-q)*a=q*(b-a)+1 >= q+1. The difference-one reverse orientation is an essential exception: p=q+1 has seed(1,1). Existing `consecutive_scale_successor_harmonic_coupling` already records adjacent-scale behavior. Large distinct odd primes avoid that exception.
For d=abs(p-q), p,q>1, and either p<q or q+1<p, conjectured/dependency-closed paper bound:
|seed_s(p,q)| <= phi(s)^2*d/(q-1).
Coprime branch: least-seed spec gives a>0; geometry gives q-1<=d*a. Existing `abs_successorFiberAmplitude_le_totient_sq` yields |seed|*a<=phi(s)^2. Multiply the first by |seed|, use the second, divide by q-1>0. Noncoprime branch is the zero seed. Formalize this exact finite inequality first.
Then C11 gives a relative-gap plus inverse-scale bound on the original clock sector and a controlled approximation of Phi by its full retained signed complement. The positive survivor is that complement carrying the nonzero nearby-scale profile; do not retire the entire coupling route or claim global cancellation. No prime-spacing assumption may be inserted.

C12 search `/tmp/bvi-c12-nearby-clock-sector-prior-research.json` completed partial=false. All20 candidates and20 source statements inspected; most candidates and proposed prime-density ingredient set irrelevant. Relevant source arguments/proofs read: `RHTower.pmRamanujanPrimitiveGram_nearby_error` and `RHTower.exists_pmRamanujanPrimitiveGram_nearby_gt` in `PMRamanujanNearbyPrimeResonance.lean`. Existing exact APIs there:
- `continuousOn_pmRamanujanDilationProfile hr` on Ioi0 (line170)
- `pmRamanujanDilationProfile_one hr` = positive diagonal Gram (line176)
- `pmRamanujanPrimitiveGram_pos hr` used by existing nearby proof
- `exists_prime_pair_ratio_lt` already realizes arbitrarily large arbitrarily close prime pairs; verify exact namespace/signature through corpus/scratch before new use.
No new continuity or prime-realization proof needed. This is actual carrier geometry, not RH work.
Focused lexical follow-up `/tmp/bvi-c12-seed-lexical-research.json`: all14 hits inspected, mainly C4/C7/C11 plus existing adjacent-scale capstone; no seed-size bound returned. No corpus-wide novelty conclusion. Coverage inventories complete but semantic coverage unmeasured and compiler metadata largely pending/stale; use verified source interfaces. Continue from this card and canonical modules, not from deleted scratch drafts.
