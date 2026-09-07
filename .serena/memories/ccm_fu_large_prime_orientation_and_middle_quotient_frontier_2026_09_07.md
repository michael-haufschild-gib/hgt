# CCM-FU large first-prime orientation — verified 2026-09-07

## Goal / current frontier
RH goal remains ACTIVE and OPEN. This turn is PROGRESS: an actual infinite family of two-prime ceilings is now proved. Full chain: Guinand–Weil source → marked rectangular current → affine Suzuki checkpoints → signed curvature → prime–polar–Gamma/unit-Riesz boundary → Xi-screw Green → RH. SD1, all-cutoff two-prime ceiling and complete growing adaptive schedule remain open.

At every sufficiently large parent cutoff M, if at least one of distinct primes p,q<M satisfies M<=5p (or M<=5q), E_{p,q}(M)<=E_empty(M). Processing that large prime first preserves EVERY retained Möbius sign; the second prime contracts energy. Therefore any two-prime ceiling failure in that parent tail requires BOTH 5p<M and 5q<M. Large-parent unit factor-two failures are confined to 5<=M/p<T, for one universal upper quotient threshold T from the prior turn. Finite parent regime and remaining middle quotient profiles remain open.

## New leaf: eight public theorems
`formal/GaloisForLFunctions/RHTower/MobiusDivisorLargePrimeOrientation.lean` (293 lines), imports existing DivisorSmoothSquareBlockMean, wired once in RHTower umbrella.

1. `divisorUnsignedDilationChannel_one_le_fifteenth_of_le_five`: for ALL N<=5, K1(N)<=sqrt(N)/15. Analytic endpoint proof; no stored data. Private first-three helper proves stronger sqrt(N)/16 using D1<=1/6, D2<=1/24, sqrt2<=3/2, sqrt3>=1. Fourth endpoint: analytic gamma/log bounds give D1<=3861/25000, D2<=13/6250, D3<=12761/50000. Clock gaps bounded by 415/1000,319/1000,268/1000 via rational squared inequalities for sqrt2,sqrt3. Product sum <2/15. D4<=0 implies K1(5)<=K1(4), completing endpoint5.
2. `divisorUnsignedDilationChannel_le_fifteenth_of_le_five_mul`: ALL M,p>0, M<=5p -> K_p(M)<=sqrt(M)/15. Exact clipped interpolation uses common endpoint/clock weights. Boundary M=5p uses integer homothety explicitly.
3. `eventually_divisorUnsignedDilationChannel_one_ge_fifteenth`: actual unit source eventually >=sqrt(M)/15. Private exact constant margin a=log(2*pi)/2-gamma-1/6>41/240; c>=11/12 follows from actual Stirling limit, gamma<139/240 from existing analytic gamma upper. Thus a-5/48>1/15, with half the strict margin absorbed into the existing eventual coefficient band.
4. `exists_divisorUnsignedDilationChannel_above_fifth_cofactor_domination`: exists M0, ALL M>=M0,p>0 with M<=5p, ALL d, K_(pd)(M)<=K_d(M). If d<=4, both parent quotient endpoints lie on the common one-fifteenth tail for M>=4max(T,1); same clock transfers lower bound to parent. Child has the one-fifteenth upper. d>=5 children are zero, d=0 handled. No support omission or unproved arithmetic premise.
5. `exists_mobiusDivisorSelectionFibre_above_fifth_parity`: exists M0, ALL M>=M0 and prime p with M<=5p, every retained label after first p has original Möbius parity. Original prime-label amplitudes are exact unsigned product channels; insertion subtracts child from parent. Processed labels vanish. Nonprime labels vanish directly from primeFactors support, including all such labels, not a sample.
6. `exists_mobiusDivisorSelectionEnergy_above_fifth_two_prime_ceiling`: exists M0, ALL M>=M0 and distinct p,q primes<M with M<=5p, E_{p,q}<=E_p AND E_{p,q}<=E_empty. Full parity makes every second prime contract, first-prime contraction was already formal. This is actual source theorem, not conditional on an open amplitude law.
7. `exists_mobiusDivisorSelectionEnergy_two_prime_failure_below_fifth`: exists M0, every original two-prime ceiling failure at M>=M0 requires 5p<M and 5q<M. Uses symmetry of pair labels.
8. `exists_divisorUnsignedDilationChannel_factor_two_failure_middle_quotient`: exists M0,T>=1, for all M>=M0,p>0, actual failure 2K1(M)<Kp(M) implies 5p<M AND 5<=M/p<T. Combines new cofactor domination with prior universal quotient bound.

These do NOT assert repeated preservation after the second merge, all-cutoff unit comparison, full two-prime ceiling or RH.

## Frozen saved-vector diagnostic — DO NOT rerun
New files under `docs/drafts/pipeline/2-fully-proven/computations/ccm-fu-adaptive-prime-energy-2026-09-06/`:
- `bounded_quotient_profile_reanalysis.py`
- `bounded-quotient-profile-reanalysis.json`
Reads existing `first-prime-unit-clock.csv` exactly once; regenerates NO defects/channels/subsets/paths. Source SHA256 `7911603285ddb67bc420d35453280026e8e7d94e5b374a7637ea1a5708f839a2`.
Frozen question: candidate global K1(N)<=sqrt(N)/8 and sufficient ordinary prefix sum D(k)<=(N+1)/8, across all 1024 saved positive cutoffs.
- Channel candidate passes all1024; maximum normalized K1(N)/sqrt(N)=0.11109282939761682 at N=120, one-eighth margin0.1523454209999595 in raw channel.
- Prefix candidate FAILS16 cutoffs; worst N119 prefix17.288487730905896 vs15, deficit2.2884877309058957.
Both numerical guidance ONLY. Global one-eighth envelope remains UNPROVED. Prefix failure is diagnostic evidence, not a formal no-go certificate or route retirement. Do not use it as a valid universal proof hypothesis. A second summation cannot silently discard the original terminal prefix times endpoint clock; this boundary prevents inferring a hard-cutoff channel envelope from second-prefix sign alone.

## Next work
Actual remaining target: middle quotients 5<=M/p<T and finite parent regime, or aggregate source compensation bypassing the sufficient factor-two comparison. Global normalized unit upper1/8, IF proved analytically, would combine with the already strict eventual lower coefficient >1/16 to close all dilations at sufficiently large parents. It is supported by saved data but not yet proved. First-five endpoint proof has closed a useful actual sector; do not redo it or assume the same one-fifteenth endpoint ceiling beyond5. Two-prime families with both primes belowM/5, and complete growing schedules, remain.

## Verification complete / efficiency
Complete scratch and exact new tree leaf passed `lake env lean`; only its new olean generated. Eight NEW public declarations axiom-audited ONCE, only propext/Classical.choice/Quot.sound, no added axioms, sorryAx or computational certificates. No old declaration audits or dependency/full/umbrella builds. Formal lint PASSED with132 existing large-file warnings only. Index refreshed (11 changed,0removed; preserve concurrent work). New card links and scoped diff whitespace passed. All SIX exact owned temp/scratch/log files removed, final strict ps snapshot ZERO live lean/lake processes. No process remains owned.

## Docs
New Stage3 card `docs/drafts/pipeline/3-formalized/ccm-fu-large-prime-orientation.md` contains paper proof and verified status. New OPEN Stage1 card `docs/drafts/pipeline/1-in-progress/ccm-fu-bounded-quotient-profiles.md` retains global-envelope question, frozen diagnostic, closed sector and remaining middle profiles. Updated two-prime-local-blocks, adaptive-prime-ceiling, source diagonal dominance and current frontier detailed paragraph+CCM-FU row. Expanded route-independent MUST-UNIFORM-DILATION-TAILS: use same positive clock mass for amplitude normalization; common endpoint ceiling controls clipped phase, remaining profiles need separate comparison.

## Lean pitfalls
Do not use unknown names Nat.one_add_one_eq_two or Real.sqrt_ofNat; norm_num normalizes literal sqrt4 and natural arithmetic. Avoid `by have h : ... := by positivity; omega` since semicolon attaches omega to inner proof; make h a separate line then omega. Exact homothety endpoint rewrite must avoid global rewrite p=p*1 which changes every p occurrence; get `divisorUnsignedDilationChannel_mul p 5 1`, simp Nat.mul_one in that equality, then rewrite. `Nat.prime_of_mem_primeFactors` is verified local API.

Prior context: `mem:ccm_fu_exact_smooth_mean_and_bounded_quotient_obstruction_2026_09_07`, `mem:ccm_fu_second_centered_hyperbola_and_unit_floor_2026_09_07`, `mem:ccm_fu_two_prime_local_factor_and_unit_obstruction_2026_09_07`.