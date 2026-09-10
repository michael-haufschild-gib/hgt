# EDQ growing-prime correction budget

RH goal remains active and unproved. Full chain: Euler deletion -> exact zero balance -> cofinal subpower bound for complete signed source -> off-line zero exclusion -> RH. Frontier map remains READ ONLY; route-independent STATUS unchanged. No numerical experiments.

## Discovery from source and deep search
The header in Sieve/DampedCofactorIntegral was stale: fixed-P low-frequency saving exists in DampedCofactorLowFreqBound. More decisively, namespace Sieve, theorem exists_norm_sum_dampedTwist_le_rate in RouteTDampedTwistRate gives constants A,delta,K and eventual N threshold uniform in finite prime set P, u in [0,1], and |tau|<=N. Upper bound K*C(P,c)*N*exp(-v), v=(log N)^(1/20), c=routeTContourLeft A delta (|tau|+N). Growing-P substitution P=primesLE floorN was verified in scratch without dropping C. Quantifiers are not the gap; C is.

## New leaf, built and audited
formal/GaloisForLFunctions/RHTower/Sieve/DampedCorrectionMassBudget.lean, 218 lines, imports DampedCorrBound, RouteTContourRateBounds, Mathlib.NumberTheory.EulerProduct.Basic. Private factor lemma plus six public theorems:
- dampedCorrBound_mass_bounds: c>=1/2, all p>=2, S=sum p^-c => exp S <= C <= exp(5S).
- nat_rpow_le_dampedCorrBound_primesLE: N>=1,c>=1/2 => N^(1-c)<=C(primesLE N,c).
- dampedCorrBound_saving_of_mass_budget: 5S<=v-r => C exp(-v)<=exp(-r).
- mass_budget_of_dampedCorrBound_saving: C exp(-v)<=exp(-r) => S<=v-r.
- eventually_dampedCorrBound_primesLE_contour_saving_lower: delta>0, eventually natural N, uniformly |tau|<=N, exp(9v)<=C(primesLE N,c) exp(-v).
- tendsto_dampedCorrBound_primesLE_contour_saving_atTop: same product at tau=0 tends to infinity.

Proof of power lower bound: finite nonnegative Euler product is smooth-number sum containing all 1<=n<=N; each n^-c>=N^-c. This avoids a prime-count import that had unrelated missing olean. Contour data supply shift*logN>=10v. Factor estimates follow from exp inequalities and x=p^-c<=3/4. No computations used.

This is a lower bound for the MAJORANT FORMULA, NOT the actual damped cofactor or EDQ energy. All-prime Ramare remains open if actual cancellation can be retained. Smaller P can preserve contour saving via positive mass budget but restores rough packet U and its mixed correlations. Do not claim this advances the actual source growth exponent.

## Verification
Scratch passed. Final leaf command lake build --old GaloisForLFunctions.RHTower.Sieve.DampedCorrectionMassBudget succeeded; existing dependency logs replayed, only new leaf Lean process observed. No umbrella/full build. Umbrella import wired near DampedCorrExp. Six new #print axioms via /tmp: only propext, Classical.choice, Quot.sound. scripts/formal_tools.py index refreshed indexes (3 changed); lint exit0 with existing size warnings; diff --check passed. All owned Lean sessions terminated normally; temporary files scheduled for cleanup before turn end.

DampedCofactorIntegral header corrected to point to existing fixed-P saving and explicit uniform-P correction. Paper details in docs/drafts/pipeline/1-in-progress/edq-full-covariance-core-attack.md section Growing-prime correction budget for the damped cofactor, line1535. Other shared worktree edits preserved.

## Deep search audit
Queries with --any --mode deep --budget-seconds 300 --max-rounds 2 --no-refresh --per-module 1 --explore 0 --json:
1. dampedOmegaMoebius \"Ramare cofactor\" \"prime-count deformation\" (limit16): 50.254s.
2. \"divisor transform\" \"inverse prime count\" \"binomial integral\" (limit12):41.193s.
Both completed argument assembly; partial semantic_index_incomplete. Inventory55947files/720511declarations. All56 candidate/source occurrences current declaration-block hashes matched, all source_only/applicability unchecked. Search1 one unverified basic prime-deformation ingredient; search2 two proposals for primePowerLadder_pow/coprimeSupport_multiLadder concerning valuation powers/disjoint support, not our mu/(1+omega) bound. Source inspection found actual uniform-P producer above, checked its applicability in Lean. Do not claim whole semantic corpus covered.

## Continue toward hard obstacle
Actual physical Ramare source: G_N=U_(P,N)-sum_p Z_p, Z_p=D_p A_p+B_p b_p, A_p uses mu(m)/(1+omega_P(m)) excluding p, B_p corresponding scalar/m, D_p f(u)=f(u/p)/p. E_N=||U||²+sum||Zp||²+ordered cross covariance-2 mixed U/Z terms. All-prime P kills U but new result rules out obtaining saving from displayed absolute Euler correction. Need signed cofactor/covariance estimate retaining cancellation or smaller-P rough/mixed recurrence. Prior source card carries exact decomposition and obstruction statuses.