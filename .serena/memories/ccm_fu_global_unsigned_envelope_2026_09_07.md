# CCM-FU global unsigned envelope and large-prime pairs — 2026-09-07

## Persisting scope
Active goal is unconditional Lean RH/falsification via CCM-FU; NOT achieved. Frontier map is READ-ONLY by latest explicit user instruction. Do not edit or revert others' map changes. No STATUS change by this work because conclusions are route-specific. No subagents/commits/pushes. Preserve concurrent changes. Read this memory after mem:ccm_fu_signed_smooth_block_ceiling_2026_09_07; no need to re-audit old declarations.

## New closed mathematical progress
R is actual smooth divisor-hyperbola remainder; a=log(2*pi)/2-gamma-1/6. K_d(M)=divisorUnsignedDilationChannel M d; w(n)=sqrt(n+1)-sqrt(n).
1. Source orientation R(s(s+1)-j)<=R(s(s+1)+j), s>=1,j<=s.
2. Even sqrt clock V_c(t)=(w(c-t)+w(c+t))/2 obeys V_c(j)-V_c(i)<=(j²-i²)c^(-5/2)/4 for c>0,0<=i<=j<=c/3.
3. Actual weighted block moment sum_(n=s²..(s+1)²-1)(n-c)²w(n)<=c/3+1/18, c=s(s+1),s>=2.
4. Weighted smooth block sum R(n)w(n)<=a for ALL s>=1.
5. Global source R(n)>=0 for ALL n, including first four blocks.
6. Global SmoothAbel(M)<=a*sqrt(M), ALL M. Terminal partial block CLOSED, no logarithmic/additive loss.
7. Global K_d(M)<=a*sqrt(M), ALL M,d (including0).
8. Analytic margins a<9/50 and unit asymptotic c_unit=log(2*pi)/2-gamma-1/4>9/100.
9. Exists N0, forall N>=N0,d, K_d(N)<=2K_1(N). NO quotient restriction, simultaneous every dilation.
10. Exists P0, forall integer p>=P0,M,d, K_(p*d)(M)<=2K_d(M). ALL cutoffs/cofactors. Below N0, p-channel inactive; existing unit/cofactor equivalence transfers.
11. Exists P0, forall distinct active primes p,q>=P0 at ANY M/ratio, actual Q_M({p,q})<=Q_M(empty). Exact existing failure witness r in{p,q},r<N<=M,K_r(N)>2K_1(N) contradicts9.
Thresholds exist but no explicit numerals claimed. Sharper 1/8 global envelope remains open and unnecessary for9-11.

## Exact remaining hard obstacle
Unit factor-two failures confined to FINITELY MANY UNIT CUTOFFS N<N0. Every original two-prime failure must involve AT LEAST ONE prime in a fixed finite head; parent M may still be unbounded. Do NOT claim finite full energy states or both primes bounded. Result10 concerns raw unsigned channels, NOT admissibility of any large next prime for arbitrary nonempty processed signed P. Result11 concerns two operations from empty. Arbitrary signed fields, growing/exhaustive orders, full signed Abel bound, SD1/PE4, RH remain OPEN. Main next problem: mixed interactions AFTER processed primes, plus finite unit cutoff head. Do not repackage this result as solving the all-state successor. Existing greedy envelope extension candidate and diagnostics in earlier memories remain relevant; avoid predictable experiments or already-closed generic receivers.

## Actual proof mechanism
Orientation uses paired log products (c-i+1)(c+i)=c²+c-i(i-1), analytic Pade log lower, sum i(i-1)=j(j²-1)/3, and harmonic geometric upper correction1/(6c).
Clock uses convexity of (1-t)^(-3/2)-(1+t)^(-3/2) on[0,1/3] to bound<=4t, exact endpoint square bounds, scaled derivative comparisons. Finite covariance identity and exact moments mu2=c/3,mu4=c(3c-1)/15 give clock excess<=1/18.
Pair orientation with decreasing clock and existing geometric quadratic source ceiling gives weighted ceiling. Exact correction above a is -(48(s-2)^3+372(s-2)^2+742(s-2)+153)/(1080s²(s+1)²(s+2))<=0 for s>=2. First block analytically bounded. Initial positivity uses geometric center minima, exact factorial log identities at2,6,12,20 and analytic log/Euler bounds. Completing terminal block gives SmoothAbel((s+1)²)<=a*s, s=floor sqrtM<=sqrtM. Centered cancellation gives unit bound, exact clipped homothety all dilations. No numerical research experiment/computational proof premise.

## Files and public names (RHTower namespace)
Six NEW leaf modules under formal/GaloisForLFunctions/RHTower:
- DivisorSmoothBlockOrientation.lean: divisorHyperbolaSmoothRemainder_reflection_le
- SymmetricSqrtClockBounds.lean: symmetricSqrtStep_quadratic_lipschitz
- SquareBlockSqrtClockMoment.lean: sum_square_block_sqrtStep_quadratic_le
- DivisorSmoothWeightedBlockCeiling.lean: sum_divisorHyperbolaSmooth_square_block_mul_sqrtStep_le_mean
- DivisorSmoothSourcePositivity.lean: divisorHyperbolaSmoothRemainder_nonneg
- DivisorUnsignedGlobalEnvelope.lean: divisorHyperbolaSmoothAbel_le_exact_mean_sqrt; divisorUnsignedDilationChannel_le_smoothMean_sqrt; exists_divisorUnsignedDilationChannel_uniform_unit_double; exists_divisorUnsignedDilationChannel_large_multiplier_double; exists_mobiusDivisorSelectionEnergy_two_large_primes_le_empty
Two edited existing leaves:
- DivisorHyperbolaSharpBlocks.lean: new divisorHyperbolaSmoothRemainder_center_le wrapper around existing private minimum.
- DivisorSmoothSignedBlockCeiling.lean: exposed old private smooth_pair_upper as divisorHyperbolaSmoothRemainder_pair_le_geometric_quadratic, updated one internal call, unchanged mathematical proof.
All six new modules wired into RHTower.lean. NO umbrella build.

## Validation COMPLETE for exact files, no repeats needed
All scratch checks and eight exact leaf emits passed via lake env lean, one owned foreground process at a time. Final exact emit handles orientation19553,clock24303,moment87934,weighted3363,positivity8627,global8312,old-block68924,sharp73003 all exit0. Orientation emits harmless informational tactic suggestions, no errors/warnings. All others quiet.
ONLY twelve NEW public declarations axiom-audited ONCE in /tmp/ccm_fu_global_envelope_axioms.lean; session72844 EXIT0, all exactly [propext,Classical.choice,Quot.sound]. No old capstone rechecked. scripts/formal_tools.py index session91079 EXIT0; scripts/formal_tools.py lint session27792 EXIT0, formal lint passed with existing large-file warnings. git diff --check passed; whitespace checked all six new untracked leaves. No source sorry/added axioms/numerical premises.
Targeted Lake packaging audit STILL PENDING. DO NOT repeat known --old/preflight path that launches prerequisite rebuilds (details prior memory). No Lake build passed claimed. User prohibits large/umbrella rebuilds.
All owned Lean/Lake processes ended; ps showed none. Eight explicit paths removed via Path.unlink and verified absent: /tmp/ccm_fu_smooth_orientation.lean, /tmp/ccm_fu_symmetric_clock.lean, /tmp/ccm_fu_clock_variance.lean, /tmp/ccm_fu_weighted_blocks.lean, /tmp/ccm_fu_smooth_positivity.lean, /tmp/ccm_fu_smooth_global.lean, /tmp/ccm_fu_global_envelope_axioms.lean, /tmp/ccm_fu_global_envelope_lint.log. No remote workers/files created this turn.

## Documentation
Working card moved to docs/drafts/pipeline/3-formalized/ccm-fu-global-unsigned-envelope.md with closed statements, detailed dependency-closed paper proof, exact public names/audit limitations/open signed boundary. Prior path docs/drafts/pipeline/1-in-progress/ccm-fu-weighted-smooth-block-ceiling.md removed; search found no remaining references.
Updated docs/drafts/pipeline/1-in-progress/ccm-fu-bounded-quotient-profiles.md to current result, preserved prior saved-vector diagnostic provenance. Updated only remaining obligations in docs/drafts/pipeline/3-formalized/ccm-fu-signed-smooth-block-ceiling.md. Frontier map READ-ONLY; STATUS changes belong to others. Generated index files shared, concurrent source edits/commits preserved.
