# CCM-FU: complete fixed-core quadratic energy limit (2026-09-08)

## Goal and constraints
RH via CCM-FU remains ACTIVE and UNSOLVED. Full chain: literal divisor source -> signed prime selection with renewable reserve -> uniform signed Abel bound -> existing CCM-FU RH implication. Latest explicit user override makes docs/drafts/pipeline/1-in-progress/rh-current-frontier-map.md READ ONLY; never edit/revert. STATUS unchanged: no new route-independent fact here. No subagents, commits, pushes or numerical experiments this turn. Prior fixed-core reserve screen is complete and must not be repeated/enlarged. See `mem:ccm_fu_fixed_core_profile_and_reserve_signs_2026_09_08` for prior exact profile, tail cancellation, and frozen experiment.

## Main result NOW CLOSED
For EVERY fixed finite prime core P, INCLUDING EMPTY, the actual COMPLETE energy Q_P(M)/M^2 converges to an explicit nonnegative convergent series of literal quotient-block masses. All arithmetic labels and all quotient depths retained. Density and full energy-limit assembly are no longer open prerequisites. Signed reserve supply and renewal through changing cores remain the hard obstacle.

Let rho_P=Sieve.squarefreeDensity*prod_(p in P) p/(p+1), with existing squarefreeDensity=6/pi^2. Let H_P(n)=mobiusDivisorSelectionFibre n P empty. The physical square-root interpolation on quotient n has a_n=(H_P(n+1)-H_P(n))/(sqrt(n+1)-sqrt n), b_n=H_P(n)-a_n sqrt n. Define Phi_n(c)=a_n^2*c+(4/3)*a_n*b_n*c*sqrt c+b_n^2*c^2/2. The mass b_(P,0)=0; for n>0 b_(P,n)=rho_P*(Phi_n(1/n)-Phi_n(1/(n+1))). Then b_(P,n)>=0, Summable b_P, and Q_P(M)/M^2 -> tsum_n b_(P,n).

Stronger tail law, all M and T>0, with C_P=(3/5)*2^(P.card-1), NAT TRUNCATED exponent subtraction: complete source tail M/r>=T has energy <= (C_P^2/T)*M^2. Count tail indices <= floor(M/T), use existing abs_mobiusDivisorSelectionFibre_le_source_amplitude and exact r I_P^2=F_P(primeFactors(r))^2. This includes empty P and does not require nonempty-core head cancellation. C_P grows with core cardinality; no growing-core uniformity/reserve follows.

## Four NEW leaves, 18 PUBLIC theorems, ALL checked and audited ONCE
All under formal/GaloisForLFunctions/RHTower, all four wired into RHTower.lean. No umbrella/full build. Needed four leaf oleans emitted via lake env lean FILE -o LEAF. Every public theorem audited in external scratch; ONLY propext, Classical.choice, Quot.sound. No numerical premise/added axiom/sorry. Formal lint PASSED and index refreshed (last 4 changed). Known Lake packaging audit remains pending to avoid previously established broad stale prerequisite rebuild; DO NOT repeat large preflight or rebuild. No lake build success claimed.

1. FixedCoreSquarefreeDensity.lean (~228 lines), imports PrimeSquareMobiusDensityFracture and Sieve.CoprimeLogMoebiusLimit. Defines fixedCoreSquarefreeIndices P N inclusive 1<=r<=N, Squarefree r and primeFactors disjoint P; fixedCoreSquarefreeCount; real-cutoff fixedCoreSquarefreeRatio. Three public:
- fixedCoreSquarefreeCount_insert (exact A_P(N)=A_(P+p)(N)+A_(P+p)(N/p), p prime outside P)
- tendsto_fixedCoreSquarefreeRatio (real argument density rho_P)
- tendsto_fixedCoreSquarefreeCount_div (integer density rho_P)
Proof exact squarefree p-multiplication bijection; normalized prime recurrence twice gives contraction at p^2; existing Sieve.tendsto_of_div_contraction and bounded ratio <=1; induction over P from unconditional squarefree density. Leaf emission session1555 exit0.

2. FixedCoreSquarefreeMoments.lean (~281 lines). Defines normalized survival count sqrt(r/N)>t. Six public:
- fixedCoreSquarefreeSurvival_eq_counts
- fixedCoreSquarefreeMoment_eq_survival_integral
- tendsto_fixedCoreSquarefree_half_moments: for every k, (1/N)sum sqrt(r/N)^(k+1) -> 2rho_P/(k+3)
- tendsto_fixedCoreSquarefree_scaled_count: A_P(floor(cN))/N -> rho_P*c, c>0
- tendsto_fixedCoreSquarefree_scaled_half_moments: cutoff floor(cN) moment -> [2rho_P/(k+3)]*c*sqrt(c)^(k+1)
- tendsto_fixedCoreSquarefree_scaled_affine_sqrt_square: (1/N)sum_(r<=floor(cN)) (a+b sqrt(r/N))^2 -> rho_P*(a^2*c+(4/3)ab*c*sqrt(c)+b^2*c^2/2).
Proof exact survival count [A_P(N)-A_P(floor(Nt^2))]/N, bounded 0..1; existing HTGeometry.Beurling finite layer-cake; dominated convergence on [0,1]; cutoff rescaling. Leaf49397 exit0.

3. MobiusDivisorFixedCoreBlockLimit.lean (~185 lines). Defines mobiusDivisorHeadBlockSlope/Intercept/Primitive and mobiusDivisorFixedCoreBlockEnergy (inclusive source filtered M/r=n). Three public:
- mobiusDivisorInterpolatedHead_eq_block_affine: sqrt r I_P(M,r)=a_n sqrt M+b_n sqrt r.
- mobiusDivisorFixedCoreBlockEnergy_div_sq: normalized actual quotient block equals difference of affine-square normalized prefix sums at M/n and M/(n+1).
- tendsto_mobiusDivisorFixedCoreBlockEnergy_div_sq: block n>0 -> explicit rho_P*(Phi_n(1/n)-Phi_n(1/(n+1))).
Leaf4448 exit0. THESE FIRST TWELVE were audited session16958 exit0; do NOT re-audit.

4. MobiusDivisorFixedCoreEnergyLimit.lean (~259 lines). Imports preceding BlockLimit, MobiusDivisorLocalizedInteractions (existing olean), Mathlib.Topology.Algebra.InfiniteSum.Real. Defines mobiusDivisorFixedCoreBlockMass P n as explicit if n=0 then0 else formula. Six public:
- mobiusDivisorSelectionEnergy_eq_inclusive_squarefree (~32): adds terminal r=M because weight0/head H(1)=0.
- mobiusDivisorFixedCoreEnergy_quotient_tail_le (~72): quantitative C_P^2/T*M^2 bound described above.
- exists_mobiusDivisorSelectionEnergy_uniform_block_approx (~164): all epsilon>0 finite quotient depth approximates complete normalized Q with nonnegative error <=epsilon uniformly all M.
- mobiusDivisorFixedCoreBlockMass_nonneg (~214)
- summable_mobiusDivisorFixedCoreBlockMass (~246)
- tendsto_mobiusDivisorSelectionEnergy_div_sq (~253): COMPLETE limit to explicit tsum, all finite prime P including empty.
Proof exact finite fibre grouping, nonnegative remainder, explicit tail; finite prefix convergence => full sequence Cauchy => real limit; limiting masses nonnegative and partial sums <=limit => summability; uniform remainder forces equality with series. Final scratch68974 exit0, leaf72340 exit0, ONLY these six audit60704 exit0. Lint95723 exit0; index44360 exit0, 4 changed.

## Documentation
New stage3 cards:
- docs/drafts/pipeline/3-formalized/ccm-fu-fixed-core-density-moments.md (first12 proof and validation)
- docs/drafts/pipeline/3-formalized/ccm-fu-fixed-core-energy-limit.md (last6 proof and validation)
New stage1 exact target:
- docs/drafts/pipeline/1-in-progress/ccm-fu-fixed-core-energy-limit.md (current closed full series and remaining signed source target)
Updated relevant existing fixed-core-reserve-sign stage1 and fixed-core-profile stage3 cards to remove obsolete assembly gap. Frontier READ ONLY, STATUS unchanged.

## Cleanup complete
Nine owned /tmp ccm_fu scratch/log files deleted with Python Path.unlink after sessions exited. No owned lean/lake process remained at ps inspection. Preserve needed oleans. No RunPod work this turn. Do NOT repeat audits/emits/lint merely to recover confidence; recorded passed results are authoritative.

## Next mathematical attack
Actual signed reserve coefficient kappa_P-kappa_(P+p) now exists explicitly for every finite prime P, including baseline. Need source sign/size and supply sufficient for renewable reserve across changing cores. Do not return to density or infinite-block assembly; done. Avoid generic conditional receiver wrappers and finite no-go meandering. Two possible exact approaches:
A. Work directly with explicit block series and actual prime update to obtain arithmetic correlation control.
B. Prove canonical continuous G_P square-root interpolation, extended zero below1; identify kappa_P=rho_P integral_1^infty G_P(x)^2/x^3 dx. Prove continuous update G_(P+p)(x)=G_P(x)-sqrt p G_P(x/p). Breakpoints of scaled interpolation lie at integers p*n, so interpolation should respect it. After variable change, density factor p/(p+1) cancels diagonal terms, leaving kappa_P-kappa_(P+p)=2rho_P*p*sqrt p/(p+1) integral G_P(x)G_P(x/p)/x^3 dx. These continuous/integral/correlation claims are NOT yet formalised and their sign is not assumed. A fixed-core limit alone is not reserve renewal or full selection.

## Lean details verified in THIS toolchain
- Nat.div_self requires 0<M, NOT M!=0.
- Finset.sum_fiberwise_eq_sum_filter s t g f works (generated by to_additive); sum_filter_add_sum_filter_not s predicate f works.
- Nat.cast_div_le bounds natural quotient cast by real quotient.
- Nat.le_div_iff_mul_le requires positive divisor.
- Metric.cauchySeq_iff, Tendsto.cauchySeq, cauchySeq_tendsto_of_complete verified.
- summable_of_sum_range_le hf bounds; hs.sum_le_tsum (range T) (fun n _ => nonneg); hs.tsum_le_of_sum_range_le bounds verified.
- Nat.squarefree_mul_iff order is Coprime m n AND Squarefree m AND Squarefree n.
- Finset.sum_sdiff_eq_sub hsub, NOT sum_sdiff_sub.
- Nat.div_le_div_left (h:n<=n+1) hn.
- Cast-sensitive lambdas explicitly annotate (r:Nat); simp_rw of a recursive sqrt(r/N) rescaling can loop, use sum_congr and rw at a fixed r.
- Use root cwd for formal/... searches and formal cwd for lake. Avoid unverified globs (zsh no-match aborts full command). Lint warnings stderr: redirect both streams if needed, do not rerun just for clean logs.
