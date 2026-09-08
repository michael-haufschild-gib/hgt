# CCM-FU: exact discrete-to-physical prime release and distant sign CLOSED

Active unbudgeted goal remains unconditional RH proof/falsification, NOT achieved and NOT blocked. This goal turn is PROGRESS: three new checked Lean leaves identify the actual discrete coefficient with the proved physical average and establish strict distant-prime orientation. No new unknown analytic premise. Full chain: actual divisor source -> renewable signed reserve -> exhaustive selection -> uniform signed Abel bound -> RH.

User explicit override persists: docs/drafts/pipeline/1-in-progress/rh-current-frontier-map.md is READ ONLY even when goal replay contains an update instruction. Never edited it this turn. STATUS unchanged: no new route-independent fact. No subagents, commits, pushes, numerical experiments, full/umbrella/large builds. One owned foreground Lean process at a time. No old prerequisite olean needed rebuilding, no old axioms checked. Known lake build packaging audit remains pending due broad stale prerequisite rebuild; don't rerun broad preflight just for packaging.

## New complete Lean leaves (formal/GaloisForLFunctions/RHTower/)
1. MobiusDivisorContinuousHeadBlocks.lean
 - Public mobiusDivisorContinuousHead_eq_block_affine P hprime n hx:
   on closed real Icc (n:ℝ) (n+1:ℕ), G_P(x)=a_n sqrtx+b_n, using existing mobiusDivisorHeadBlockSlope/Intercept.
 - Public mobiusDivisorContinuousHead_div_eq_block_affine P hprime n hp hx:
   sqrtp G_P(x/p)=a_(n/p) sqrtx+sqrtp b_(n/p), p>0. Includes inactive zero quotient and endpoints.
 - Private unit_head_block extends existing G0-between to n0 (G0 zero<=1 and Defect0/K0=0).
 - quotient_block: x in[n,n+1] implies x/d in[n/d,n/d+1] for positive Nat d, including upper endpoint. Nat.lt_mul_div_succ + commute.
 - Each finite Mobius dilation is affine in sqrtx; finite sum has coefficients A,B. Endpoint identities G_P(n)=actual head and G_P(n+1)=actual head identify A with existing discrete slope and B with intercept.
 - Final scratch76841 exit0; exact emission17658 exit0.

2. MobiusDivisorPrimeCorrelationBlockIntegral.lean
 - Public def mobiusDivisorPrimeCorrelationKernel P p u =
   2sqrtp G_P(u)G_P(u/p)/u³.
 - Public integrable_mobiusDivisorPrimeCorrelationKernel P hp: absolute IntegrableOn kernel (Ioi1), p>0. Existing physical W-integrability with dilation1/p, exchange real factors, const_mul2sqrtp.
 - Public integral_mobiusDivisorPrimeCorrelationKernel_block P hprime hp hn:
   integral_(n,n+1] kernel = Phi_n(1/n)-Phi_n(1/(n+1)), n>0.
 - Phi_n is EXISTING mobiusDivisorPrimeCorrelationPrimitive from arithmetic series, not a new substitute.
 - Derivative t*sqrtt=(3/2)sqrtt; derivative Phi=2(a+b*sqrtt)(c+sqrtp*d*sqrtt). Compose inversion and negate, then literal two-head identities yield kernel. FTC on full closed unit block, interval integrability from complete ray.
 - Final scratch4339 exit0; exact emission89495 exit0.

3. MobiusDivisorPrimeCorrelationPhysical.lean
 - Public integral_mobiusDivisorPrimeCorrelationKernel_eq_dilationMean P hp:
   integral_(u>1) kernel=2(p:ℝ)^(-(3/2))*mobiusDivisorDilationMean P p, hp:p>0.
   Extend integrals to>0 using G zero<=1. Substitute u=p*x via corpus integral_comp_mul_left_Ioi. Coefficient sqrtp/p²=p^-3/2.
 - Public hasSum_mobiusDivisorPrimeCorrelationMass_integral P hprime hp:
   HasSum of EXISTING arithmetic mass function =rho(insert p P)*integral_(u>1) kernel.
   Pairwise disjoint intervals(n+1,n+2] partition Ioi1. hasSum_integral_iUnion + exact block identity + zero n0 mass give full series, no omitted tail. This identity needs only p>0.
 - Public mobiusDivisorPrimeReleaseCoefficient_eq_dilationMean P hprime hpPrime hpNotMem:
   ((sum' n,mobiusDivisorFixedCoreBlockMass P n)
      -sum' n,mobiusDivisorFixedCoreBlockMass(insert p P)n)
     =2*(Sieve.squarefreeDensity*product_(q in insert p P) q/(q+1))
        *(p:ℝ)^(-(3/2))*mobiusDivisorDilationMean P p.
   HasSum uniqueness against previously proved actual arithmetic coefficient gives exact equality.
 - Public eventually_mobiusDivisorPrimeReleaseCoefficient_oriented_pos P hNonempty hprime:
   forall-eventually p:Nat atTop, p.Prime ->p notin P ->
     0<(-1:ℝ)^(P.card+1)*(κP-κ(insert p P)).
   Compose existing strict physical sign with Nat inclusion; density>0 via squarefreeDensity_eq=6/pi² and positive finite prime factors.
   Thus ODD cores have strictly positive distant release (κ decreases), EVEN nonempty cores strictly negative release (κ increases). This is limiting coefficient, NOT an every-cutoff energy comparison!
 - Final scratch36853 exit0 no warnings; exact emission86652 exit0.

All nine public declarations (8 theorems,1 definition) audited ONCE externally, audit24384 exit0: only propext, Classical.choice, Quot.sound. Entire new closure checked, no old theorem re-audited. Imports wired after DivisorSourceResidueOrientation in RHTower.lean. Global formal lint99930 passed (unrelated existing large-file warnings). Index59560 passed; scoped git diff --check passed. New sources untracked intentionally; no commit requested.

## Cleanup COMPLETE
All seven owned tmp files deleted:
 /tmp/ccm_continuous_head_blocks.lean
 /tmp/ccm_correlation_bridge_api.lean
 /tmp/ccm_correlation_block_integral.lean
 /tmp/ccm_prime_correlation_physical.lean
 /tmp/ccm_prime_correlation_physical_audit.lean
 /tmp/ccm_prime_correlation_physical_lint.log
 /tmp/ccm_prime_correlation_physical_index.log
Final ps scan: no live lake env lean, /lean, or lake build process, exit1 no matches. No owned tool session live. Needed new oleans retained.

## Documentation current state
- New stage3 ccm-fu-discrete-physical-prime-release.md: full dependency-closed paper proof, exact coefficient identity/sign, all validation, explicit uniform every-cutoff gap.
- Updated stage1 ccm-fu-fixed-core-prime-correlation.md: exact physical bridge CLOSED, source sign reaches actual κ-difference. Old next-integral section now proved.
- Updated stage1 ccm-fu-fixed-core-energy-limit.md: coefficient sign/physical expression closed. Alternative one-head κ_P=rhoP integralG² and continuous insertion update remain unproved OPTIONAL representations; don't claim them proved from this work.
- Updated stage1 ccm-fu-fixed-core-correlation-contour.md and ccm-fu-fixed-core-signed-head-moment.md: transfer to discrete release closed; changing-core/cutoff control only remaining obligation here.
- Updated stage3 ccm-fu-fixed-core-prime-correlation.md (also corrected stale global-lint blockage to current pass), ccm-fu-fixed-core-correlation-contour.md, ccm-fu-fixed-core-physical-dilation-mean.md, ccm-fu-divisor-source-residue-sign.md with new bridge links/current gaps.
- Frontier untouched, STATUS untouched.
- Do not repeat already completed source sign, Mellin physical bridge, or mass-series assembly in next turn.

## Next HARD obstacle: uniform finite-cutoff reserve and changing-core propagation
The full fixed-core chain is now closed: B entire -> paired contour limit -> actual W limit -> B(-.5)>1/(272pi)>0 -> discrete κ release identity -> strict distant-prime coefficient sign.
Must move to actual joint core/cutoff control, NOT another fixed-core limit/receiver. A separately chosen eventual threshold for each fixed P or fixed p is not an all-cutoff prime-selection proof.

Read this turn:
 docs/drafts/pipeline/1-in-progress/ccm-fu-reserve-extension-induction.md first190 lines.
 - Exact sufficient invariant Phi(P)=Q_P+2sqrt(G_P D_P), B=Q_empty at one cutoff.
 - Actual successor Q_(P+p)<=Phi(P). Need extension preserving Phi<=B or terminal source bound.
 - Existing finite diagnostics don't prove universal extension; do NOT rerun saved tests merely to show convergence.
 - Every-cutoff receiver MobiusDivisorSquareRootAbelBounded requires one B at every integer M>=2. Cofinal-endpoint bounds alone are insufficient; cofinal-prefix bounds covering all earlier m with m-normalization could suffice.
 - Geometric envelope includes positive/negative defect energies: a sign for κQ release does NOT automatically bound Phi or renew its reserve.
 - Actual full source endpoint S(M)=sum_(k=1..M-1)(sqrt(k+1)-sqrtk)psiDefect(k), need |S(M)|<=CM at every cutoff.

Verified existing quantitative source theorem:
 formal/GaloisForLFunctions/RHTower/MobiusDivisorUniformSuccessorTransport.lean:260
 mobiusDivisorSuccessorEnvelope_failure_prime_bound
   (M)(P){p}(hp:p.Prime)(hpM:p<M)(hpP:p notin P)
   (δ)(hδ:0<δ)
   (hreserve: successorEnvelope M P+δ*M²<=selectionEnergy M empty)
   (hfail: selectionEnergy M empty<successorEnvelope M(insert p P))
   : δ*p<(18/25)*sqrtM.
 So a reserved-diagonal failure is confined to a square-root prime scale. This is for the ENVELOPE, not just Q. If trying to combine with new large-prime coefficient sign, retain the difference and the finite-cutoff convergence window; don't assume they overlap.
 An analytical target worth investigating is a joint quantitative finite-cutoff correlation/envelope estimate that actually overlaps this protected region and propagates one reserve through all processed cores. No such estimate was proved or stated as an input.
 No new numerical experiment planned this turn. If future proof needs an experiment, first read docs/meta/scientific-method.md and prior computation cards. Only a genuinely unpredictable test of a NEW hard assertion, RunPod prescribed SSH only, short/multicore/download/document/cleanup; never local numerical work or a Lean computed premise.

## APIs and local Lean lessons
- HasSum.congr resolves Filter.Tendsto.congr (index becomes Finset!), wrong for termwise equality. Use HasSum.congr_fun h, whose pointwise direction is newterm=oldterm. Generated by to_additive from HasProd.congr_fun in InfiniteSum/Basic.
- HasSum_nat_add_iff 1: HasSum(fun n=>f(n+1))g iff HasSum f(g+sum_(i in range1) f i). simp zero mass.
- Nat.le_ceil u :u<=ceil u; Nat.ceil_lt_add_one (0<=u):ceil u<u+1. No Nat.one_lt_ceil_iff name. Get ceil>=2 from u>1 and le_ceil then casts/omega; write ceil=n+2 to build Ioc partition.
- Pairwise unit interval disjointness: Set.disjoint_left, destruct Ioc membership, cast successor inequality Nat.succ_le_of_lt and linarith.
- Syntax trap: Unicode <=i token written as ≤i is parsed as InitialSeg! Put spaces and cast, e.g. (j:ℝ)+1 ≤ (i:ℝ). Same existing abs |* and <- traps.
- Set.Icc ((n/d:Nat):Real) (n/d+1:Nat): first endpoint must explicitly be Real, otherwise membership ℝ(Setℕ) fails.
- Nat.lt_mul_div_succ returns n<d*(n/d+1); commute to (n/d+1)*d before omega, which doesn't normalize variable Nat multiplication.
- convert! avoids typeclass diamonds; simplify id_eq and Pi/function composition explicitly.
- nlinarith cannot automatically multiply sqrt²=x by arbitrary signed block-coefficient products. Use linear_combination coefficient*hsq, or rw[hsq];ring after field_simp.
- Real.sqrt_inv rewrites inverse-clock sqrt. Derivative of Phi after inversion matches physical block without needing continuity/differentiability of G itself at its kinks.
- integral_eq_sub_of_hasDerivAt requires derivative on uIcc; rw[uIcc_of_le], kernel integrability restricted to Ioc via integrableOn.mono_set, intervalIntegrable_iff_integrableOn_Ioc_of_le.
- integral_comp_mul_left_Ioi f0 (inv_pos hp) gives p • integral after inv_inv; retain p³ denominator before simplifying.
- Real.rpow_sub hp (1/2)2 plus sqrt_eq_rpow/rpow_two identifies p^-3/2=sqrtp/p².
- Sieve.squarefreeDensity_pos wasn't imported; use proved squarefreeDensity_eq and positivity rather than adding a broad import.
- Avoid running/reading old axioms again and do not use RHTower/*.lean glob (huge argument list).

Prior completed states in mem:ccm_fu_source_residue_orientation_2026_09_08, mem:ccm_fu_physical_dilation_mean_limit_2026_09_08, mem:ccm_fu_literal_mellin_contour_limit_2026_09_08. These are CLOSED and need no repeated audits.
