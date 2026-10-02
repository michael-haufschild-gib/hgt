# Route SZ: actual matched odd-source gap closed

Goal remains ACTIVE: unconditional Lean proof/falsification of RH via SZ, RH unresolved. No subagents, computations/experiments, added axioms, full/umbrella builds, heartbeat changes, commits/pushes. Continue corpus-driven hard research. Every turn state route, hard gaps, prior contribution. One foreground Lean at a time; final audit `lake --old env lean <leaf> -o ...` from formal/. Do not redo passed audits without changes.

## New verified leaves (all paths formal/GaloisForLFunctions/RHTower/)
1. CCMRestrictedWeilFiniteNeumannSource.lean: final leaf34076 exit0/no warnings, wired. Defs ccmMatchedOddPoleSource=(pplus-pminus)/2 and ccmShiftedBoundedWeil=c*I+B with exact prescribed interval shift. Three public theorems:
- norm_ccmMatchedOddPoleSource_le: norm p<=exp(a/2).
- eventually_ccmMatchedOddPoleSource_finite_orbit_bound: exists M,R>0, eventually a, for all ha>0, n=Nat.ceil a, norm(H^[n]p)<=R and sum_{j<n}norm(H^[j]p)<=M exp(a/2).
- eventually_ccmMatchedOddPoleSource_neumann_approximation: exists M,R>0 eventually a forall ha exists physical u, normu<=M exp(a/2)/c and norm(p-(cI+B)u)<=R. Literal finite alternating sum, exact residual. No assumptions on unknown response.
2. SuzukiMatchedOddSourceBound.lean: final leaf87048 exit0/no warnings, wired. Two public theorems:
- suzukiTaCoalescingOddEnergy_half_le_exp: actual odd energy<=exp(a) for every positive aperture.
- exists_suzukiTaCoalescingOddEnergy_half_uniform_bound (line175): exists C>0 forall positive aperture a, suzukiTaCoalescingOddEnergy a (1/2)<=C. NO HYPOTHESIS BINDERS. Actual unscaled energy, matched anchor1/2, actual prime-polar-Gamma source and prescribed interval shift.
All five public axioms29754 passed, only propext/Classical.choice/Quot.sound. Root #check confirms literal premise-free statement. Both imported exactly once in RHTower umbrella; no umbrella build.

## Proof
D=normκ+46,C0=2D,L=4D/pi,q=exp(-4),K=2logC0+10,n=ceil a,E0=exp(a/2),eta=L E0/sqrt(expKa). Actual recurrence yields d_j<=q^j E0+eta C0^j. Geometric sums: norm residual<=R=1+LC0; sum norms<=M E0 with M=1/(1-q)+LC0. u=c^-1 sum (-1)^j H^[j]p, exact p-Au=(-1)^n H^[n]p. Actual source weld e(sinhVecC(1/2))=p. w=actual raw odd response, f=Jw, E=normw²=Re<p,f>. E=GammaNorm²+Re<Af,f>, A=cI+B>=I. Positivity on f-u and symmetry yield E<=2c normu²+2 normr normw. expa<=2c gives E<=4M²+2R sqrtE, hence E<=8M²+4R². Source Cauchy-Schwarz gives E<=expa on remaining bounded aperture range. No Gamma-domain membership is required for this physical test u.

## Next hard target, corpus-based paper candidate
Physical response decay O(a exp(-a)), then signed shift/mass cancellation. Need Gamma admission of actual finite Neumann vector plus quantitative residual. For any finite-exponential budget V and R>=1, candidate exact inequality:
Ilog(f)=integral(1+max(log|xi|,0))*|Fourier f|² <= (1+logR) normf² + (2V²/pi²)*(logR+2)/R.
Low part Plancherel, each tail exact integral of (1+logx)/x² plus proved Fourier envelope V/(pi|xi|). Proves weighted-L2 admission itself. For actual u, V_u<=exp(a/2)*C0^ceil(a)/c; normu<=M exp(a/2)/c; R=exp((2logC0+10)a). Gamma energy O(a exp(-a)); tail O(a exp(-11a)). Quantitative residual d_n<=exp(-7a/2)+LC0 exp(-9a/2) must be exported explicitly from the finite recurrence; the current public uniform residual bound alone is insufficient.
After actual form lift g with Jg=u, z=w-g has q(z)=Re<r,Jz>-Re<g,z>_Gamma. Since q pays both Gamma and physical mass, q(z)<=2(normr²+normg_Gamma²), giving physical mass norm(Jw)²=O(a exp(-a)). This does not by itself settle the complete signed Wronskian or growing-shift combination.
Verified source locations: CCMArchimedeanLogWeightEquivalence:58 ccmArchimedeanFormWeight_le_logComparison; CCMArchimedeanFormDomainEquivalence:128 weightedToL2 transport,184 ccmLogFormToArchimedean. CCMArchimedeanHilbertFormDomain:91 withDensity measure;142 norm_sq_ccmArchimedeanFourierL2;230 form domain is support-defect kernel;254 physical aperture map. Relevant portions read. New code for next conjecture NOT started.

## Search
Deep finite-Neumann search1186930 partial/source-only, Xi Gaussian ingredient set inapplicable. Energy lexical no hits then broadened any-term retrieved actual odd source and exact energy identities, no compiler metadata. Gamma search1187063 partial/source-only, semantic coverage unmeasured; retrieves actual truncated-exponential Fourier envelope, not admission theorem. No absence claims.

## Code lessons
For complex aperture lemmas, give full vectors to inner_smul_left/right and norm_inner_le_norm. Even specifying field/vector may not let rw match RCLike.re/Complex.re or CLM coercions. Bind fully typed local equalities first (hself:(inner C f f).re=normf² and hB:inner C (Bf)u=inner C f(Bu)), then rewrite them. No heartbeat increase. Avoid dsimp unfolding iterate before iterate_succ rewrite; use change. Qualify Finset.sum_range_succ. Use all_goals rather than redundant tactic sequencing that closes goal then runs ring.

## Docs and verification
P3: docs/drafts/pipeline/3-formalized/sz-matched-odd-source-bound.md.
Active continuation: docs/drafts/pipeline/1-in-progress/sz-bounded-remainder-source-iteration.md (initial uniform target marked closed; next physical decay).
Working log: docs/drafts/pipeline/1-in-progress/sz-source-wronskian-conjecture-loop-2026-10-01.md.
SZ map updated with closure and stale open claims corrected.
Lint38433 exit1: twelve unrelated unreachable modules CCMApertureChainProfile, CCMApertureTranslationChains, CCMExponentialRampPrimeMoment, CCMExponentialRampSourceDissipation, CCMExponentialRampTerminalEntropy, CCMRetainedChainKernelLower, MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines, SoninPrimeSquareCorrectionNuclear, ThetaMovingShellFirstOrderPhase, ThetaTailConfluentCenterGram, ZetaZeroDensityPowerSaving. Neither new leaf flagged. Global lint NOT green. Targeted tracked whitespace check passed. Preserve unrelated dirt.
All own processes terminal. All ten exact owned /tmp search/scratch/lint files removed successfully; valid two leaf oleans retained. No goal-complete or blocked update made.

Beyond physical decay remain complete signed Wronskian/cusp cancellation, canonical V2 normalization, shift removal, Xi identification and RH.