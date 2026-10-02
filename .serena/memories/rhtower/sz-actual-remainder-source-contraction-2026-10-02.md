Route SZ active goal is still unconditional Lean RH proof/falsification; RH unresolved. Previous turn made verified progress: THREE new leaf modules prove the exact full remainder multiplier/compression and the actual odd-orbit one-step norm recurrence. No subagents/experiments/added axioms/heartbeat increases/full or umbrella builds/commits/pushes. One own foreground Lean process at a time; final command lake --old env lean <leaf> -o <olean>. No processes currently live; owned tmp files removed, valid module oleans retained.

NEW VERIFIED LEAVES in formal/GaloisForLFunctions/RHTower:
1 CCMRestrictedWeilPolarConvolution.lean (~227 lines), nine public theorems.
Imports PrimeOuterShell, CCMPolarPrimeSourceSign, HTGeometry/L2ConvolutionFourierMultiplier.
ccmPolarConvolutionProfile a := indicator centralInterval(2a) of p_+(h)+p_-(h).
ccmPolarConvolution a := (convolutionKernel profile measurable integrable).op : SoninL2 →L SoninL2.
Public: measurable_ccmPolarConvolutionProfile; integrable_ccmPolarConvolutionProfile; ccmPolarConvolutionProfile_sub; ccmPolarOperator_eq_compressed_convolution; ccmPolarConvolutionProfile_eq_cosh; fourier_ccmPolarConvolutionProfile; ccmPolarOperator_eq_compressed_fourierMultiplier; integral_norm_ccmPolarConvolutionProfile (=8 sinh a); norm_ccmPolarConvolution_le (<=4 exp a).
Compression identity proved for every actual aperture L2 vector via cofunctions, actual support, L2.inner_def. No smoothness restriction.
Exact Fourier profile = (polarMultiplier a (-2*pi*xi):ℂ).
Final audit71723 exit0/no warnings. Wired.

2 CCMRestrictedWeilRemainderMultiplier.lean (~237 lines), seven public theorems.
Imports polar convolution, CCMPolarPrimeExponentialFrequencyCancellation, GroundFrequencyLocalization, CCMFiniteExponentialRemainderTail.
ccmFullLinePrimeOperator a := sum n in Icc2 floor(exp2a), (criticalMellinAtomWeight n:ℂ) • ccmSymmetricLogTranslation(logn).
ccmFullLineBoundedRemainder a := κ•1 + ccmPolarConvolution a - ccmFullLinePrimeOperator a.
Public:
ccmFinitePrimeOperator_eq_compressed_fullLine
ccmRestrictedWeilBoundedRemainder_eq_compressed_fullLine
fourier_ccmFullLinePrimeOperator_ae
fourier_ccmPolarConvolution_ae
fourier_ccmFullLineBoundedRemainder_ae: actual full-line Fourier cofn =ae [κ+(polarPrimeStieltjesSymbol a (-2*pi*xi):ℂ)]*fourierUnitary f.
norm_ccmFullLinePrimeOperator_le <=42 expa
norm_ccmFullLineBoundedRemainder_le <=D expa, D=normκ+46.
All prime powers and original floor cutoff retained.
Final audit23929 exit0/no warnings. Wired.
Optimization lesson: inferred norm-bound chains with many underscores hit default 200000 heartbeats at whnf. Solved by local typed A/P/T and short calc, never raising limits. open HTGeometry shadows add_le_add_right with opposite orientation; use add_le_add h (le_refl ...) instead. Qualified ContinuousLinearMap.comp_apply required. Trig casts are Complex.ofReal_cos / ofReal_sin, NOT cos_ofReal/sin_ofReal; proof uses exp_mul_I, cos_neg/sin_neg, push_cast.

3 CCMRestrictedWeilSourceContraction.lean (~199 lines), THREE public theorems.
Imports actual remainder multiplier.
Private helpers cutoff_norm_le, full_remainder_low_band, source_tail_norm_le, normalized_source_step.
Low-band proof uses Lp.norm_le_norm_of_ae_le on exact Fourier cofn and cutoff, not a model operator.
Tail bound norm(f-Q_Rf)<=2V/(pi sqrtR), from audited squared tail.
Public:
eventually_ccmFullLineRemainder_symbol_small (K ε)(hK:0<K)(hε:0<ε):
 eventually a:ℝ, ∀xi absxi<=exp(Ka),
 norm(κ+(polarPrimeStieltjesSymbol a (-2pi xi):ℂ)) <=(ε/2)expa.
Uses prior exp-window theorem at K+1, ε/4; expa eventually pays 2pi and scalarκ.
eventually_ccmNormalizedWeilRemainder_budget_contraction K ε hK hε:
 eventually a, ∀ha:0<a, ∀f:aperture⟨a,ha⟩, ∀V, Budget f.1 V →
 norm(H f)<=ε norm f+(4D/pi)*V/sqrt(exp(Ka)), where H is actual ccmNormalizedWeilRemainder (prescribed interval shift).
eventually_ccmNormalizedWeilRemainder_odd_norm_recurrence K ε hK hε:
 eventually a, ∀ha:0<a, ∀n,
 let p=(1/2:ℂ)•(pplus-pminus); f=H^[n] p;
 norm(H f)<=ε norm f+(4D/pi)*(C0^n exp(a/2))/sqrt(exp(Ka)), C0=2D.
Actual budget supplied by ccmNormalizedWeilRemainder_odd_iterate_budget; NO assumed source/response regularity premise.
Scratch79461 and final audit94938 exit0/no warnings. Wired.

All NINETEEN public axiom queries82012 pass, only propext/Classical.choice/Quot.sound. Three imports verified exactly once at root umbrella lines18129-18131 (may shift with other work). Final lint29335 exit1 on eleven UNRELATED unreachable modules: CCMApertureChainProfile, CCMApertureTranslationChains, CCMExponentialRampPrimeMoment, CCMExponentialRampSourceDissipation, CCMExponentialRampTerminalEntropy, CCMRetainedChainKernelLower, MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines, SoninTimeBandTaylorSourceDirection, ThetaMovingShellFirstOrderPhase, ZetaZeroDensityPowerSaving. New leaves not reported. Global lint NOT green; preserve unrelated changes.

DOCS:
P3 docs/drafts/pipeline/3-formalized/sz-actual-remainder-source-contraction.md contains exact theorem, dependency-closed paper proof, all audits.
Main docs/drafts/pipeline/1-in-progress/sz-bounded-remainder-source-iteration.md checks off multiplier/compression + actual one-step norm estimate, but remains in progress.
Working log docs/drafts/pipeline/1-in-progress/sz-source-wronskian-conjecture-loop-2026-10-01.md full records.
Frontier-map SZ has new actual source norm recurrence paragraph. Prior P3 orbit card now points to this closure.

SEARCH:
1186552 polar compression partial, semantic coverage unavailable, source-only. Proposed rank-one tensor/aperture ingredient set irrelevant. Lexical follow-up gave exact polarFourierTransform & convolutionKernel.
1186728 band contraction partial/pending, source-only; no ingredient sets. Special Kaiser/packet estimates inapplicable; did retrieve newly audited finite budget tail. Applicable direct mathlib source is Lp.norm_le_norm_of_ae_le, LpSpace/Basic:340.
1186806 next Neumann/source search partial, stale coverage snapshot, unmeasured semantic coverage, source-only. Proposed ingredients positivity+ordinary norm-based Neumann convergence DO NOT supply aperture-uniform source control.
Lexical geom_sum query first page unhelpful, no absence conclusion. Direct rg found Mathlib/Algebra/Ring/GeomSum:232 geom_sum_mul (sum x^i)*(x-1)=x^n-1; 237 mul_geom_sum; 240 geom_sum_mul_neg (sum x^i)*(1-x)=1-x^n. Mathlib/Algebra/Field/GeomSum:43 geom_sum_eq. MUST verify these APIs in /tmp scratch before use.

NEXT HARD ATTACK:
Use proved recurrence, not a new conditional criterion.
Set epsilon=exp(-4), K=2log C0+10, N=ceil(a). Solve d_(j+1)<=epsilon*d_j+L*C0^j exp(a/2)/sqrt(expKa).
Simple induction bound d_j<=epsilon^j*d0 + L*C0^j exp(a/2)/(sqrt(expKa)*(C0-epsilon)) (overestimate at j=0 harmless). C0>=92.
Need norm p<=exp(a/2), then d_N=O(exp(-7a/2)), sum_{j<N} d_j=O(exp(a/2)).
Actual pole norm facts:
CCMRestrictedWeilCanonicalHeadCompletedErrorControl:143 norm_sq_ccmPolarApertureVector_half a =2sinh a.
same:172 norm_sq_ccmPolarApertureVector_neg_half =2sinh a.
CCMRestrictedWeilPolarSourceCancellation:22 inner_ccmPolarApertureVector_opposite a s =2a.
Thus norm((pplus-pminus)/2)^2=sinh a-a, <=exp a; verify norm subtraction identities in scratch.
Finite Neumann u=(1/c)sum_{j<N}(-H)^j p, residual r=p-(cI+B)u=(-H)^N p. Use finite polynomial identity/telescoping, no infinite-norm uniformity premise.
For actual Riesz response E=q(v)=Re<p,Jv>, q>=<A Jv,Jv>, q>=norm(Jv)^2, A=cI+B>=I:
E<=<Au,u>+2 normr sqrtE<=2c normu²+2 normr sqrtE.
IMPORTANT u only needs physical L2 here, NOT Gamma operator/form-domain membership. expa/c<=2 bounds first term. Small apertures E<=normp².
Actual source weld sources:
SuzukiTaCoalescingCovarianceTangent:117 def suzukiTaRawCoalescingOdd; 128 def suzukiTaCoalescingOddEnergy; 177 suzukiTaRawCoalescingOdd_inner a c w:
inner rawOdd w = inner ((suzukiApertureCoordinate a.2.le).sinhVecC c) (suzukiTaPhysicalEmbedding a w).
:211 suzukiTaCoalescingOddEnergy_eq_norm_sq (located, signature needs read).
SuzukiTaHilbertSpace:82 physical embedding = suzukiWeilIntervalFormEmbedding.comp suzukiTaToFormCLM.
Existing exact unitary maps suzukiTaExponentialL2 a s to ccmPolarApertureVector a s, from suzukiApertureZeroExtendL2_exponential_eq_ccmPolarL2Vector. Keep this transport for sinhVecC(1/2).
Norm intervalB >=norm physicalB was proved inside CCMRestrictedWeilPolarShiftLower; may need export/reuse for A positivity. Actual source c is norm(intervalB)+1. Don't silently switch shifts.

After uniform matched odd energy: signed Wronskian/cusp cancellation, canonical V2 anchor1 versus matched1/2 normalization, shift removal and Xi identification still open. Bounded shifted even/odd energies alone do not prove these or RH.
Prior memory mem:rhtower/sz-finite-exponential-remainder-orbit-2026-10-02 retains representation/tail details and earlier arithmetic chain.
