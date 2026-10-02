# Route SZ: full exponential frequency window and source-piece budgets

RH remains unresolved; active goal unchanged. No subagents/computations/new axioms/heartbeat increases/full builds/commits. One own foreground Lean process at a time. Final leaf command from formal/: lake --old env lean GaloisForLFunctions/RHTower/<leaf>.lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/<leaf>.olean. Preserve unrelated dirty tree. Main working log docs/drafts/pipeline/1-in-progress/sz-source-wronskian-conjecture-loop-2026-10-01.md; main paper candidate sz-bounded-remainder-source-iteration.md. Previous memories: mem:rhtower/sz-prime-polar-polynomial-frequency-2026-10-02 and mem:rhtower/sz-bounded-remainder-arithmetic-inputs-2026-10-02.

## Completed this turn
1. formal/GaloisForLFunctions/RHTower/CCMPolarPrimeExponentialFrequencyCancellation.lean. Imports polynomial cancellation, Sieve.VonMangoldtTwistHalfDensityWindow, and CCMRestrictedWeilCanonicalHeadCompletedErrorControl. Five public theorems:
- abs_polarMultiplier_le_exp_div_frequency {a xi}(ha:0<=a)(hxi:1<=abs xi): abs(polarMultiplier a xi)<=6*exp a/abs xi.
- criticalMellinPrimeCosineModule_eq_halfDensityTwist_re: literal cosine module =2*Re(sum_range(floor(exp(2a))+1) (1/sqrt n) smul vonMangoldtTwist(-xi)n). Zero/one vanish, all prime powers retained.
- abs_criticalMellinPrimeCosineModule_le_halfDensityTwist.
- eventually_abs_criticalMellinPrimeCosineModule_le_exponentialHighFrequency (K eps)(hK:0<K)(heps:0<eps): eventually a forall xi, (2a)^312<=abs xi -> abs xi<=exp(K*a) -> abs primeCosineModule<=eps exp a.
- eventually_abs_polarPrimeStieltjesSymbol_le_exponentialFrequency same final bound on entire abs xi<=exp(K*a) band. This is actual unconditional source cancellation, not a criterion.
Private exact cutoff specialization: L=K+1, X=exp(L*a), M=floor(exp a), N=floor(exp(2a)). (L*a)^(19/20)/a->0 gives xmin<=M including floor loss. log N<=2a<=log2+(La)^2. T0=(La)^311<=(2a)^312 eventually. sqrtM<=exp(a/2); sqrt(N+1)<=2exp a. Prime bound42 exp(a/2)+16 eta expa. Continuous polar term decays high frequency. Polynomial source theorem handles low band.
Scratch1813 and final leaf23736 exit0, no warnings. All five axiom queries91656 exit0: propext, Classical.choice, Quot.sound only. Root umbrella wired near polynomial cancellation. P3: docs/drafts/pipeline/3-formalized/sz-prime-polar-exponential-frequency.md. Route frontier SZ updated.

2. formal/GaloisForLFunctions/RHTower/CCMTruncatedExponentialFourierBudget.lean. Imports CCMRestrictedWeilPolarFourierRegularity only. Definitions ccmTruncatedExponential s l r z := Icc(l,r).indicator(x=>z*(exp(s*x):Complex)); ccmTruncatedExponentialBudget := norm z*exp(max(s*l)(s*r)). Nine public theorems:
- norm_ccmTruncatedExponential_le (all real params)
- integrable_ccmTruncatedExponential
- fourier_ccmTruncatedExponential_eq_interval {l r}(hlr:l<=r)(s)(z)(xi): Fourier atom = z*integral_l^r exp((s-2*pi*i*xi)*x)
- norm_fourier_ccmTruncatedExponential_le hlr s z {xi}(hxi:xi!=0): norm Fourier atom<=budget/(pi*abs xi)
- ccmTruncatedExponential_translate: f(x-h)=atom(s,l+h,r+h,z*exp(-s*h))(x)
- ccmTruncatedExponentialBudget_translate: exact budget invariant under this translation
- ccmTruncatedExponentialBudget_mono_interval hll hlr hrr s z
- norm_fourier_sum_ccmTruncatedExponential_le {iota}(t:Finset iota)(s l r:iota->Real)(z:iota->Complex)(hlr:forall i in t,l i<=r i){xi}(hxi): norm Fourier(sum atoms)<=sum(budgets)/(pi*abs xi), no extra count factor
- ccmTruncatedExponential_restrict: Icc(u,v).indicator(atom s l r z) = atom s (max l u)(min r v) z, also valid for empty intersections.
Scratch23268/30428 exit0. Final leaf4101 exit0, no warnings/errors. Nine axiom queries42237 exit0 with same standard axioms only. Wired root umbrella after polar Fourier regularity. P3:sz-truncated-exponential-fourier-budget.md.

Global lint60973 and final10308 exit1 on 13 unrelated unreachable modules. Final list: CCMApertureChainProfile, CCMApertureTranslationChains, CCMEulerBoundaryKernelShell, CCMEulerBoundaryNonFredholm, CCMExponentialRampPrimeMoment, CCMExponentialRampSourceDissipation, CCMExponentialRampTerminalEntropy, CCMRetainedChainKernelLower, MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines, ThetaMovingShellFirstOrderPhase, ThetaTwoNodePortTransversality, ZetaZeroDensityPowerSaving. Neither owned new leaf reported; do not claim global lint passes or fix unrelated files. git diff --check targeted root umbrella/frontier passes. No full/umbrella builds.

## Next exact hard-source conjecture (same many-moment route)
For every eta>0 and fixed K>0, eventually a, every finite atom representation f supported in [-a,a] with total endpoint budget V satisfies
norm((B_a/c_a) f)<=eta*norm(f)+D*exp(-K*a/2)*V,
and actual output has finite representation budget<=C0*V, aperture/count-independent D,C0.
Actual B=complex scalar*kI + crossed rank-two polar operator - full finite weighted symmetric prime translations (CCMRestrictedWeilBoundedRemainder definitions at ~145,180,207,233). Kernel of crossed polar maps is2cosh((x-y)/2). For budget V, supnorm<=V, each polar coefficient<=2exp(a/2)V => output total budget<=4exp a V. Symmetric prime total coefficient<=42exp a; scalar<=abs(kappa)exp a for a>=0. Actual c>=exp a/2 already audited, so fixed C0=2(abs(kappa)+46). Empty clipped intervals vanish; finite list representation can handle them explicitly. Must weld literal functions to actual Hilbert cofunctions/operator, not replace B with an abstract assumed-regular operator.
Need full-line multiplier/compression identity to obtain the one-step norm estimate, and quantitative L2 Fourier tail. Angular multiplier variable is2*pi*xi; absorb fixed2pi using an extra unit in exponential slope.
Directly read norm_sq_sub_fourierCutoff_central_eq_tailIntegral in SuzukiHlogCompactEmbedding:131: squared cutoff error=integral of complement indicator times norm(unitary Fourier f)^2. New pointwise Fourier bound should give tail squared<=2V^2/(pi^2 R). SoninDecayTailMellin:84 demonstrates integral_Ioi_rpow_of_lt; use reflection for negative half. Neither this L2 tail nor actual finite atom operator closure is yet formalized.
Then H=B/c, p=1_I*sinh(x/2), budget exp(a/2). Set eta=e^-4, R=e^(K*a), K=2log C0+10, n=ceil a. One-step bound + budget gives H^n p=O(e^-7a/2), sum_{j<n}norm H^j p=O(exp(a/2)). u=(1/c)sum(-H)^j p; residual p-(cI+B)u=(-H)^n p. Actual coercive form yields E<=2c normu^2+2norm residual sqrt E, hence bounded odd source energy. Extra Gamma form-domain argument might give physical mass O(a exp(-a)), only paper candidate.
Uniform shifted even/odd energies DO NOT prove signed joint-aperture Wronskian sign, remove shift, or identify Xi. Canonical V2 anchor1 differs from matched1/2. Signed Wronskian, normalization and RH remain open.

## Searches inspected
All partial/source-only, compiler metadata pending/stale; no claim of exhaustive absence.1185711 exponential source confirmed exact polar formula and earlier polynomial/half-density inputs.1185843 broad atom query unhelpful proposed Mellin tail ingredient.1185853 useful HTGeometry/ExponentialPieceFourierDecay integer-frequency unit-interval antiderivative proof and CCMRestrictedWeilPolarFourierRegularity.1185899 convolution query no complete operator weld; suzukiPolarConvolution in SuzukiPolarConvolutionRate uses different suzukiWeilRemainderKernel, not actual rank-two P.1186014 L2 tail query proposed special smooth cutoff + L1 bound, not sufficient. Use direct Plancherel cutoff identity plus inverse-square integration above.

## API lessons verified
Complex.re_sum (not Complex.sum_re); abs_add_le (not abs_add). abs_sub_le takes a,b,c; set middle0 and simp for abs(a-b)<=abs a+abs b. Filter event pullback is hTendsto.eventually hEvent (not .comp_tendsto). Function.comp_def needed to simplify a function-level Tendsto composition before Real.rpow_natCast. add_le_add h le_rfl avoids swapped add_le_add_right instance behavior. Keep floor argument unchanged when using exp a=exp(a/2)^2; nlinarith equality instead of rewriting inside floor. integral_exp_mul_complex works with real interval, complex rate. max_add_add_right verified. Real.fourier_add, Real.fourier_smul, Real.exp_max are invalid and unused; finite Fourier sum proof used actual integral_finsetSum with integrable phase*atom.

All own processes complete. Exact owned /tmp scratch/search/lint files being removed; valid repo leaves/oleans retained. No need to rebuild completed leaves next turn.