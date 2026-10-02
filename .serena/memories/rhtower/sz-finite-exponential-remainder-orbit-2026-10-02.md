Route SZ goal remains ACTIVE: unconditional Lean RH proof/falsification; RH unresolved. No subagents, computations/experiments, added axioms, heartbeat increases, full/umbrella builds, commits/pushes. Single own foreground Lean process at a time. Final command lake --old env lean <leaf> -o <olean> from formal/. Preserve unrelated dirty tree.

NEW VERIFIED:
1. formal/GaloisForLFunctions/RHTower/CCMFiniteExponentialRemainderOrbit.lean (461 lines; 18 public theorems).
Imports CCMTruncatedExponentialFourierBudget, CCMRestrictedWeilPrimeOuterShell, CCMRestrictedWeilPolarShiftLower, PrimeMassSharpUpper.
RHTower.CCMFiniteExponentialBudget : SoninL2 → ℝ → Prop, inductive actual zero/atom/add/smul/mono representation; atom arbitrary real s and nonempty [l,r], cofn =ae ccmTruncatedExponential.
Class namespace public nonneg, ae_norm_le, integrable, ae_norm_fourier_le, neg, sub, finset_sum, translate, cutoff, polar, norm_pole_charge_le, polar_operator, prime_atom, prime_operator, remainder, normalized_remainder.
Translation invariant budget, interval cutoff decreases budget (empty interval handled). Polar actual crossed rankOne budget <=4 exp(a)V: each charge <=2 exp(a/2)V, avoiding aperture-length loss. Entire prime sum budget <=42 exp(a)V using primeMassHalf_le_sqrt. B budget <=(norm κ+46)exp(a)V.
ccmNormalizedWeilRemainder a : aperture →L aperture := (actual prescribed Suzuki interval shift c)^(-1) • actual B. c>=exp(a)/2.
ccmNormalizedWeilRemainder_odd_iterate_budget a n: actual H^n ((1/2:ℂ)•(pplus-pminus)) has budget C0^n exp(a/2), C0=2(normκ+46), no extra premise.
ccmNormalizedWeilRemainder_odd_iterate_fourier a n: ae ξ≠0, norm(L2 Fourier orbit ξ)<=V_n/(pi abs ξ).
Final audit35153 exit0 no warnings, olean retained.

2. CCMFiniteExponentialRemainderTail.lean (two public theorems).
Imports orbit + Mathlib.Analysis.SpecialFunctions.ImproperIntegrals.
CCMFiniteExponentialBudget.fourier_tail_sq_le hf hR: norm(f-fourierCutoff[-R,R]f)^2<=2 V²/(pi² R).
ccmNormalizedWeilRemainder_odd_iterate_tail a n hR: same for literal H^n odd pole source with V_n as above.
Positive half via integral_Ioi_rpow_of_lt at -2, negative via reflection, norm_sq_sub_fourierCutoff_central_eq_tailIntegral. No extra tail assumption.
Scratch11198 and final audit13836 exit0, no warnings; olean retained.
All TWENTY public theorem axiom queries52666 pass, only propext/Classical.choice/Quot.sound.
Both wired beside CCMTruncatedExponentialFourierBudget in root RHTower.lean. No umbrella build.
P3 card docs/drafts/pipeline/3-formalized/sz-finite-exponential-remainder-orbit.md. Frontier map SZ updated.
Main active card docs/drafts/pipeline/1-in-progress/sz-bounded-remainder-source-iteration.md now checks actual orbit closure + quantitative tail. Working log docs/drafts/pipeline/1-in-progress/sz-source-wronskian-conjecture-loop-2026-10-01.md updated.
Final lint66480 exit1 on 12 unrelated unreachable modules: CCMApertureChainProfile, CCMApertureTranslationChains, CCMExponentialRampPrimeMoment, CCMExponentialRampSourceDissipation, CCMExponentialRampTerminalEntropy, CCMRetainedChainKernelLower, MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines, SoninCutoffMonomialDilation, ThetaMovingShellFirstOrderPhase, ThetaTwoNodeSignedSturmEnergy, ZetaZeroDensityPowerSaving. Neither new leaf reported. Global lint not green.

CORPUS SEARCH:
1186086 actual class closure: partial/source-only, no applicable rank-one ingredient set. Usable ccmApertureCompression_val, ccmApertureSymmetricTranslation_coeFn in PrimeOuterShell; complete generic cofn translation sum in PrimeTransportPoleSchurNorm:260.
1186271 multiplier/convolution: partial, coverage pending, relevant hits all source-only; no ingredient sets/proof ideas. Useful HTGeometry/L2ConvolutionFourierMultiplier.convolutionKernel_op_eq_fourierMulCLM (file read first190 lines). Existing .olean verified present.
Search mandatory before new topic/Lean; use documented research command directly, no help/source prep. Miss≠absence.

NEXT HARD ATTACK (not more criteria wrappers):
Prove actual full-line multiplier/compression identity then one-step norm contraction.
g_a(h)=1_[-2a,2a](h)*2 cosh(h/2); at x,y in aperture, g_a(x-y)=exp(x/2)exp(-y/2)+exp(-x/2)exp(y/2).
Use support of f from indicatorCutoff_suzukiApertureHilbert and L2.inner_def to prove compression of (convolutionKernel g_a).op equals actual crossed rank-two ccmPolarOperator. SchurKernel.op_coeFn:169, apply:54, ae_integrable:104 in HTGeometry/SchurKernelOperator (only those symbols located).
Exact polarFourierTransform_eq_polarMultiplier in CCMPolarPrimeSourceSign:158, profile definition152. Full symmetric integral with exp(i ξ h). Mathlib Fourier at frequency t gives polarMultiplier(a,-2*pi*t); this .olean exists.
Translation Fourier formula in CCMCoherentMidpointFourier:18 private fourier_logTranslation_ae, via public MellinL2.fourier_additiveTranslation and MellinL2.fourierPhaseMulAux_ae. File first58 lines read. Full prime sum uncompressed translations must retain all terms/cutoff. κ atom retained.
HTGeometry/L2FourierMultiplier.norm_fourierMulCLM_le:191; Fourier multiplier definition179, apply184. L2ConvolutionFourierMultiplier gives actual convolution/multiplier equality.
CCMRestrictedWeilPolarMultiplier is a DIFFERENTIAL pole-annihilator, not desired convolution bridge; don't confuse.
Low band: proved exponential-frequency polar-prime cancellation, absorb 2*pi by enlarged fixed exponent. High band: new tail and global convolution norm <=(normκ+46)exp(a); after division by c fixed cost C0. Contraction estimate expected norm(H f)<=eta norm(f)+C0 sqrt(2)*V/(pi sqrt R), eventually aperture.

MANY-MOMENT PAPER (main card):
Fix eta=e^-4, K=2log C0+10, R=e^(Ka), n=ceil a.
Budget V_j=C0^j exp(a/2). One-step recurrence yields norm(H^n p)=O(e^-7a/2), sum_{j<n}norm(H^j p)=O(e^(a/2)).
u=(1/c)sum_{j<n}(-H)^j p, r=p-(cI+B)u=(-H)^n p.
Actual Riesz E=q(v)=Re<p,Jv>, q(v)>=<A Jv,Jv>, q(v)>=norm(Jv)^2, A=cI+B>=I. Positivity yields E<=<Au,u>+2 norm(r)sqrt E<=2c normu²+2normr sqrt E, uniform since expa/c<=2.
IMPORTANT u only needs physical L2 for this argument; do not add unnecessary Gamma operator/form-domain admission premise. Coordinate/source weld still must be exact.
Small aperture E<=normp² suffices.
Still open after this selected target: signed Wronskian, canonical V2 anchor1 vs matched1/2 normalization, shift removal/Xi identification, RH. Bounded shifted energies alone prove none of these.

All own processes complete. Exact owned scratch/search/lint files from this turn removed at checkpoint; valid module oleans retained. No failed repo Lean leaf remains. Earlier compiler errors were coercion/proof-focus syntax, not mathematical falsifications.
Prior context: mem:rhtower/sz-prime-polar-exponential-frequency-2026-10-02; mem:rhtower/sz-bounded-remainder-arithmetic-inputs-2026-10-02; mem:rhtower/sz-matched-even-source-bound-2026-10-02.
