# TG-C9.2/C9.3 audited; next C9.4 actual prime graph core

Goal active/unmet: unconditional actual RH or negation through TG. No subagents, numerical experiments, axioms/holes, heartbeat increases, full/umbrella builds, commits/pushes. Final leaf audits use lake --old env lean. One owned foreground Lean process at a time. Every turn state route, hard gaps and previous-turn progress. Documented corpus search before new conjectures/code; actual source authoritative.

## New production leaf and audit
formal/GaloisForLFunctions/RHTower/PrimeBurnolFourierJetClosure.lean (~420 lines).
Scratch and production command lake --old env lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/PrimeBurnolFourierJetClosure.olean GaloisForLFunctions/RHTower/PrimeBurnolFourierJetClosure.lean pass exit0 without warnings.
Separate import #print axioms audits all five public theorems: only propext, Classical.choice, Quot.sound.
Umbrella import wired; index refreshed. Lint exit1 on11 unrelated unwired RHTower leaves: CCMApertureChainProfile, CCMApertureTranslationChains, CCMExponentialRampPrimeMoment, CCMExponentialRampSourceDissipation, CCMExponentialRampTerminalEntropy, CCMRetainedChainKernelLower, MobiusDivisorCriticalMovingHeadFiniteSource, MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines, ThetaMovingShellFirstOrderPhase, ZetaZeroDensityPowerSaving. No TG error. New-leaf and scoped tracked whitespace clean.
ALL owned processes terminal. ALL /tmp/tg-c92-* scratch/search/audit/log files cleaned with apply_patch. Production olean retained. No remaining build to poll.

## Exact new knowledge
1. private hermite_four_step_summable_zero: nonnegative summable a with (n+3)(n+4)a(n+4)=(n+1)(n+2)a(n) must vanish. For any r, k*a(4k+r) nondecreasing k≥1; numerator identity (4r+2)k+(r+1)(r+2)>0 yields harmonic lower tail. No initial-mode/residue split.
2. burnolJetWeakTest : Schwartz→L physical L2 is actual C²+B², C=creationCLM=2πQ-D, B=annihilationCLM=2πQ+D.
3. burnolJetWeakTest_hermite_tail_kernel: if u annihilates W h_(n+2) for every n, u0. Uses exact Hermite norm recurrence d_(n+1)=(n+1)d_n/π and Bessel energies |<h_n,u>|²/d_n.
4. primeBurnolFourierJetClosedGraph is literally topologicalClosure of range z↦(z,E z), E(f,g)=(f+F g,Mf+FMg), f,g in actual maximal position-square domain. Both input/output projections injective: primeBurnolFourierJetClosedInput_injective and primeBurnolFourierJetClosedOutput_injective (line349).
5. Proof admits actual Schwartz vectors to D(M), proves exact M action and pairing, passes continuous test equations to graph closure via closure_minimal/isClosed_eq. Exact Fourier D² identity and weak Hermite exclusion rule out graph collisions without separately assuming limiting jet integrability.
6. burnolJetWeakTest_no_bounded_leftInverse: bounded T left-inverting W gives u=T.adjoint h0; tail orthogonality forces u0, while Gaussian test contradicts norm positivity.
7. primeBurnolFourierJet_no_bounded_first_recovery (line402): no bounded R:H×H→H recovers first coordinate for ALL full maximal-domain pairs. Exact admitted cancelling pair (Fφ,-φ) has E-output (0,-(8π²)^-1 F(Wφ)); composing R with that channel and F inverse gives forbidden T.

Critical scope: negative theorem is FULL maximal-domain physical carrier. Do NOT assert it already excludes bounded recovery on the literal finite EVEN prime-depth core. Need graph-core density AND correct even restriction. Ordinary L2 density supplies neither. Positive closed-graph injectivity restricts to closed source subgraphs by inclusion. No Gamma–Xi/Hardy/sub-unit consequence proved; RH unresolved.

## Cards/state
P3 docs/drafts/pipeline/3-formalized/tg-fourier-jet-closed-graph.md.
P5 docs/drafts/pipeline/5-failed/tg-fourier-jet-bounded-recovery.md: bounded ambient recovery candidate retired with exact positive survivor (closed graph closable/injective). Original P1 recovery card deleted/moved.
P1 tg-fourier-jet-weak-kernel.md retained as COMPLETE research record pointing to canonical P3; not an active conjecture.
Main log tg-source-conjecture-loop-2026-10-01.md checkpoint through C9.2/C9.3; frontier map TG paragraphs updated.
Next active P1 docs/drafts/pipeline/1-in-progress/tg-fourier-jet-prime-graph-core.md (C9.4). Parent tg-fourier-radial-jet-completion.md updated.

## C9.4 exact next hard proof
For each prime p, prove span of literal graph columns (e_(p,n),M e_(p,n)) is dense in the entire maximal multiplication graph on EVEN physical L2. Then transport to both source coordinates. Also restrict no-recovery proof correctly to even carrier before inferring finite-source obstruction.

Best paper mechanism derived this turn:
- Work half-line first. Let raw f_n=r exp(-(n+1)ell r), ell>0, with actual nonzero Euler amplitudes restored by exact span-scaled identity.
- q_n=(1+r²)f_n=f_n+M f_n. q0 L2 by order0/order2 radial-jet admission; nonzero on half-line. q_n=exp(-ell r)^n q0 (actual Euler amplitudes vary: include their nonzero scalar ratios explicitly).
- Existing integer-Laplace moment determinacy proves q_n span dense in ordinary half-line L2, exactly as BurnolDepthCompletion's orthogonality proof. q0*g L1 by L2 Cauchy–Schwarz; all moments0 force g0 since q0≠0 AE.
- Define bounded rational multiplier graph parametrization G h=(h/(1+r²),r²h/(1+r²)). Both symbols ≤1. Exact AE identities G q_n=(f_n,Mf_n) and G(f+Mf)=(f,Mf).
- Continuity+density gives full maximal graph⊆closure graph span; reverse inclusion uses closedness of maximal real multiplication. No false Hilbert norm on default product, no new weighted-L2 representation needed.
- Transport actual even source via existing even-extension normalization and exact multiplication covariance. Can transport weighted column density and then use even rational graph multipliers; don't silently assume odd directions are generated.
- For even no-recovery, Gaussian is even. Tail proof can include odd Hermite tests by parity/orthogonality of even u; prove this explicitly.

Alternative annihilator paper proof on card: graph orthogonality gives moments of r exp(-ellr)[u+r²v]; L1 from radial0/radial2; moment determinacy gives u+r²v0. More direct G argument avoids choosing Hilbert product geometry.
WeightedDensityL2 also exists/read but is unnecessary for simple positive-resolvent G.

## Relevant actual source read this turn
HTGeometry/BurnolDepthCompletion.lean imports LocalExponentialTestClosure.
- ae_eq_zero_of_integer_laplace_moments {ell}(hell:0<ell){f} (hf:IntegrableOn f(Ioi0)) (∀n, ∫Ioi0 (exp(-ell*t):ℂ)^n*f t=0) → f=ae0.
- burnolDepthFeature ell n t=(t*exp(-((n+1)*ell*t)):ℝ):ℂ.
- memLp_burnolDepthFeature; burnolDepthFeatureL2; burnolDepthFeatureL2_ae.
- burnolDepthFeature_eq_coordinate_pow.
- burnolDepthSpan_orthogonal and dense_burnolDepthSpan (lines190–222) give exact existing proof template.
- burnolDepthSpan_eq_span_scaled.
RHTower/PrimeBurnolDepthCompletion: literalDepthSpan_eq transports nonzero unsquared amplitudes and ell=logp.
RHTower/PrimeBurnolFourierCompletion: actual evenExtension normalization and source density from prior turn.
HTGeometry/WeightedDensityL2 (~226lines) read definitions/headers: positive-density AE equality, memLp_two_withDensity_iff, weightedDensityUnitary. Available if needed.
HTGeometry/MaximalRealL2Multiplication: actual M domain, apply_ae, formal symmetry, isSelfAdjoint and closedness via IsSelfAdjoint.isClosed.

## API details learned
ContinuousLinearMap.adjoint_inner_right A x y: inner x(A.adjoint y)=inner(Ax)y.
fourierUnitary.toContinuousLinearMap is WRONG here (selects finite-dimensional LinearEquiv conversion); use .toContinuousLinearEquiv.toContinuousLinearMap or established .toLinearIsometry.toContinuousLinearMap.
Use Complex.I explicitly in standalone calculations (bare I can resolve unitInterval notation).
Submodule.topologicalClosure_coe, not coe_topologicalClosure.
SchwartzMap.toLp_fourier_eq φ: F(φ.toLp2)=(Fφ).toLp2.
schLp helper abbrev SchwartzMap.toLpCLM ℂ ℂ2volume; map_add/map_smul reliable, direct rw sometimes needs explicit change to toLp.
Orthonormal.inner_products_summable takes vector then orthonormal proof via dot: orthonormal_hermiteSchwartz_toLp.inner_products_summable u.
Public APIs verified in scratch, no recollection-only names.

## Searches
Documented deep queries (results inspected; partial coverage/deadlines explicitly acknowledged):
Hermite orthonormal summable inner recurrence;
bounded inverse dense Schwartz adjoint range Hermite;
exponential depth weighted L2 graph core density.
Last query returned WeightedDensityL2/weightedDensityUnitary. No absence inference. Exact Burnol moment proof found/read via rg and actual source.
