# SZ: actual ground global Gamma domain

- **Stage:** 1-in-progress
- **Type:** CONJECTURE; no RH or new Lean result claimed
- **Route:** SZ, canonical-head absolute source sign and first-contact boundary analysis

## Exact target
For every actual restricted Weil operator-domain vector f, prove that its zero extension has full Gamma Fourier multiplier in L2 on the whole line. Specialize to the literal canonical ground, with its interior multiplier equal to the exact scalar--polar--prime forcing and with both exterior boundary operators constructed. Do not assume a global multiplier-domain premise.

## Why this is a missing mathematical step
`CCMRestrictedWeilActualBirmanSchwinger` proves the exact interior weak ground equation. `CCMScrewNullLogRegularity` explicitly leaves the logarithmic multiplier, Dirichlet realization and bounded cross-boundary block outside its Lean statement. `GammaJumpCommutatorH1Bound` proves a smooth-cutoff commutator estimate, not sharp-aperture boundary regularity. Global log-domain admission is needed before using whole-line multiplier identities on the actual ground. It alone is not a sign proof, a physical H1 theorem, or justification for differentiating prime translations under dilation.

## Paper mechanism under audit
The actual Gamma density is rho(h)=exp(-h/2)/(1-exp(-2h)). For h>0, rho(h)<=2/h follows from exp(h/2)>=1+h/2 and exp(-2h)<=exp(-h/2). Across the right boundary x=a+s, y=a-t, its exterior kernel is rho(s+t); the left boundary has the reflected kernel. The corpus Carleman theorem therefore bounds both exterior actions on L2. This is a construction of the actual boundary action, not an assumed estimate on an unknown vector.

To weld this to the global multiplier domain, split global smooth test functions at the sharp aperture. Prove their truncated parts belong to the form domain, identify the full mixed jump pairing across the boundary, and combine the actual interior forcing with the two exterior L2 actions. Fourier duality and Riesz then establish the full multiplier-domain claim. Each analytic identification must be proved; the kernel bound alone does not establish the final claim.

## Corpus evidence
Search1224131,1224144,1224159 were partial, with complete inventories but mostly pending/stale compiler metadata. Candidate lemmas, source arguments, proof ideas, and suggested ingredient sets were inspected; suggested cross-route or RH-equivalent combinations do not discharge this target. Direct reads locate `HTGeometry.CarlemanOperatorBound`, `HTGeometry.ConductorHankelBound`, and the actual mixed Gamma jump identity. No novelty claim follows from missing search hits.

## Status
Global-ground-domain argument remains in progress. Both actual aperture boundary pairings and sharp smooth-test multiplier admission are formalized in `CCMRestrictedWeilGammaBoundaryPairing.lean` and `CCMRestrictedWeilSharpSmoothDomain.lean`. Final leaf audits37470/54474 and all27 public axiom queries17789 passed; standard logical axioms only. See P3 `sz-gamma-sharp-boundary-pairing`. The full ground-domain theorem, canonical-head sign, prime dilation derivative, near-floor cancellation and RH remain open.

## Cross-boundary proof closed in scratch
Write Z for positive-half-line zero extension and R for reflection. For f,g in positive-half-line L2, let Bf(s)=integral over t>0 of rho(s+t)f(t). Carleman domination proves B bounded and the two-variable complex kernel absolutely integrable. The shear (h,t)->(h-t,t), Fubini, and reflection identify integral over h>0 of rho(h)<T_h Zg,RZf> with <g,Bf>. For h>0, <Zg,T_h RZf>=0 by support; translation unitarity and <Zg,RZf>=0 then give <(T_h-1)Zg,(T_h-1)RZf>=-<T_h Zg,RZf>. Thus the actual mixed Gamma jump form equals -<g,Bf>, absolutely. This establishes the analytic boundary identification rather than postulating it.

Sharp test admission is proved by the endpoint-sensitive identity primitive(g')=g-g(-a) on [-a,a]. Adding g(-a) times the actual zero-slope pole recovers the sharp restriction of g. Both summands have the full Gamma multiplier in L2 by existing corpus theorems. This does not claim that an arbitrary ground is H1.

Additional searches1224312 and1224434 were partial (the latter coverage pending), with mainly source-only or unrelated candidates. No ready global weighted-duality theorem was established by these results. The next mathematical obligations remain two-endpoint assembly, dense-test passage, and global multiplier admission for the actual ground.

## Stronger conjecture exposed by the cross-boundary proof

**C-next: arbitrary sharp-cutoff form admission and exhaustion.** The boundary result applies to arbitrary positive-half-line L2 inputs, not only form-domain inputs. For any global finite-Gamma-energy vector v, split v=P v+(1-P)v at a half-line. The exact pointwise quadratic identity says the sum of the two nonnegative diagonal jump energies equals the original jump energy minus twice the real cross term. The cross term is absolutely integrable by the new Hankel identity, bounded in ordinary L2. Thus each diagonal energy is finite. The global Binet--Plancherel energy identity should then construct both weighted form lifts. Two half-line cuts give every finite interval.

This also suggests strong form convergence of growing interval cutoffs: the exterior L2 norm tends to zero; the integrated cross term tends to zero by the uniform boundary operator bound; Fatou on the interior jump energy and the exact decomposition then force exterior jump energy to zero. No global smooth-core density theorem needs to be assumed. This is a stronger statement newly exposed by the proof; it is returned to paper and corpus novelty audit before Lean implementation.

If closed, apply the exact aperture mixed identity to growing sharp cutoffs of arbitrary global form tests. Combine the actual interior weak forcing and the two exterior actions. Form convergence yields a global functional represented by an ordinary L2 vector. The remaining weighted-adjoint calculation identifies the full Gamma multiplier of the actual operator vector. This is the next concrete producer, not an RH-equivalent premise.

C-next corpus audit: search1224581 completed (partial=false), snapshot1224595 inventories65340 files; compiler metadata remains largely pending/stale. Candidate lemmas, source arguments, proof ideas and ingredient sets were inspected. The relevant hit `SuzukiGammaWallCutoffCommutator.gammaJumpKernel_mul_cutoffDiff_le` assumes a Lipschitz cutoff; it is not the arbitrary sharp projection claim. Existing global Binet--Plancherel identity `ccmActualHeadGammaAutocorrelationEnergyL_eq_spectralEnergy` supplies the proposed admission bridge. Exact weight is 1+2*(gammaHardyPhaseRate(2*pi*abs(xi))-gammaHardyPhaseRate(0)); evenness must be used to align it with the spectral energy formula before constructing a weighted L2 lift. No new Lean implementation of C-next has started.

Next proof API, verified by source reads: `CCMArchimedeanDenseFormCore.lean:93` constructs weighted membership using `memLp_two_iff_integrable_sq_norm`, `integrable_withDensity_iff_integrable_smul measurable_ccmArchimedeanFormWeightNNReal`, and `coe_ccmArchimedeanFormWeightNNReal`. The same construction applies to an arbitrary Fourier L2 representative once finite actual Gamma spectral energy and ordinary L2 mass give integrability of weight times norm squared. `integrable_ccmGammaSpectralExcessDensity` and `integral_ccmGammaSpectralExcessDensity_eq_norm_sub` already give the forward direction for every global weighted vector. No recollected API needs to be assumed.
