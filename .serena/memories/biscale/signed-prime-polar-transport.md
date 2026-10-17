# Signed prime–polar transport — 2026-10-17

Mission: quantitative coupling of actual von Mangoldt atoms and both continuum polar branches, retaining signed correlations. Independent BiScaleUncertainty research; do not work on RH, use hgtl7, or run numerical experiments. The attachment `/Users/michael/.codex/attachments/e9ef520a-4498-4562-99e8-1c42812df597/pasted-text-1.txt` governs the active 100-contribution goal; read it if context is missing. Authoritative relocated `formal/GaloisForLFunctions/BiScaleUncertainty/README.md` was read fully, including Trap 10, and is READ-ONLY. Stay on Section 3.3. Construct unconditional explicit producers; apply stencils directly to T(N), never a pre-floor linear counterterm or floored continuum cutoff.

## Goal and verified state

**10/100 substantive packages verified; 90 remain. Goal ACTIVE. Latest turn: verified progress.** Count coherent mathematical packages, not helpers, rescalings, classical moments or reformulations. Ledger: `docs/reports/BiScaleUncertainty/SignedPrimePolarTransport-FACTS.md`. Parent card: `docs/drafts/pipeline/1-in-progress/signed-prime-polar-transport-2026-10-17.md`.

Packages 1–7: C1 annular signed Chebyshev coupling; actual signed source packet and mixed Gram bounds; full-half-line scalar admission; coherent collar Schur constraint; rough-source gauge upper estimate with genuine remainder; exact gauge energy/support budget; optimal fixed-width signed scalar compensation. None proves cutoff-uniform packet control.

Package 8: real-ratio factorial lift, actual atomic sum T(K), both polar moments and harmonic correction. W_N=(R_4N−4R_2N+4R_N)/sqrt N has pairing (2B_N−C_N)/sqrt N with 0≤C_N≤1 and bound (10log(4N+1)+3)/sqrt N. W_N(0)=0, W_N(log4N)=2, so not itself an autocorrelation.

Package 9: continuous clamped-ramp producer S_N with collar 1/(4N), exact positive integer grid preservation, pairing [2B_N−(1+1/(8N))C_N]/sqrt N, bound [10log(4N+1)+3+1/(8N)]/sqrt N and 1≤∫S_N²≤16. Actual C_c object `continuousFactorialProducer (n : ℕ)` with N=n+1; numeric-only main `continuousFactorialProducer_certificate`. Card at `3-formalized/signed-prime-polar-grid-preserving-smoothing-2026-10-17.md`; five direct leaf checks and fourteen standard-axiom audits pass. Historic evidence remains in ledger.

## Package 10 — actual balanced source construction

Paper: `docs/reports/BiScaleUncertainty/SignedPrimePolarFactorialSourceFactorization.md`.
Card: `docs/drafts/pipeline/3-formalized/signed-prime-polar-factorial-source-factorization-2026-10-17.md`.

For N≥1 set A=1+1/(4N), δ=log(A)/3, ε=expδ−1. Let R_N be the continuous factorial ramp stencil with collar ε. Define τδ(t)=max(0,min(t,2δ−t)), ρ_N(t)=exp(t)τδ(t)/ε², F_N(u)=R_N(−u), G_N(u)=exp(u/2)ρ_N(u). These are actual compact continuous sources, pointwise disjoint. Tent mass is one and its exponential moment is [(1+expδ)/2]².

H_N(x)=∫F_N(u)G_N(u+x)du equals the finite causal integral ∫ρ_N(t)exp(t/2)R_N(x−t)dt. Integer separation throughout t∈[0,2δ] proves H_N(log m)=W_N(log m) for every integer m≥1. H is continuous, supported in [0,log(4N+1)], satisfies |H(x)|≤2exp(x/2)/sqrt N, and equals exp(x/2)/sqrt N on the closed top band [log(2N+1),log(4N)]. Thus 1≤∫H²≤16.

Finite-rectangle Fubini evaluates both polar branches: ν(H_N)=[2B_N−a_N C_N]/sqrt N, a_N=[(1+expδ)/2]³∈[1,A]. Atomic sequence is finite and absolutely summable; polar integral is admitted. No discrepancy hypothesis.

Important improvement: raw F±G would cost O(N), but reciprocal scaling c=N^(1/4) preserves every mixed correlation. Set P_N=cF_N+G_N/c, M_N=cF_N−G_N/c. Then J_N=(h_P−h_M)/2=H_N(x)+H_N(−x), hence same grid and pairing, |ν(J_N)|≤[10log(4N+1)+3+1/(4N)]/sqrt N, and 2≤∫J_N²≤32. Since ∫F²≤16 and 6N≤∫G²≤30N, the actual equal origin energies satisfy 6sqrt N≤h_P(0)=h_M(0)≤46sqrt N. This is a signed contrast, not positivity or arbitrary packet control. Origin energy is not archimedean jump energy.

Namespace `GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar`.
Actual objects: `factorialSourceLeft`, `factorialSourceRight`, `factorialSourceScale`, `factorialSourcePlus`, `factorialSourceMinus`, and `factorialSourceProducer`, all indexed by n with N=n+1. Scale is sqrt(sqrt N). `factorialSourceProducer_certificate (n : ℕ)` bundles literal source contrast, equal and two-sided source energies, every grid value, exact pairing and bound, finite/absolute atomic admission, polar integrability, and both contrast L² bounds. Only n:ℕ is an input.

Thirteen final direct `lake --old env lean <leaf> -o <olean>` checks pass with empty logs: ExponentialTentMoments, ExponentialTentSourceEnergy, SignedPrimePolarSourceParameters, ClampedExponentialBranchMoments, SignedPrimePolarRampCore, SignedPrimePolarRampMoments, SignedPrimePolarCausalSource, SignedPrimePolarCausalMoments, SignedPrimePolarCausalEnergy, SignedPrimePolarCausalPairing, SignedPrimePolarSourceFactorization, SignedPrimePolarSourceEnergy, SignedPrimePolarSourceCertificate. Fifteen #print axioms reports use only propext/Classical.choice/Quot.sound. All thirteen imports occur once; index passes and lists endpoint at SourceCertificate.lean:94. Evidence `/tmp/spp10-*-final.log`, `/tmp/spp10_final_axioms.lean`, `/tmp/spp10-final-axioms.log`, `/tmp/spp10-final-manifest.json`, `/tmp/spp10-index.log`, `/tmp/spp10-lint.log`.

Global lint exits 1 for nine unrelated concurrent unwired modules: CenteredRamanujanVarianceAndAbelCofactorCancellation, CoherentKernelSplitting, DivisorAverageChebyshevAndDyadicBlockVarianceProducer, MultiOctaveStepBrickPartitionAndWitnessDyadicPositivity, NyquistWeightCellAsymptotic, NyquistWeightKernel, NyquistWideSourceEnergy, RightNodeCollarPartition, RoutePMVarianceToWitnessSynthesisAndCriticalStripBridge. No package-local error. Preserve other lanes' work. No full/umbrella build, commits/push, or numerical experiment. All owned Lean/search/index/lint processes are terminal. Obsolete spp10 implementation/API scratch files removed; final audit and search evidence retained. README diff is empty.

## Next uncounted candidate

`docs/drafts/pipeline/0-backlog/signed-prime-polar-factorial-archimedean-cost-2026-10-17.md`.
Quantify actual Lévy–sinh jump energies of balanced factorial sources and their signed difference. Candidate rates sqrt(N) log(N+1) for each source, with much smaller signed difference, remain UNPROVED. Source origin-energy bounds alone do not supply the jump-energy domain. Use explicit translation increments of ramps/tents, narrow-tent support for lower bounds, and exact signed contrast for differences; do not truncate the nonlocal energy to a spectral moment.

Inspected `LogarithmicCompressionEnergy.lean` through line111: exact logarithmic tail integral and `biScaleLevyEnergy_le_linear_log_tail` require ContDiff ℝ 2. Existing `FiniteSourceEnergyScalarization.biScaleLevyEnergy_source_parallelogram` also requires C². Our ramps/tents are only continuous; establish concrete increment bounds and integrability. `UnitEnergySmallSources.source_energy_normalization` is scalar normalization, not a new contribution. Inspected `SignedGramTrialCertificate.gramGap_eq_zero_iff` and `QuantitativeGramProducer.quantitativeGramCoefficient_source_energy`; neither is the missing actual-source upper bound.

Search `/tmp/spp10-next-factorization-search.json` is partial with semantic worker disconnected, full file inventory but mostly pending compiler metadata; candidate/source-argument lists empty, prose inspected. Lexical fallbacks `/tmp/spp10-next-factorization-lexical.json` and `/tmp/spp10-next-arch-energy-search.json` return relevant names but omit freshness/coverage metadata. No absence/novelty claim. Broaden prior-work audit before new Lean code. Multiple-collar receiver remains parked.

## Lean workflow and reusable fixes

One owned foreground Lean process at a time. Final direct checks, no full builds or heartbeat increases. Verify new mathlib names in /tmp. #print axioms only /tmp. update_plan unavailable; cards track work. Serena active project cannot extract Lean symbols, so use read-before-edit precise patches. No agents spawned.

Explicit literal function types prevent coercion mismatches. For C_c autocorrelation integrability, specify `(g := (f : ℝ → ℝ))` and give the whole Integrable lambda type. For square integrability, bind `hc : Continuous (fun x => ...)` and `hcomp : HasCompactSupport (fun x => ...)` explicitly before `(hc.pow 2).integrable_of_hasCompactSupport`; this also fixes reflection/Homeomorph coercion and competing zero/measure instances. Typed literal lambda integrability before integral_add/sub rewrites avoids Pi.pow/Pi.sub mismatch.

Use `(mul_le_mul_iff_left₀ (Real.exp_pos t)).mp` to cancel a positive RIGHT factor; `mul_le_mul_right` is a different theorem. In rewrite calls give `(x := -x)` for reflected zero lemmas, or rw may match the unreflected term. HasCompactSupport.mul_left multiplier is implicit `(f := ...)`; mul_right uses `(f' := ...)`. Compact-support subset binder is K. Continuous.intervalIntegrable needs both endpoints. Universal @ API probes may need explicit universe levels `.{0}` or `.{0,0}`.

The causal moment proof reuses `HTGeometry.integral_tiltedTentFullProfile` by translation; not a separate contribution. Private `integral_integral_Icc_swap` is unavailable outside its old module; new finite_rectangle_swap locally proves continuous rectangle Fubini via Measure.prod_restrict. All constructor/branch formulas needed for the next source-energy work are now public in the verified new leaves.


## Latest authoritative checkpoint: contribution 11 complete (2026-10-17)

Supersedes earlier current-count/frontier notes: **11/100 verified; 89 remain; goal ACTIVE**. `SignedPrimePolar.factorialSourceArchimedean_certificate` (only n:ℕ input) proves actual jump-domain admission, sqrt(N) log N individual growth, exact difference -2 integral H_N w with O(log N/sqrt(N)) bound, and normalized logarithmic lower cost. Nine direct leaf checks and eleven standard-axiom audits pass; imports/index updated. Global lint has 22 unrelated unwired modules, no package-local error. All owned processes terminated; API scratch cleaned. README was not edited.

Completed card: `docs/drafts/pipeline/3-formalized/signed-prime-polar-factorial-archimedean-cost-2026-10-17.md`. Full evidence and formulas: `mem:biscale/signed-prime-polar-transport-package-11` and facts ledger. Next uncounted candidate: `docs/drafts/pipeline/0-backlog/signed-prime-polar-factorial-local-packet-2026-10-17.md`; actual localized packet budget must be proved, not assumed. No uniform global packet result follows. Preserve signed arithmetic–polar terms and the finite divisor cap. Continue the same research lane toward all 100 packages.
