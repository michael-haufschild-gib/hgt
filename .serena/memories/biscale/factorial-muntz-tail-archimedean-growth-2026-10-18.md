# Actual correction-tail logarithmic Weil growth — complete

## User scope / stop condition
The user cleared the persistent RH goal, then explicitly requested: "finish what you have started to not leave half done code behind". Completed exactly the three already drafted leaves, verification, wiring, research card, and handoff. Do not automatically start another research branch, resume RH research, or create/update a goal. RH and the original ramp's mixed-term problem remain unproved.

Card: docs/drafts/pipeline/3-formalized/factorial-muntz-tail-archimedean-growth-2026-10-18.md. The former stage-1 card was moved, parent link repaired. Parent docs/drafts/pipeline/1-in-progress/factorial-ramp-diagonal-margin-2026-10-18.md records the completed result and finish-only scope.
Predecessor: `mem:biscale/factorial-muntz-tail-primitive-suppression-2026-10-18`.

## Completed modules
All files under formal/GaloisForLFunctions/BiScaleUncertainty; namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar.

1. ExpDecayFourierMass.lean — six theorems: expDecayTest_integrable, expDecayTest_exists_fourier_bound, expDecayTest_fourier_sq_integrable, expDecayTest_fourier_mass_trunc_tendsto, expDecayTest_fourier_mass_eq, expDecayTest_fourier_sq_gamma_integrable. For any ExpDecayTest F, prove L1 membership, uniform Fourier decay for truncations and F, Fourier-square integrability, dominated convergence of Fourier mass, exact noncompact Parseval integral |FT(F)|² = 2*pi*integral F², and gamma-weighted integrability. Existing compact truncations, Fourier convergence, and autocorrelation convergence supply the bridge. Uniform mass majorant is M²*(1+|r|)^(-2); gamma majorant uses exponent -3/2.
SHA256 3a45a9391597b7934df01a9834f3fd86e49ae1c212200904a805226c980003ac.

2. FactorialMuntzTailArchimedeanGrowth.lean — two definitions (factorialMuntzTailArchEnergy, factorialMuntzTailArchLoss) and four theorems: factorialMuntzSmoothedTail_fourier_mass_eq, factorialMuntzSmoothedTail_arch_integrable, factorialMuntzSmoothedTail_arch_quarter, factorialMuntzSmoothedTail_arch_log_lower. Applies the analytic bridge to actual smoothed correction tails U_(n,k). Integrates RHTower.exposing_archimedean_scalar_quarter after discharging Fourier, primitive, and gamma integrability. Gamma/symbol identification comes from RHTower.WeilPoleWeight.gammaBracket_eq_archimedeanWeilSymbol.
SHA256 bcd05284627048026fa84489730cd716357e78ba92eb30a0c088474d2763a709.

3. FactorialMuntzTailWeilGrowth.lean — one definition factorialMuntzTailWeilLoss and four theorems: factorialMuntzSmoothedTail_weil_log_lower, factorialMuntzSmoothedTail_weil_coercive, factorialMuntzSmoothedTail_weil_log_rate, factorialMuntzSmoothedTail_weil_eventually_pos. Combines the actual archimedean lower bound with the verified literal prime/pole mass budget.
SHA256 dce445390bdf29b625bef988f2fd428fce0ad436e41610d9dc1f9b1cc9b6f690.

## Exact mathematics / limitations
N=n+1; m=integral U²; M=integral |FT U|²=2*pi*m; P=integral |FT U|²/(r²+1/4)²; A=(1/(2*pi))*integral |FT U|²*gammaBracket.
For every n,k,b: (b-C0+1/4)*m <= A + exp(b)^4/(8*pi)*P, where C0=RHTower.ExposingRayPrimitive.coercivityConst.
Predecessor gives P<=C/N³ for every n,k, C=32*(360*exp(1))²*pi, and m>=1/(512*N) eventually in k for each n. Taking b=log(N)/2 yields exp(b)^4=N² and (log(N)/2-C0-64*C/pi)*m<=A.
Actual prime/pole error is at most K*m, K=512*(factorialMuntzTailPrimeBudget+144*exp(1)²). D=C0+64*C/pi+K.
Thus for each n, eventually k: (log(N)/2-D)*m <= Re W(U,U).
For every real B, eventually n, eventually k: B*m <= Re W(U,U).
Eventually n, eventually k: log(N)/(2048*N) <= Re W(U,U), and separately strict positivity is proved. The threshold in k may depend on n. These are actual-source theorems with no remaining compact-support, RH, or all-source Weil-positivity premise.
The original ramp's mixed Weil terms and sufficient coupled diagonal margin remain open. Do not use positive-form Cauchy–Schwarz for the indefinite Weil form without proving positivity. Tail-family positivity does not establish all-source RW or RH.

## Verification / exact gate outcome
All three direct leaf commands used lake --old env lean -j 1 with emitted oleans; all exited 0 with empty logs:
/tmp/bsu-exp-decay-fourier-mass-leaf.log
/tmp/bsu-tail-arch-growth-leaf.log
/tmp/bsu-tail-weil-growth-leaf.log
Combined API and exhaustive #print axioms scratch /tmp/bsu-tail-arch-axioms.lean exited 0. All 17 public declarations (14 theorems, 3 definitions) use only propext, Classical.choice, Quot.sound. Output /tmp/bsu-tail-arch-axioms.log.
Each module is imported exactly once in formal/GaloisForLFunctions/BiScaleUncertainty.lean. Guarded /tmp/bsu-tail-arch-finish.py exited 0, verifying final source hashes, all 17 axiom records, exact import counts, empty leaf logs, and all formalized-card links. Inventory /tmp/bsu-tail-arch-verification.json. Four predecessor hashes matched (ReadoutDecay, PrimitiveEnergy, Mass, PrimePolarBudget). Scoped git diff --check passed.
Guarded scripts/formal_tools.py index exited 0; /tmp/bsu-tail-arch-index.log. Generated API/gaps/overview and search index refreshed.
Guarded scripts/formal_tools.py lint --check-generated exited 1, with 381 existing large-file warnings and exactly six unrelated concurrent umbrella-reachability errors:
- BiScaleUncertainty.ThreePrimeScalarPhaseCollision
- BezoutValuationIncidence.ActiveDeletedMartingaleAndShiftedEulerConvergence
- BezoutValuationIncidence.ArithmeticLagSchedulesAndSharpRecoveryHorizon
- BezoutValuationIncidence.RamanujanLagCoefficientAndTotientQuotient
- BezoutValuationIncidence.TrueTranslationPredictionAndExactCompression
- BezoutValuationIncidence.ValuationVisibilityClockAndRamanujanSupport
No error names these three completed leaves; no forbidden-declaration or generated-freshness error. Log /tmp/bsu-tail-arch-lint.log. Unrelated work was preserved. All own Lean and guarded jobs are terminal; no full umbrella build, commit, or push.

## Reuse notes
Current toolchain uses mul_le_mul_iff_left₀ for cancelling a positive factor on the right; mul_le_mul_left takes an inequality and is not the cancellation equivalence. Verified actual API in /tmp scratch.
In arch_quarter final normalization, field_simp rewrites integral integrands; finish with all_goals ring_nf after convert/first rfl/field_simp. This avoids redundant-ring errors and warnings and passed with empty diagnostics.
Research search /tmp/bsu-tail-arch-search.json completed partial=false/errors=[], with all 20 candidate and 20 source-argument summaries inspected. Compiler coverage was mixed and refresh incomplete due background indexing; not an exhaustive compiler-fresh search. No web/novelty or numerical experiment claim.
