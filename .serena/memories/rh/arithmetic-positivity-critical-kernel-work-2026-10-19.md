# Arithmetic Positivity Theory — PAUSED, 2026-10-19

Latest user instruction: finish started Lean work, wire imports, update docs, then pause. Completed. User cleared the persistent goal; get_goal returned null. Do not resume conjecturing or create a replacement goal without a new request. Accepted significant-result count remains 0/100. No hgtl7 skill, subagents, numerical experiments, added axioms, heartbeat increases, full/umbrella builds, commits, or pushes. README remained read-only.

## Durable state
Main card: docs/drafts/pipeline/1-in-progress/apt-critical-prime-kernel-signature-2026-10-19.md. Its top status is PAUSED. It contains the paper arguments, complete reuse/search audit, final verification, all eight checked arithmetic certificates, and the unresolved negative-coercivity plan. Keep this card in 1-in-progress because sign/coercivity remains OPEN.
Parent card: docs/drafts/pipeline/3-formalized/apt-critical-translated-prime-form-2026-10-19.md. Updated to link the continuous representative and exact weight-mass support identities to the paused successor.

## Completed support leaves
Directory: formal/GaloisForLFunctions/arithmetic-positivity-theory/.
- FactorialCriticalPrimeCumulativeCharge.lean: 248 lines, 11 public declarations. H_N=sum_{1<=m<=N} A(m)/m^3; zero iff N<=1, negative iff 2<=N<=4, positive iff N>=5, strict positive margin log(2)/150 from five. Absolute charge bound and summability, cumulative convergence. Earlier targeted/direct/axiom/index checks passed. Do not retest unchanged.
- FactorialCriticalPrimeKernelDensity.lean: 339 lines, 17 public declarations. gamma(u)=u^-2(1-cos(2*pi*u/12)); D=gamma*H_floor. Exact closed-tail Fubini, integrability, real L1 periodization, reflection, and full translated prime form=(4/pi^4) integral D*Q=(4/pi^4) integral_Ioc(0,1) Rraw*Q. Earlier targeted/direct/17-axiom/index checks passed. Do not retest unchanged.
- FactorialCriticalPrimeContinuousKernel.lean: 187 lines, 8 public declarations. K(t)=sum_{k>=0}H_(k+1)*gamma(k+1+t), continuous on [0,1] by uniform inverse-square majorant. P=K on (0,1). Rcont=(K(t)+K(1-t))/2 is continuous, matches endpoints and Rraw on (0,1), and gives exact complete translated-form integral.
- FactorialCriticalPrimeKernelMass.lean: 202 lines, 4 public declarations. Singleton pattern mass=b(j)^2*existing factorialCriticalHarmonicDefect(m); gamma=(pi^2/72)*sincSq(u/12) for u>0; integrability; exact integral_(0,infinity) gamma*Q=(pi^2/12)*sum b(j)^2. Reuses HTGeometry.BandLimitedPositiveConfiguration.integral_cexp_mul_sincSq_scaled_eq_zero; no duplicate general Fourier theorem.
All four leaves are wired in formal/GaloisForLFunctions/ArithmeticPositivityTheory.lean. Continuous and Mass imports are at lines 36 and 37 at closure.

## Final closure verification
Both actual new files compiled via lake --old env lean -o <actual .olean> <actual .lean>, with status 0 and empty logs:
- /tmp/apt_critical_prime_continuous_kernel_actual.{log,status}
- /tmp/apt_critical_prime_kernel_mass_actual.{log,status}
Combined actual-import #print axioms covered all 12 public declarations, exactly matching the source declaration sets: /tmp/apt_critical_prime_kernel_closure_axioms.{log,status}, status 0. Each uses only propext, Classical.choice, Quot.sound.
Combined mass scratch, explicit mathlib API probes, and eight exact arithmetic examples passed with empty log: /tmp/apt_critical_prime_kernel_closure.{log,status}, status 0. API probes needed explicit universe levels for generic integral lemmas. integral_re and integral_comp_abs are global names, not MeasureTheory-qualified. Real-part proof simplifies Complex multiplication before commuting scalar factors.
scripts/formal_tools.py index passed: /tmp/apt_critical_prime_kernel_closure_index.{log,status}. Refreshed LEAN_API.md, LEAN_GAPS.md, LEAN_OVERVIEW.md. All 12 declarations were checked individually, exactly once under their actual modules. API rows contain unqualified declaration names plus module columns, not fully qualified theorem names.
Source whitespace, forbidden-declaration/heartbeat scans, and scoped git diff --check produced no errors. No full or umbrella build was run.

## Global lint remains non-green
scripts/formal_tools.py lint --check-generated returned 1: /tmp/apt_critical_prime_kernel_closure_lint.{log,status}. 381 existing large-file warnings and exactly six unrelated reachability errors:
- BiScaleUncertainty.SieveLocalVisibilityClassification
- BiScaleUncertainty.SievePrimePowerLocalRegularity
- BiScaleUncertainty.SieveVisibilityPhaseSeparation
- BiScaleUncertainty.SieveVisibilityRadialEstimates
- TransHorizonIncidenceMechanics.FermiBoundedPrimeCapacityObservability
- TransHorizonIncidenceMechanics.FermiFinitePrimeAntichainBound
No APT or stale-generated-file error. Preserve these foreign writers' modules; do not fix their wiring as part of this paused APT task.

## Build recovery and cleanup
The original targeted continuous build expanded changed transitive artifacts for ~48 minutes. It and the --old retry were terminated by their verified owned process groups (30588, 46559), exits 143 and no remaining descendants. Neither is a passing build. First direct check then exposed missing transitive artifacts. A targeted --old build of six identified BiScale/RHTower dependency leaves completed successfully: /tmp/apt_finish_missing_dependencies.{log,status}, status 0. No foreign source was edited. Actual-file and axiom audits above followed recovery.
All owned build/search/check sessions are finished. Six completed scratch source files were deleted: apt_critical_prime_continuous_kernel.lean, apt_critical_prime_continuous_kernel_actual_axioms.lean, apt_critical_prime_kernel_mass.lean, apt_critical_prime_negative_budget.lean, apt_critical_prime_kernel_closure.lean, apt_critical_prime_kernel_closure_axioms.lean (all under /tmp). Their logs and corpus-search JSON are retained. All eight arithmetic statements/proofs were copied into the paused card before deletion.

## Search and mathematical limits
Extensive corpus research searches were used, with candidate/source screening and exact-name lexical pagination. Detailed evidence paths are on the card. Relevant existing work includes real L1 periodization; band-limited sinc-square Fourier identities; existing factorialCriticalHarmonicDefect; Sonin sine-current identity; degree-five/seven sine bounds; logarithmic inverse-cube integral and antitone integral-test framework; complex exponential and monomial Laplace integrals. No absence/novelty inference from missing hits or unmeasured coverage.
Last search /tmp/apt-critical-kernel-sine-laplace-prior.json finished with partial=true, coverage pending, background refresh incomplete, runtime deadline, and malformed local-model JSON during judging. All 20 candidate and 20 source-argument statements were screened. connes_sinDiv_eq_laplace and laplace_sineKernel are possible later ingredients; their applicability is not compiler-checked here. Do not repeat the search merely to claim absence.
The proposed uniform negative coercivity is NOT proved. Native analytic harmonic estimates, exact charge-to-budget reductions, quantitative cumulative bounds, curvature estimate, and infinite-tail controls remain open. The eight Lean-checked arithmetic examples establish only arithmetic implications, not those premises. No negative witness, route retirement, RH consequence, or significant-contribution credit is claimed.
If explicitly resumed, use the card's proposed J_m and Laplace/Taylor estimates, singleton mean bound -log(2)/300, and reflected-kernel deviation bound T/12 as conjectural obligations. Existing NIST DLMF 6.7.13/14 already give the classical sine/cosine Laplace ingredients, so those ingredients are not novel. Audit actual native sign/coercivity and independent novelty/significance before counting anything.