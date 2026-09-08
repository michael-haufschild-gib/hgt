Active unbudgeted all-congruence Selberg 1/4 goal remains UNPROVED. Prior goal turn and this turn are genuine progress; no blocked audit progression. Never mark goal complete from these source interfaces. Latest substantive steering remains whole-corpus idea search -> conjecture -> prove/fail -> pivot. Full parent card: docs/drafts/pipeline/1-in-progress/selberg-quarter-conjecturing-loop.md. It contains cycle22 live target. No task-owned live handles at checkpoint.

Completed cycles20–21:
1) formal/GaloisForLFunctions/RHTower/SelbergMaassBoundaryTrace.lean
Namespace GaloisForLFunctions.RHTower.SelbergMaassTrace.
Imports SelbergMaassFourierModes, SelbergBesselBoundaryOperator, DeningerFourierKothe.
Actual source coefficient_weighted_bound: every positive-height trace has C>=0 with (1+|n:R|)^2*norm a_n<=C. Derived from the prior squared-frequency bound k_n²*norm a_n<=M: divide by (2pi/w)², use nonzero integer |n|>=1 and (1+|n|)²<=4n²; C=4L+norm a0 includes0.
coefficient_norm_summable uses root RHTower.deningerFourier_summable_inv_sq. coefficient_normSq_summable from norm a<=C and summable norm a. coefficient_gradient_summable from k²*norm a²<=M*norm a.
frequency_eq_abs_signed: Bessel frequency(log(N+1))n = |signedFrequency(N+1)n|, actual cast/exponential normalization.
coefficient_frequency_summable from k<=1+k².
boundaryTrace N f T: actual coefficient sequence at y=expT, bundled in complex l2. formTrace N f T: same sequence in operator FormDomain(log(N+1)).
maass_boundary_decomposition (line159): literal outgoing seam series = principal-frequency series minus Re inner(C trace,trace).
maass_seam_summable actual signed seam series.
No omitted source data beyond the existing seam's explicit0 coefficient; the actual sequence retainsa0.
Scratch /tmp/selberg_maass_trace_domain.lean; names /tmp/selberg_trace_domain_names.lean.
Stage3 docs/drafts/pipeline/3-formalized/selberg-actual-maass-boundary-trace.md.
Scratch/direct checks passed; targeted final build passed one target, log /tmp/selberg_maass_trace_build.log.

2) formal/GaloisForLFunctions/RHTower/SelbergMaassParseval.lean
Namespace GaloisForLFunctions.RHTower.SelbergMaassParseval.
Imports SelbergMaassFourierModes + DeningerFourierBridge (does not depend on new Trace module).
private slice_memLp from actual slice continuity, compact bound and MemLp.of_bound on finite Ioc.
private slice_normSq_intervalIntegrable uses Complex.continuous_normSq.comp(slice_continuous...).
coefficient_eq_fourierCoeffOn: literal normalized interval coefficient equals Mathlib fourierCoeffOn on0..w. Kernel equality from root RHTower.deningerFourierKernel_eq_fourier.
coefficient_mass_hasSum from actual hasSum_sq_fourierCoeffOn.
coefficient_horizontal: one integration by parts gives coef(dxF)=signedFrequency*I*coefF.
maass_mass_hasSum: sum normSq a =w^-1 integral normSq f.
maass_horizontal_hasSum: sum signedFreq²*normSq a =w^-1 integral normSq dxF.
maass_vertical_hasSum: sum normSq(actual deriv a) =w^-1 integral normSq dyF.
quarterSlice N f y: literal horizontal integral of normSq dxF + normSq dyF -(1/(4y²))*normSqF.
modalQuarter N f y n=normSq deriv a_n +(signedFreq²-1/(4y²))*normSq a_n.
maass_quarter_hasSum to w^-1*quarterSlice; maass_quarter_energy_identity (line178) quarterSlice=w*tsum modalQuarter. All y>0, actual C2 Maass source, no modal ansatz/extra spectral hypothesis.
Scratch /tmp/selberg_maass_parseval.lean; names /tmp/selberg_maass_parseval_names.lean.
Stage3 docs/drafts/pipeline/3-formalized/selberg-maass-quarter-parseval.md.
Scratch/direct checks passed; targeted final build passed one target, log /tmp/selberg_maass_parseval_build.log.

Verification:
Both modules wired in RHTower umbrella. Eighteen capstones (10Trace including data constructions,8Parseval) in /tmp/selberg_trace_parseval_axioms.lean report only standard propext, Classical.choice, Quot.sound. No added axioms/admissions/numerical experiments. All task Lean checks/builds serialized.
Index refreshed /tmp/selberg_trace_parseval_index.log;0changed because concurrent corpus refresh had already indexed sources. Explicit corpus searches returned both modules' capstones afterward.
LATEST repository-wide lint PASSED with existing large-file warnings, log /tmp/selberg_trace_parseval_lint.log. Prior7unwired errors were resolved externally; earlier failing logs are historical. Task-file whitespace checks passed.
All task-owned Lean/Lake handles terminal. Other agents' CoppoQuarticClockApplications/PhysicalObserverSpectralRealization and /tmp/ccm_terminal_recovery.lean were running at audit, not touched. Shared tree has many unrelated modified/untracked files; preserve them. No task commits. No full/umbrella builds.

NEXT cycle22 paper chain is recorded but no source/scratch yet:
Corpus idea sources actually read: HTGeometry.WaveEnergyFlux (lines90–172) uses actual PDE + Green integration by parts to expose flux; HTGeometry.PeriodicCuspBoundaryGap (first85lines) supplies first-frequency holomorphic cusp mechanism BUT its holomorphic premise does not apply to Maass, so do not reuse its conclusion.
Define normalized actual mass M(y)=1/w integral|F|² and flux J(y)=1/w Re integral Fy*conjF; G(y)=1/w integral(|Fx|²+|Fy|²).
First target: actual derivatives M'=2J, J'=G-lambda*M/y², hence quarterSlice/w=J'+(lambda-1/4)M/y². Use real C2 chart, periodIntegral_hasDerivAt on F*conjF and Fy*conjF with real-part map, and one horizontal integration by parts. F and Fx periodic source helpers already public in SelbergMaassFourierMean. Complex conjugate derivative and C1 product API names must be verified against actual toolchain in scratch.
Then test quantitative decay for exceptional0<lambda<1/4: prior constant coefficient vanishing (SelbergExceptionalCuspMean) and new horizontal Parseval give G>=k1²M, k1=2pi/w. On y>=Y=1/k1, candidate M''>=k1²M. Source cusp filter givesM->0. Nonnegative convexity should forceM'<=0; integrating factor for W=M'+k1M has W'>=k1W, and W<=k1M->0 rules out W>0. Then (exp(k1y)M)'<=0 gives M(y)<=M(Y)exp(-k1(y-Y)). Proposed only, not used. Convexity plusM->0 should also forceJ->0; flux identity would then give finite tail gradient energy. No infinite-height interchange, full-cusp quotient measure/core response/globalSelberg proof yet.

Useful current APIs:
Public mean helpers: directional_contDiffOn, point_horizontal/vertical, slice_horizontal/vertical/continuous, directional_periodic. maass_periodic N f x hy. f.2.2.1.1 actual ContDiffOn R2 chart; f.2.2.1.2 sourcePDE. Root RHTower differs from GaloisForLFunctions.RHTower.
Actual coefficient_hasDerivAt/second, horizontal_second, modalEquation, uniform coefficient decay, inverse-square bound are in prior Modes; see mem:selberg/compact-boundary-and-actual-fourier-modes-2026-09-08.

Toolchain lessons:
Summable.of_nonneg_of_le takes nonnegative target, pointwise comparison, summable majorant. Use refine ... ?_ ?_ hs for predictable goal order.
Deninger invsq is zpow -(2:Z); rw zpow_two makes product x*x, so add pow_two to match ordinarysquare.
HasSum.congr_fun exists and expects desired summand = old summand.
For integral kernel equality dsimp only before rw to expose beta redexes.
Continuous.norm.pow2 gives a function-power expression that simp Pi.pow_apply did not resolve inside IntervalIntegrable. Direct Complex.continuous_normSq.comp works.
For physical interval sums, prove integrability of each normSq slice, then intervalIntegral.integral_add/sub/const_mul and ring.
Only lake env lean file for scratch/direct, targeted lake build module for final; one task Lean worker at a time, await terminal handles. No computations or full umbrella builds. New modules must be wired.
