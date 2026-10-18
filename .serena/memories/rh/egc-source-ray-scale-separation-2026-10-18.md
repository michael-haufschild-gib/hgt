# EGC source-ray scale separation — verified 2026-10-18

Goal remains unconditional RH in Lean; RH OPEN. Rotated from RFHM to EGC, a different source/contour mechanism. EWJ reconnaissance only. Do not count this component as goal completion or as outer-contour orientation.

## Exact result

For the original prescribed EGC source ray, every fixed shift eps and real offset x in PaperEGCSmallParameter satisfy
(m+1) * paperEGCCompleteCorrection eps x (-(m+1)) -> -eps^2/2.
For eps=paperEGCScale n this is exactly the original source-only centeredPrimeArchRealShiftDiagonalExtractor (paperEGCSourceRayPoint x m) n. No extra analytic hypothesis. Therefore its scaled limit cannot be zero for any n; o(1/m) of the unrenormalized source is false.

The positive survivor is arithmetic and coefficient-faithful. For sigma>1 and arbitrary real x, eps:
C = B + R,
B = i eps/2 [logDeriv archFactor(sigma+i(x+eps)) - logDeriv archFactor(sigma+i(x-eps))],
R = LSeries a(sigma),
a(n) = -i eps/2 * Lambda(n) * [n^(-i(x+eps))-n^(-i(x-eps))].
Every prime-power coefficient is retained. The norm bound |a(n)| <= |eps| Lambda(n) yields, for sigma>=sigma0>1 and M=sum Lambda(n)n^(-sigma0),
|R| <= |eps| 2^(-(sigma-sigma0)) M,
|R-a(2)2^(-sigma)| <= |eps| 3^(-(sigma-sigma0)) M.
Both estimates hold uniformly across ALL real frequencies x. 2^sigma R -> a(2) for each fixed eps,x. At x=0, a(2)=-eps log(2) sin(eps log(2)), strictly negative for 0<eps<=1; consequently the centered arithmetic remainder is eventually strictly negative.

Gamma mechanism: t=m+1. For Re a,Re b>0,
t[digamma(t/2+a)-digamma(t/2+b)] -> 2(a-b).
Positive real log factorization plus derivative at 1 handles the log term. Corpus Stirling defect gives |t defect|<=24/t. Each reciprocal term t/(t+c)->1, so paired pole contributions cancel. Actual half-Gamma factor gives -eps^2/2; arithmetic part is exponentially negligible at this scale.

## New modules / main theorems

- formal/GaloisForLFunctions/BiScaleUncertainty/LogGridUniformDirichletTail.lean: norm_logGridTerm_le_geometric, lSeries_geometric_bound_of_support, lSeries_logGridTail_bound. Generic coefficient majorant plus finite head deletion supplies admission and full vertical-line budgets.
- formal/GaloisForLFunctions/BiScaleUncertainty/HorizontalGammaDifference.lean: tendsto_natScale_log_one_add, tendsto_natScale_div_shift, tendsto_natScale_digamma_pair.
- formal/GaloisForLFunctions/RHTower/PaperEGCArithmeticRay.lean: paperEGCCompleteCorrection_source_ray_split, norm_paperEGCRayArithmetic_le, norm_paperEGCRayArithmetic_sub_first_prime_le, tendsto_paperEGCRayArithmetic_first_prime, paperEGCRayCoeff_centered_two, eventually_paperEGCRayArithmetic_centered_re_neg.
- formal/GaloisForLFunctions/RHTower/PaperEGCSourceRayBaseline.lean: tendsto_natScale_paperEGCRayArithmetic, tendsto_natScale_paperEGCRayArch, tendsto_paperEGCCompleteCorrection_source_ray_scaled, tendsto_paperEGCSourceExtractor_scaled, not_tendsto_paperEGCSourceExtractor_scaled_zero.

Card: docs/drafts/pipeline/3-formalized/egc-source-ray-scale-separation-2026-10-18.md. Dependency-closed paper proofs written before Lean. Scoped no-go and strongest positive survivor both audited. EGC remains live; expanding-real-coordinate outer covariance/sign still unpaid. Results use fixed shifts; no joint shrinking-shift uniform asymptotic asserted. The baseline and arithmetic sign do not distinguish on/off-line zeros.

## Verification

All four canonical lake --old env lean leaf checks exited 0. No warnings/errors; Gamma log has an informational ring tactic suggestion. All 23 public theorem #print axioms reports passed with only propext, Classical.choice, Quot.sound. All 57 mathlib API probes passed. Both theorem-area umbrellas import the new leaves. git diff --check passed. Four source hashes revalidated after final edits.

Global scripts/formal_tools.py lint exited 1, only seven unrelated concurrent orphan modules:
BSU OddPrimeSieveFamilies, SieveMomentFourier, SixthValuationPhaseRecovery, ValuationTripleResonance;
BVI JordanUpperBoundAndGcdOrbitPrimitiveEnergy, PowerDampedRenormalizedDefectAndPronicCeiling, RenormalizedMobiusDefectAndFirstOctaveCancellation.
No new EGC leaf flagged. Do not claim repository-wide lint clean.

Evidence retained: /tmp/hgt-egc-{grid,gamma,arithmetic,baseline}.log; /tmp/hgt-egc-ray-axioms.{lean,log}; /tmp/hgt-egc-lint.log; /tmp/hgt-egc-ray-source-sha256.txt; /tmp/hgt-egc-ray-audit-manifest.json. Search JSONs: /tmp/hgt-egc-outer-search.json, /tmp/hgt-ewj-admission-search.json, /tmp/hgt-egc-ray-input-search.json. Deep search source inventory complete but compiler coverage mostly source-only, semantic coverage unmeasured; generated suggestions irrelevant. Used lexical hits and verified exact source.

All owned Lean/search/lint process handles terminated normally. Removed obsolete /tmp/hgt-egc-ray-api.lean and .log after merging probes into final audit. No full/umbrella builds, numerical experiments, web, commits/pushes, or edits to read-only frontier/framework READMEs.

Lean lessons: use Function.comp_def when simplifying a composed FUNCTION inside Tendsto/HasDerivAt; comp_apply alone does not expand an unapplied composition. Explicitly type the derivative of log at the inner function value before composing. ArithmeticFunction.vonMangoldt_nonneg takes n implicitly. Use norm_mul after LSeries.term_smul_apply when scalar multiplication reduces to complex multiplication. Cast numeric bases explicitly with a local equality before rewriting Complex.ofReal_cpow or ofReal_log. gammaRealLogConnection is in GaloisForLFunctions, not RHTower.