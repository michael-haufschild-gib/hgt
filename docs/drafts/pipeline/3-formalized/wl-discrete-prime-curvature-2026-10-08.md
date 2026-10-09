# Integer lag: discrete prime curvature

- **ID:** wl-discrete-prime-curvature-2026-10-08
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Lean corpus search only, as explicitly required by user.
- **Goal:** reduce the WL source-bound problem by exposing exact local arithmetic content of lag curvature. The overall goal remains unconditional RH or its falsification.

## Plan

1. Audit existing lag identities and arithmetic increments using corpus search.
2. Prove the precise local recovery identity on paper, then in Lean.
3. Investigate native curvature signs, retaining all archimedean corrections.
4. Audit the leaf with `lake --old env lean`, inspect axioms in scratch, wire umbrella, run lint.

## Conjecture log

- C1: finite signed barycentric lag balance with exact prime compensation. Verdict: BRIDGE, already follows from existing chord/ramp machinery; no source ceiling discharged. Do not present as new scientific knowledge.
- C2: define B(n) = sqrt(n) a_n + n log(n) - S(n), where S is the literal trivial-zero series. For every n >= 2, B(n+2)-2B(n+1)+B(n) = Lambda(n+1)/(n+1). Thus three corrected actual lag observations recover one exact arithmetic weight.
- C3: eventually the uncorrected second difference of sqrt(n) a_n is positive exactly at odd prime powers, and negative at every other index. PROVED HERE and formalized.

## Paper proof of C2

The corpus identity gives B(n) = n(1+gamma) - log(2*pi) + n M(n) - psi(n). The arithmetic increments are M(n+1)-M(n)=Lambda(n+1)/(n+1) and psi(n+1)-psi(n)=Lambda(n+1). Therefore B(n+1)-B(n)=1+gamma+M(n); taking one further difference proves C2. All n used in the lag formula are >= 2. There is no zero-location or unproved analytic premise.

## Paper proof of C3

Write D(n) = sqrt(n+1)a_(n+1) - 2sqrt(n)a_n + sqrt(n-1)a_(n-1), n >= 3. Let E(n) be the same centered second difference of x log x, and T(n) the second difference of S(x). C2 gives nD(n)-Lambda(n) = -nE(n)+nT(n).

The second derivative of x log x is 1/x. Its centered second difference is its second derivative integrated against the nonnegative unit-mass tent on [-1,1]. Therefore 1/(n+1) <= E(n) <= 1/(n-1), giving nE(n) -> 1. Corpus convexity and monotonicity of S give 0 <= T(n) <= 4 S(n-1) <= 8/(n-1)^2 (the last bound is `trivialZeroSeriesReal_le_two_div_sq`). Hence nT(n) -> 0 and nD(n)-Lambda(n) -> -1.

Let delta = min(1-log 2, log 3-1)/2 > 0; positivity follows from 2 < exp(1) < 3. Eventually |nD(n)-Lambda(n)+1| < delta. At a non-prime-power Lambda=0; at a power of 2 Lambda=log 2; both give D(n)<0. At every odd prime power, Lambda=log p >= log 3, so D(n)>0. These exhaust the integers n>=3. No pointwise computation or zero-location assumption is used.

The first identity supplies exact weights, while the eventual native sign law loses the powers of 2. Neither controls the accumulated lag height; that global cancellation remains the RH-strength step.

## Audit boundaries

This is a source identity, not an upper lag bound or an RH proof. External novelty is unaudited because user prohibits external reading. Only Lean source content returned by the corpus search tool may be read during research. No numerical experiments or full builds.

## Lean certificates

- `formal/GaloisForLFunctions/RHTower/WeilLagDiscretePrimeCurvature.lean`: `RHTower.IntegerLagCurvature.corrected_first_difference`, `corrected_second_difference`, `corrected_second_difference_nonneg`, `corrected_second_difference_pos_iff`, `corrected_second_difference_eq_zero_iff`, `scaled_second_difference`.
- `formal/GaloisForLFunctions/RHTower/WeilLagNativeCurvatureSign.lean`: `RHTower.IntegerLagCurvature.logCurvature_bounds`, `trivialCurvature_bounds`, `scaledCurvature_eq`, `scaledCurvature_bounds`, `scaledCurvature_error`, `eventually_scaledCurvature_odd_prime_power_sign`.
- Exact finite estimate: for every integer m >= 3, `abs(m D(m) - Lambda(m) + 1) <= 9/(m-1)`. The proof keeps the full trivial-zero series and actual Mangoldt weights.
- Both leaf modules passed `lake --old env lean`; targeted olean generation passed without warnings. Every public theorem in both modules was checked using `#print axioms` in a scratch file: only `propext`, `Classical.choice`, `Quot.sound`.
- Both modules are imported by RHTower; indexes regenerated. No full or umbrella build was run. Final global lint exited 1 on seven unrelated unwired modules: XiGaussianOneSidedIdentityRH, ApertureConeCalculus, ApertureConeWinding, ApertureLogTranslation, ApertureOpenHistoryIdeal, BoundaryCoronaCStarAlgebra, OneSidedLaplaceAtomRigidity. No proof-debt finding or wiring error for either new module.

## Research assessment and next cycle

The exact corrected recovery is a bridge from the existing explicit formula. The native sign classification refines the local source geometry: powers of two lose their positive corrected curvature after the archimedean terms are restored. Neither local result controls signed accumulation, so no RH-strength source premise has been discharged. External novelty is not claimed.

Next target: the complete signed Green primitive of the native curvature. Search and inspect existing source-bound results before selecting a new conjecture. A sign-only or curvature-only argument must not be promoted to the missing square-root bound; retain the affine boundary terms and full signed arithmetic contribution. The overall RH goal remains active.

## Log

- 2026-10-08: searches found existing barycentric receiver, two-point prime-compensated chord identity, and Mertens increment theorem. C2 paper proof complete; Lean audit pending.
- 2026-10-08: C2 formalized in `RHTower/WeilLagDiscretePrimeCurvature.lean`; both direct `lake --old env lean` audit and targeted olean generation exited 0 with no warnings. Six public theorem axiom checks report only `propext`, `Classical.choice`, `Quot.sound`. Wired into RHTower umbrella; regenerated indexes. Global lint exited 1 on eight unrelated unreachable modules being added elsewhere, with no proof-debt error. C3 scratch formalization is underway in `/tmp/hgt_wl_entropy_bounds.lean`; first check exposed elaboration/algebra presentation issues, now corrected for recheck.
- 2026-10-08: C3 completed in `WeilLagNativeCurvatureSign.lean`, audited directly and through a separate successful axiom-check process. Final global lint has seven unrelated missing imports. Card promoted; temporary probe files removed after verification.
