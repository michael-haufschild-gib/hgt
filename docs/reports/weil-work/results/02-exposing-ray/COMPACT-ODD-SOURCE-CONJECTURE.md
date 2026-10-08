# Next conjecture: compact polar radical approximants with a uniform negative trace tail

Status: OPEN; source proof mechanism to audit, not a Lean theorem. Full exposing-ray matching and energy lower inequality remain OPEN.

Let F=D^3 Phi-(1/4)D Phi. Seek actual odd real C2 polar tests f_L supported in [-L,L], fixed Y,L0, and a quantitative superexponential approximation to F, such that for every L>=L0:

1. crossCorr(f_L,f_L)(y)<=0 for EVERY y>=Y, including the cutoff boundary and all lags above2L;
2. exp(-2*pi*exp(2)*exp(y))<=-crossCorr(f_L,f_L)(y) whenever Y<=y<=2L-4;
3. every integer trace and signed archimedean energy approximate those of F with explicit weighted error, strong enough to compare L=(log N)/2+C with the original exposingTail(N).

The first two assertions are a new constructive source goal suggested by all-order parity. Assertion3 is stronger and must be paid separately. None matches the prescribed negative exposing proportions merely by having negative signs. No negative full Weil energy is conjectured from a negative tail.

## Candidate construction avoiding cutoff derivatives

Use the existing nonnegative even C2 cutoff chi_L, equal1 on [-L+1,L-1] and zero outside[-L,L]. Fix eta(u)=flatBump(17/50,17/1000,u-1)-flatBump(17/50,17/1000,u+1), a real odd compact C2 source, with nonzero half-pole moment by its exact translation multiplier. Define

    f_L = chi_L F - a_L eta,
    a_L = FT(chi_L F)(i/2) / FT(eta)(i/2).

Both moments are real. Oddness gives the other half-pole from the first. Since FT(F)(i/2)=0, a_L is precisely a tail integral; the full theta envelope should make it superexponentially small. This keeps the tail sign of F and supplies exact polar admission without differentiating a cutoff. The literal corpus definitions and all Fourier normalizations must be checked before code.

Choose R containing eta's support and beyond F's fixed right-tail sign threshold. Outside[-R,R], chi_L has a fixed nonnegative sign, so f_L has the same one-sided sign as F wherever nonzero. A common full-series absolute envelope follows from bounded a_L and eta's fixed compact support. For y<=L+R, a central interval of length2 lies in the untouched cutoff plateau once L>=R+4. Its signed main term is the one from DIFFERENTIAL-PARITY-PROOF.md; adverse products require one argument in the compact core and are paid by the same exp(-a exp(2(y-R))) error. For y>=L+R, every nonzero convolution factor has BOTH arguments >=R, by compact support, so the convolution is nonnegative pointwise and odd autocorrelation is nonpositive. This covers the entire transition to zero beyond2L, not just fixed y as L tends to infinity.

[OPEN CORE] Verify a_L real/nonzero denominator, exact C2/support/polar identities, common envelope, plateau/core partition including endpoints, all integer weighted errors, and full signed Gamma-energy convergence. Retain the finite head n<exp(Y), which may have either sign. Those finitely many traces and the exact negative exposing proportions remain additional unsolved endpoint obligations; never discard them.

## Utility and novelty gate

This would construct a family of actual admissible compact sources with a uniform complete tail sign, rather than another obstruction imposed by a repeated spectral lattice. However, if the corpus already supplies this class, use it directly. A finite sign family alone is not significant progress on the exact endpoint unless its signed head and energy budget can be exploited. Before implementation, search the corpus and audit the natural-aperture/vanishing-tail comparison.

## Current corpus/API audit

The literal cutoff is `RHTower.bulkCutoff` in `TruncatedRiemannKernelWeilEnergy`, with `bulkCutoff_nonneg`, `bulkCutoff_le_one`, `bulkCutoff_eq_one` and `bulkCutoff_eq_zero`. The actual complex Fejer source is `RHTower.fejerTest`, defined from `flatBump (17/50) (17/1000)` in `WeilPositivitySummableWeightsObstruction`; there is no verified `fejerTestReal` interface. `truncatedRiemannKernelReal` is currently defined in `WeilFullConeRiemannKernelRigidity`. These locations were found by exhaustive text search after older module locations returned no definition. The corpus `riemannPhiCore` instead uses a sharp indicator and must not be differentiated as C2.

The follow-up compact negative-source deep search was partial, with a complete68,500-file inventory and incomplete compiler/background refresh. Every candidate/source argument and proposed ingredient set was inspected. The returned linear-polar closure and existing positive-source admission cannot prove a negative tail; no absence claim follows.

The corpus already has `contDiff_riemannKernelDeriv`, `contDiff_infty_nearRadicalTest`, `tsupport_nearRadicalTest`, `paperFT_nearRadicalTest_eq` and `norm_W_nearRadicalTest_le` for arbitrary finite derivative combinations. Use these actual near-radical estimates instead of rebuilding generic cutoff calculus. The intended pre-correction source is the K=3 coefficient vector a_1=-1/4, a_3=1, a_0=a_2=0. Its cutoff Fourier defect at either pole is exactly minus the tail transform, because the untruncated source vanishes there. The added core correction's zero-side contribution and all cross terms still need an explicit bound; the existing uncorrected near-radical norm theorem alone does not prove that bound.

## Rate/application gate before investing in a new leaf

The present differential source has no physical shifts. Its theta autocorrelation scale is governed by exp(y), whereas the actual exposing mixture is dominated by its outer unit-shift lag y-2; the existing sharp rate is 2*pi*exp(-2) per integer n. The coarse sign lower bound from cycle14 does not match that rate or target proportions. A negative tail from F alone must not be described as an opposite exposing-ray producer. Audit whether the useful source should instead be the actual odd derivative of `polarShift c riemannKernelReal`, keeping its outer shifts and all k-mixture weights. Its autocorrelation would be minus the second derivative of `polarExposingKernel c`; that identity and its complete weighted error must be established from the corpus, not assumed. The extra derivative changes target amplitudes, so even this refinement does not automatically match -w_N. Prioritize a rate-and-proportion mechanism over another isolated tail-sign theorem.

## Cycle 15 rate/proportion verdict

The strict-width law is now formalized for all fixed finite complex combinations of actual Phi derivatives and their finite mixtures. In particular an unshifted fixed odd differential source cannot itself supply a nonzero multiple of the literal exposing trace on all sufficiently large integers. A compact cutoff approximating that fixed source does not thereby solve the trace discrepancy; any claim that it does must account for the complete additional corrections. The compact tail-sign subconjecture remains OPEN, but isolated sign formalization is DEFERRED in favor of the critical-width four-shift source in CRITICAL-WIDTH-ODD-CONJECTURE.md. The new width law does not rule out growing derivative bases or arbitrary compact polar constructions.
