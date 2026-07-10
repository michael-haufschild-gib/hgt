# Positive weighted gap functionals survive masked sampling

- **ID:** arch-theta-sampling-quotient
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rhtower-nogo-positive-content-audit.md`, Candidate C
- **Statement:** For arbitrary masked sample sites, every open sampling gap supports a canonical continuous tent detected by any continuous density that is nonnegative on the gap and positive somewhere inside; the corresponding weighted functional cannot factor through the samples, even nonlinearly.  The theta seam and all consecutive positive-integer-log gaps are specializations.

## Goal

Replace the narrative archimedean pairing no-go by a reusable positive separator theorem.  The theorem names an arbitrary sampling mask, arbitrary sites, an arbitrary gap, a positive continuous weight, and a canonical witness in the sampling kernel.  The actual RHTower theta source is then a direct specialization rather than part of the support proof.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: generic Lean theorem `weightedGapFunctional_not_factors_through_maskedSamples`, theta specialization `archimedeanThetaSeamFunctionalOn_not_factors_through_maskedSamples`, compatibility theorem `archimedeanThetaSeamFunctional_not_factors_through_primePowerSamples`, focused build green, axiom audit clean
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Exact candidate

Let `iota` be an index type, let `active : iota -> Prop` select the active sample indices, and let `site : iota -> R` locate them.  For `a < b`, assume

`active(i) -> site(i) notin (a,b)`.

Define masked sampling and the canonical tent by

`S(phi)(i) = phi(site(i))` when `active(i)`, and `0` otherwise,

`g_(a,b)(u) = max(0, min(u-a, b-u))`.

For a continuous weight `w` that is nonnegative on `[a,b]` and positive somewhere in `(a,b)`, put

`A_w(phi) = integral_[a,b] phi(u) w(u) du`.

Then `S(g_(a,b)) = 0`, `A_w(g_(a,b)) > 0`, and there is no map `F`—linearity not assumed—with `A_w = F composed with S` on continuous real test functions.

For the completed-zeta source,

`w_theta(u) = exp(u/4) (evenKernel(0, exp u)-1) > 0`.

Taking sites `log(n+1)` and the gaps `(log(N+1), log(N+2))` proves nonfactorization even from every positive-integer-log sample, for every `N`.  Prime-power sampling and `(log 2, log 3)` are the original compatibility specialization.

## Proof `[PROVED HERE]`

1. Every active site lies outside `(a,b)`, so the tent vanishes at every active sample; inactive coordinates are zero by definition.  Hence `S(g_(a,b))=0`.
2. The tent is continuous and nonnegative, and it is strictly positive at every point of `(a,b)`.  Multiplication by `w` is nonnegative on `[a,b]` and strictly positive at an interior point, so its interval integral is positive.
3. If `A_w = F composed with S`, then `S(g_(a,b))=S(0)` forces `A_w(g_(a,b))=A_w(0)=0`, contradicting positivity.
4. For consecutive integer logarithms, strict monotonicity of `exp` would turn an intervening sample into an integer strictly between `N+1` and `N+2`, which is impossible.

## Scientific status

- `[BRIDGE]` Support separation itself is classical and is not new scientific knowledge.
- `[BRIDGE]` The exact RHTower identification is stronger than the former no-go narrative because it uses the completed-zeta theta source already tied to the critical Fourier trace, rather than an unnamed “archimedean Gaussian.”
- `[SEARCH]` A future novelty candidate must use this nonzero sampling-quotient class to prove a property not already supplied by classical support separation.  Do not promote the bridge itself as novel.

## Log

- 2026-07-10 — Created in stage 1 from the all-no-go audit.  Selected the canonical gap `(log 2, log 3)` and `xiThetaLogSource` as the actual archimedean source.
- 2026-07-10 — Paper proof completed and formalized in `SeamArchimedeanSamplingQuotient.lean`.  Focused Lean check passed; the two capstones use only `propext`, `Classical.choice`, and `Quot.sound`; formal lint passed.
- 2026-07-10 — Generalized the Lean theorem from the single interval `(log 2, log 3)` to arbitrary masked sites, arbitrary gaps, and arbitrary positive continuous weights.  Added the all-consecutive-positive-integer-log theta theorem; retained the original prime-power declarations as compatibility specializations.
