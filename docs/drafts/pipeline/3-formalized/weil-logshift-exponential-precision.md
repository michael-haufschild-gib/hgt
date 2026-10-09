# Exponentially shrinking observation errors still permit divergent moments

Status: formalized and audited. Corpus-only research, 2026-10-09.

## Proved result

For every 0<=sigma<4-pi, every bounded recovery-history center h0, and every epsilon>0, there exists a bounded history h with

|h(k)-h0(k)| <= epsilon exp(-sigma(k+2)) for every k,

whose absolute reconstructed moment terms are unbounded in every tail at every real shift. In the closed unit ball of bounded error parameters u, mapped to h=h0+epsilon exp(-sigma(k+2))u, such parameters form a dense residual set in the supremum topology. Eventual boundedness or signed summability at any history-dependent shift is meagre in that parameter ball.

## Corpus evidence

The previous uniform-ball increment proves divergence under arbitrarily small uniform errors. Its dense residual set cannot automatically be pulled through the non-open exponentially decaying multiplication map. The earlier smooth-edge diagonal proof, however, has freely chosen rates a<pi and b>2pi, with resulting inverse response exponent a+4-b. Direct local research and exhaustive `WeilLogShift*.lean` searches found no existing exponential-history-precision theorem. No external sources consulted.

## Dependency-closed paper proof

1. Given sigma<4-pi, choose max(0,sigma+2pi-4)<a<pi, then 2pi<b<a+4-sigma. The existing kernel envelopes and exact smooth cutoff estimate give c>0 and gamma=a+4-b>sigma with D_k>=c exp(gamma(k+2)) eventually. Therefore exp(-sigma(k+2))D_k tends to infinity.
2. For sigma>=0, q(k)=exp(-sigma(k+2)) defines a bounded continuous history with 0<q(k)<=1. Multiplication by q is a continuous linear map on bounded histories. The affine perturbed history H(u)=h0+epsilon q u has weighted moment coordinates T_n(u)+b_n, where T_n is continuous linear and b_n is the center's moment. Its kth origin diagonal response is epsilon q(k)D_k, hence diverges for epsilon>0.
3. Generalize the already-proved opposite-coordinate perturbation argument to any affine coordinate family T_n+b_n with diverging kth diagonal response. Inside every positive-radius closed parameter ball, every strict tail event is open dense. The geometric ball-preserving and distance estimates are unchanged; affine baselines cancel exactly.
4. Apply completeness and Baire to the error-parameter unit ball. Countably many thresholds and tail cutoffs give unbounded origin terms generically. Existing outward kernel comparison transfers this to every real shift simultaneously. Eventual boundedness or summability at even one shift is meagre.
5. Unit-ball error parameters satisfy |u(k)|<=1, so H(u) obeys the required pointwise exponential precision envelope. Nonempty dense family provides the final history for every center and epsilon.

## Scope and implementation

- Generalize the existing origin diagonal rate proof; retain its existing theorem as the zero-rate specialization.
- Generalize the existing uniform-ball constructive theorem to affine coordinates; retain its original moment theorem as a specialization.
- Reuse the origin-to-all-shifts implication by exposing its existing proved statement.
- New leaves will define the exponential envelope, affine perturbation, scaled response, and their category consequences.
- Audit every public theorem in modified and new leaves. No new unproved analytic assumptions or axioms; only parameter-domain restrictions in final results.

## Limits

No claim at sigma>=4-pi or that this rate boundary is optimal. No every-error, one-sided-origin, generic norm-to-infinity, exact-prefix-preservation, full real-cutoff, or RH conclusion.

## Formal results and verification

- `WeilLogShiftOriginDiagonalDivergence.lean`: new lower envelope above every rate below 4-pi; original positive-envelope theorem retained as the zero-rate specialization.
- `WeilLogShiftUniformBallPerturbation.lean`: new affine-coordinate ball perturbation criterion; original origin-moment result retained as a specialization.
- `WeilLogShiftUniformBallGenericity.lean`: existing proved origin-to-all-shifts implication exposed as a public reusable theorem.
- `WeilLogShiftExponentialPrecision.lean`: exponential damping still leaves the inverse diagonal divergent; bounded precision envelope and perturbed history; exact affine moment expansion and unit-coordinate response; exact coordinatewise error bound.
- `WeilLogShiftExponentialPrecisionGenericity.lean`: open dense tail events, dense residual nowhere-bounded and nowhere-signed-summable parameter sets, meagre exceptions, and constrained-error witnesses around every bounded center.
- All five affected leaves compiled/exported with `lake --old env lean ... -o ...`, exit 0 and no diagnostics. Both new leaves passed first compilation. The generalized affine proof needed one local cutoff rename; no mathematical argument changed. No subsequent source edits.
- All thirty-six public theorems in the five leaves, including retained old APIs, were audited exactly once by scratch `#print axioms`, exit 0. Every theorem uses exactly `[propext, Classical.choice, Quot.sound]`. Eighteen public theorem statements are new this increment.
- All five umbrella imports are unique. Index refresh exited 0. Every one of the forty-three public API rows has the correct declaration kind, module and source line. Scoped source checks passed.
- Global lint exits 1 solely for fourteen unrelated unwired modules: `RHTower.LaguerrePolyaFirstOrderGapBound`; `HTGeometry.QKrawtchoukJacobiResolvent`; and these twelve `HTGeometry.PaperStableCoordinate` leaves: `CoordinateLeadingDerivation`, `FactorialClosure`, `FiltrationDerivationShift`, `GradedRelationSanity`, `LaurentDerivationTransport`, `LaurentLNDDescent`, `LaurentPresentation`, `LaurentWeightedMap`, `LocalizationLND`, `ModificationPieces`, `ReesToDegeneration`, `SourceLocalizedDerivation`. No diagnostic names any affected leaf. These unrelated files remain untouched.
- No new unproved analytic assumptions or axioms, proof gaps, raised limits, numerical experiments, external sources, full builds, commits, or subagents.

## Next conjecture: one fixed history-coordinate error

Test whether the origin response to the first coordinate impulse is nonsummable:
`¬ Summable (fun n => weilLogShiftRecoveryMomentResponse 0 n 0)`.
This differs from the proved moving-diagonal obstruction. If true, even a perturbation of one fixed history coordinate would obstruct signed summability: two distinct amplitudes along that coordinate cannot both give summable origin moments, because their difference is a nonzero multiple of this response column. Since any positive exponential error envelope permits a nonzero perturbation at that fixed coordinate, this could remove the present restriction sigma<4-pi for the existence of nonsummable histories. It would not by itself prove unbounded individual moment terms or the current genericity conclusion; those need separate arguments.

If the column is instead summable, extract the positive stability statement for that finite history error and investigate the other columns. The exact finite-matrix receiver identifies column behavior as a meaningful obstruction, rather than treating the current diagonal threshold as optimal. Direct lexical recovery/column search found only `norm_weilLogShiftRecoveryMomentPanel_eq_columns`; no fixed-column divergence result was found. This remains a conjecture, not a proved consequence.

## Working plan

1. [x] Inspect corpus frontier and close dependency-level paper argument.
2. [x] Generalize and verify existing rate and affine perturbation mechanisms. All three modified existing leaves compiled/exported successfully; retained APIs remain in place.
3. [x] Verify bounded multiplication APIs and formalise exponential precision. New precision leaf compiled/exported with exit 0 and no diagnostics on first compilation.
4. [x] Prove dense residual all-shift divergence and constrained-error witnesses. Final new leaf passed first compilation, exit 0 and no diagnostics. Formal result includes sigma=0 as well as positive subcritical rates.
5. [x] Compile affected leaves, exhaustive axiom audit, import/index/lint checks. Only the fourteen unrelated global wiring errors above remain.
6. [x] Update route cards and memories; clean owned scratch; record next conjecture.

## Log

- 2026-10-09 — previous increment completed uniform-ball genericity. Current conjecture strengthens observation precision exponentially; the non-open-map caveat is explicit. Direct local search performed before new Lean code.
- 2026-10-09 — generalized origin lower-envelope proof compiled/exported with exit 0 and no diagnostics. Existing positive-rate theorem retained as its zero-rate specialization. Uniform-ball perturbation proof generalized to affine coordinate families, retaining the original origin-moment theorem; existing origin-to-all-shifts implication exposed for reuse. Bounded multiplication API audit running.
- 2026-10-09 — bounded multiplication API audit passed. `WeilLogShiftExponentialPrecision.lean` drafted with damped diagonal divergence, bounded envelope, affine perturbation, exact coordinate responses and precision bound. Generalized constructive leaf compiling before dependent leaves.
- 2026-10-09 — first generalized affine compilation found a local tail cutoff named T shadowing the affine map family T; renamed cutoff to startIndex and resumed compilation. Both new leaves are drafted and wired. Exhaustive audit prepared for all thirty-six public theorems across all five affected leaves, including retained old APIs.
- 2026-10-09 — generalized affine perturbation leaf compiled/exported with exit 0 and no diagnostics after the cutoff rename. Existing uniform-ball genericity leaf is recompiling after exposing its proved outward-transfer helper. Weighted precision and category leaves follow sequentially.
- 2026-10-09 — uniform-ball genericity leaf compiled/exported with exit 0 and no diagnostics after the helper exposure. New exponential precision leaf now compiling. Next conjecture recorded separately: nonsummability of one fixed inverse-response column, which could test whether the diagonal rate restriction is essential.
- 2026-10-09 — exponential precision leaf passed first compilation, including the exact envelope bound, affine expansion, and damped diagonal divergence. Final category/witness leaf now compiling.
- 2026-10-09 — category/witness leaf passed first compilation. All five affected leaves compiled/exported. Thirty-six-theorem axiom audit and index refresh running; no later source edits.
- 2026-10-09 — all thirty-six public theorem audits passed with exact standard axiom sets. All forty-three public API rows and five unique imports verified. Latest global lint has only the fourteen unrelated wiring errors recorded above. Card moved to formalized; uniform-ball and smooth-edge cards plus failed-route positive survivor updated. Fixed-coordinate response nonsummability is the next conjecture.
- 2026-10-09 — dedicated result memory written and three predecessor memories updated. All seven owned scratch files removed and absence verified; former in-progress card absent. All owned jobs terminal. This increment is complete; the indefinite corpus research goal remains active.
