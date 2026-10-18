# Actual Müntz source smoothing and Weil-domain transfer

- **Stage:** 3-formalized
- **Routes:** WL/RW; actual factorial source.
- **Parent:** [actual diagonal margin](../1-in-progress/factorial-ramp-diagonal-margin-2026-10-18.md).
- **Predecessor:** [uniform analytic boundary repair](../3-formalized/factorial-muntz-uniform-analytic-repair-2026-10-18.md).
- **Objective:** Produce an actual smooth corrected source in the existing decay-class Weil domain, with normalized source approximation and exact transformed readout. Discharge domain hypotheses rather than assume them.

## Plan

1. Audit installed convolution, normalized bump, and decay-class explicit-formula APIs.
2. Prove finite-rate convolution estimates; instantiate them for the canonical corrected Müntz source and the existing normalized mollifiers.
3. Prove the exponential readout factorization, mass normalization, and approximation back to the corrected source.
4. Apply the complete archimedean/polar/Abel-prime identity to these actual sources. Audit leaves and axioms, wire imports, index and lint.

## Dependency-closed paper proof

Write `G_n=F_n+1_(x<=0)c_n exp(x/2)` for the verified canonical correction, and let `r_n` be the actual compact factorial ramp. The verified tail `T_n=G_n-r_n` obeys `|T_n(x)|<=1_(x<=0)12 exp(3x/2)/sqrt(n+1)`. Consequently `|T_n(x)|<=12 exp(-|x|)/sqrt(n+1)`. The continuous compact function `r_n(x)exp(|x|)` is bounded, so `|G_n(x)|<=C_n exp(-|x|)` for a finite nonnegative `C_n`. This gives actual integrability and a finite-rate global envelope; no claim of decay at every exponential rate is made.

For a compact continuous kernel `kappa`, define `M(kappa)=integral |kappa(y)| exp(|y|) dy`. It is finite and nonnegative. The triangle inequality gives `exp(-|x-y|)<=exp(|y|)exp(-|x|)`, hence

`|(kappa*G_n)(x)|<=C_n M(kappa)exp(-|x|)`.

If `kappa` is C2, convolution is C2 and its derivative is `(deriv kappa)*G_n`; the same estimate applies with `M(deriv kappa)`. Thus the actual convolution satisfies `ExpDecayTest`, with decay margin `delta=1/2` and common constant `C_n(M(kappa)+M(deriv kappa))`.

Take the existing normalized compact mollifiers `RHTower.CHMDDoobGraph.mollifier k`, whose integral is exactly one. Define `H_(n,k)=mollifier_k*G_n`. The ordinary approximate-identity theorem applies to locally integrable `G_n`, so the construction returns to `G_n` almost everywhere as the mollifier shrinks. This limit is a source approximation, not yet continuity of the Weil form.

For `Re s>-1`, the weighted source is integrable and the weighted compact kernel is integrable. The identity `exp((s-1/2)x)=exp((s-1/2)y)exp((s-1/2)(x-y))` converts the tilted convolution into the convolution of the two tilted factors. Fubini gives

`readout_s(H_(n,k))=readout_s(mollifier_k)*readout_s(G_n)`.

At every right-half-plane zeta zero `rho`, this is exactly `readout_rho(mollifier_k)*c_n/rho`. At `s=1/2`, the kernel readout is one, so total mass is preserved. No transform normalization or zero-side identification is assumed.

For each fixed complex `s`, the normalized kernel readout tends to one. Apply the continuous approximate-identity theorem at zero to `x -> exp(-(s-1/2)x)`; its convolution with the normalized bump at zero is exactly the kernel readout. Multiplying the exact factorization above therefore gives convergence of the actual smoothed readout to the corrected readout throughout `Re s>-1`, including `s=0` and `s=1`. At any fixed right-half-plane zeta zero, the limit is `c_n/rho`, which is nonzero. Consequently those smoothed readouts are eventually nonzero. This is a fixed-parameter limit and does not exchange any infinite zero sum.

With the produced `ExpDecayTest H_(n,k)`, the existing unconditional theorem `archPoleEnergy_eq_re_W_add_abelPrimePairing` applies to the actual convolution. Its prime term is explicitly the Abel prime pairing; both polar terms are retained inside `archPoleEnergy`.

## Open obligations and scope

This construction must not be described as an unsmoothed full-Weil limit. Continuity as the mollifier shrinks, removal of the Abel regularization when needed, positivity, the coupled ramp diagonal margin, and RH remain open unless separately proved. The corpus's `AllExpDecay.convolution` is inapplicable: it requires every exponential rate, while the source currently has a fixed rate.

## Evidence and verification

Current source hashes for `FactorialMuntzUniformTail.lean` and `FactorialMuntzAnalyticRepair.lean` match their prior verified records. Inspected `CHMDGraphMollification.lean`, installed mathlib convolution differentiation/integration statements, and the decay-class explicit formula. Current corpus search: `/tmp/bsu-muntz-smooth-domain-search.json`; partial=false, no reported errors, semantic coverage unmeasured because of the reporting budget.

Implemented `ExponentialDecayCompactConvolution.lean` (six public theorems, one definition) and `FactorialMuntzWeilSmoothing.lean` (eleven public theorems, one definition). The generic helper compiled. The actual-source module's domain, mass, a.e. approximation, transform product, zero readout and full Weil identity compiled. The three additional fixed-readout limit/nonvanishing theorems passed `/tmp/bsu-muntz-smooth-limit.lean` with exit 0 and an empty log. They are now integrated into the actual-source leaf. Both modules are wired once into the area umbrella.

The final integrated leaf check and 19-declaration axiom audit exited 0. All declarations use only `propext`, `Classical.choice`, and `Quot.sound`. Source hashes match `/tmp/bsu-muntz-smooth-verification.json`; both generated objects are newer than their sources, and both area imports occur exactly once. API and fixed-readout probe logs are empty. The helper has one harmless unused-binder warning; the actual-source check emits an informational `ring_nf` suggestion but no error. No placeholders or additional axioms were introduced.

Direct checks used `lake --old env lean -j 1`, with one owned Lean process at a time. No full or umbrella build, heartbeat increase, numerical experiment, web search, or novelty claim. The final declaration audit is `/tmp/bsu-muntz-smooth-axioms.lean`, with output `/tmp/bsu-muntz-smooth-axioms.log`. No temporary import-cache snapshot was created.

The final `scripts/formal_tools.py index` passed. The final `scripts/formal_tools.py lint --check-generated` exited 1 on two unrelated missing umbrella imports: `BiScaleUncertainty.EulerPoissonChiralDriftAndPrimeShiftRigidity` and `BezoutValuationIncidence.GcdOrbitProjectionAndExactTranslationPeriods`. The generated catalogs are current in that check. Full logs: `/tmp/bsu-muntz-smooth-index-final.log` and `/tmp/bsu-muntz-smooth-lint-final.log`. Neither failure names a new leaf. All nine local links across this card and the parent resolve. No owned Lean process remains live.
