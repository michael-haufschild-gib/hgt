# Finite closed-cycle recovery on controlled correlations

- **ID:** biscale-finite-cycle-recovery-1810
- **Stage:** 2-fully-proven; explicit automatic parameters certified, arbitrary-net source audit pending
- **Type:** BRIDGE; quantitative extension of existing cycle completeness
- **Parent:** [field programme](../../1-in-progress/rh/bi-scale-uncertainty/biscale-field-development-1810.md), item 9

## Controlled class and finite observations

Let `h,g` be normalized real autocorrelations of nonzero actual sources. Assume their correlation supports lie in `[-L,L]`, both have `h(y),g(y)≥κ>0` on `|y|≤ρ`, and both obey the same increasing continuity modulus `ω`. Normalized autocorrelations are even and bounded in absolute value by one, by Cauchy–Schwarz and translation invariance of the source norm.

Choose an integer `n≥1` with `nρ≥L`, and a finite `η`-net `X` of `[-L,L]`. For each `x∈X`, put `y=x/n` and observe two closed products:

`Q_h(x)=h(y)h(−y)=h(y)²`,

`C_h(x)=h(−x)h(y)^n=h(x)h(y)^n`.

The second cycle has `n+1` edges: `−x` followed by `n` copies of `y`. Its sum is zero. Thus maximum order is `max(2,n+1)`, and at most `2|X|` literal closed-cycle observations are used. A uniform mesh with spacing at most `η` gives at most `2(ceil(2L/η)+1)` observations when `L,η>0`.

## Exact noise estimate

Write `δ₂=max_X |Q_h−Q_g|` and `δ_C=max_X |C_h−C_g|`. Positivity on the collar gives

`|h(y)−g(y)| = |Q_h(x)−Q_g(x)|/(h(y)+g(y)) ≤ δ₂/(2κ)`.

For `u,v∈[0,1]`, factorization of `u^n−v^n` gives `|u^n−v^n|≤n|u−v|`. Therefore

`κ^n |h(x)−g(x)| ≤ δ_C+nδ₂/(2κ)`

at every mesh point: subtract `h(x)h(y)^n` from `g(x)g(y)^n`, add and subtract `g(x)h(y)^n`, and use `|g(x)|≤1`. Moving any point of `[-L,L]` to a mesh point adds at most `2ω(η)`. Outside that interval both correlations vanish. Hence

`‖h−g‖∞ ≤ κ^(−n)(δ_C+nδ₂/(2κ))+2ω(η)`.

This compares exact admissible sources with noisy observations; an estimator fitting measured arrays inherits the estimate with the sum of the two data residuals. No claim is made that arbitrary noisy arrays are admissible.

## Deriving controls from actual sources

For a smooth compact source `f`, normalize its squared norm to one and write `B=∫|f′|²`. The fundamental theorem of calculus, Cauchy–Schwarz over the translation interval and integration over the source variable give

`‖T_t f−f‖₂²≤Bt²`.

Since `2(1−h(t))=‖T_t f−f‖₂²`, this yields `h(t)≥1−Bt²/2`. A second Cauchy–Schwarz application gives `|h(x)−h(y)|≤sqrt(B)|x−y|`. If the source lies in an interval of length `L`, its autocorrelation is zero for `|x|>L`.

There is a conditioning/order tradeoff. If `n≥BL²` and `n≥1`, then at `y=x/n` both collar values are at least `1−BL²/(2n²)`, and Bernoulli's inequality gives `h(y)^n,g(y)^n≥1/2`. Their sum is at least one. The same proof then gives

`‖h−g‖∞ ≤ 2δ_C+2nδ₂+2sqrt(B)η`.

This replaces exponential collar conditioning by a larger sufficient order of size `BL²`. It requires a derivative-energy bound; the existing singular Lévy-energy bound must not be substituted without an additional proved implication.

## Singular-energy controls already available in the corpus

The derivative bound is optional. Put `c=exp(−1/2)` and let `E` bound the normalized singular energy of both sources. The existing `autocorr_increment_mul_log_le` and `normalized_autocorr_difference_sq_mul_log_le` give, for `0<|t|≤1`,

`1−h(t)≤4E/(c(−log|t|))`,

`|h(x)−h(y)|²≤8E/(c(−log|x−y|))` when `0<|x−y|≤1`.

Thus `ρ_E=exp(−1−8E/c)` gives a common collar with `κ=1/2`, and `ω_E(η)=sqrt(8E/(c(−log η)))` is an available modulus for `0<η<1`. Equality of locations is handled separately. These are consequences of already proved energy estimates, not new source regularity assumptions and not derivative estimates. The existing `exists_uniform_autocorr_continuity_radius` already formalizes a uniform radius; reuse it or its stronger quantitative input.

For the additional class satisfying every logarithmic-grid zero, the existing normalized tail inequality gives `|h(x)|²≤8E/(c|x|)`. Consequently common compact support is unnecessary for **approximate** finite recovery: take an effective radius `L≥32E/(cε²)` so that both tails have size at most `ε/2`, choose `n≥L/ρ_E`, and choose a mesh with `ω_E(η)≤ε/4`. The same finite-cycle estimate gives the global bound

`‖h−g‖∞ ≤ max(ε, 2^n(δ_C+nδ₂)+ε/2)`.

For example `η=exp(−1−128E/(cε²))` suffices. Choose `L≥1` to avoid a zero-radius mesh, and `n≥1`. The resulting finite count and noise threshold are explicit in `E,ε`, even for an unbounded family of source support radii. This does not assert uniform exact finite-order completeness.

Source ingredients inspected: `InfiniteGridUniformTail.lean` contains the global normalized modulus, uniform radius, and grid-induced tail. The additional mathematical work is their coupling to the finite closed-cycle reconstruction protocol. The corpus query `normalized energy logarithmic increment positive collar modulus cycle recovery` returned collar-energy results but did not surface these exact uniform-tail statements; direct source inspection located them. Its snapshot reported `partial=false` with semantic completeness unmeasured. Do not infer absence from those ranked results.

## Scope, obstruction and gates

- The existing smooth distant-copy family has exact first distinguishing order `floor(T)+1` and support radius of size `T+1`. Its normalized origin correlation agrees with the normalized seed on a fixed neighborhood when `T>2`; consequently the order cannot be bounded independently of `L/ρ`. Formalize this controlled-class embedding and its constants.
- [Jaming–Kolountzakis](https://nyjm.albany.edu/j/2003/9-12p.pdf) studies triple-correlation reconstruction and stability. The observations here are products of correlation values along closed cycles. Those two observation models must not be identified without a proved transfer.
- Corpus query `closed cycle positive collar quantitative recovery finite order noise` returned all-orders cycle recovery and collar-energy results, without this finite sampling estimate among returned candidates. Coverage was a source snapshot, semantic completeness unmeasured.
- [x] Finite-cycle factorization and elementary conditional noise estimate proved symbolically.
- [ ] Lean finite-cycle and sampling identities, including zero-radius and endpoint cases.
- [x] Actual smooth-source derivative bounds, explicit normalization and nonempty controlled classes; no assumed convergence or assumed recovery.
- [x] Existing distant-copy obstruction transported into the controlled class with quantified parameters.
- [x] Formalize the singular-energy collar and the grid/energy finite-accuracy theorem above by reusing the existing modulus and tail estimates; inspect the exact corpus query before claiming any extension absent.
- [x] Named-source/axiom audits, umbrella wiring, index and scoped lint. Global unrelated failures are recorded below.

This component does not close item 9.

## Frozen Lean completion

All ten started leaves passed their final direct source checks with no errors
or warnings. Nine logs are empty; `DerivativeCycleConditioning` emits two
informational ring notices, matching the axiom audit. Its redundant tactic
composition warning was removed and the final source checked. All 80 public
declarations have transitive audits using only `propext`, `Classical.choice`,
`Quot.sound`. Only five dependency leaves required new oleans; all five builds
passed. Unique umbrella imports, indexed names and source hashes are verified.
Global lint has no diagnostic for these leaves (20 unrelated structural errors
and 417 size warnings). No umbrella or existing olean was rebuilt.

| Exact claim | Canonical leaf and declaration |
|---|---|
| Exact first-order collar `exp(−1−8E/c)`, logarithmic modulus and quarter-accuracy radius | `FirstOrderEnergyCollar.lean`: `correlation_firstOrderCollar`, `correlation_logarithmic_modulus`, `continuityRadius_quarter_eq` |
| Arbitrary positive `κ`, scalar recovery, literal closed observations, mesh count and maximum order | `ClosedCycleScalarRecovery.lean`: `scalar_cycle_recovery`, `literalObservationCycle_sum`, `literalObservationCycle_count_le`, `literalObservationCycle_length_le` |
| Actual compact derivative in L², primitive identity, exact all-lag translation bound | `CompactSourceDerivativeEnergy.lean`: `primitive_compactDerivativeVelocity`, `integral_compactSource_translation_sq_le` |
| Source-derived correlation collar, Lipschitz modulus and interval support bound | `CompactCorrelationDerivativeBounds.lean`: `nyquistNormalizedCorrelation_ge_one_sub_dirichlet`, `lipschitzWith_nyquistNormalizedCorrelation_sqrt_dirichlet`, `nyquistNormalizedCorrelation_eq_zero_of_source_interval` |
| Separate finite pair/spoke errors and exact window/global reconstruction | `ControlledClosedCycleRecovery.lean`: `controlled_global_recovery_norm`, `exists_common_levyEnergySource` |
| Exact grid-tail recovery with the stated `32` and `128` constants | `GridFiniteCycleRecovery.lean`: `grid_finite_cycle_recovery_norm_exact` |
| Actual fixed-energy distant copies, uniform collar/modulus and unbounded distinguishing order | `ControlledSharpCycleSources.lean`: `controlledSource_uniform_collar`, `controlledSource_detects_iff`, `exists_controlled_sources_above_order` |
| Derivative-energy conditioning and exact `2δ_C+2nδ₂+2√Bη` bound | `DerivativeCycleConditioning.lean`: `derivative_inner_power_ge_half`, `derivative_global_recovery_norm` |
| Arbitrary measured arrays, actual fitting residuals and reconstruction coefficient | `ClosedCycleDataResiduals.lean`: `controlled_recovery_from_measured_array` |
| Actual unit-mass compact sources, preserved correlation/normalized derivative energy and a nonempty controlled class | `UnitMassCompactSources.lean`: `autocorr_unitMassCompactSource_zero`, `normalizedDirichletEnergy_unitMassCompactSource`, `exists_unit_mass_derivative_controlled_source` |

Leaves reside in `formal/GaloisForLFunctions/BiScaleUncertainty/`.
The literal spoke implementation uses a natural index `k` for the positive
paper order `n=k+1`; its total cycle order is `k+2`. Accordingly the displayed
`n` coefficients are preserved exactly, including the grid estimate's `2^n`.
Actual source construction discharges source regularity and normalization;
the recovery theorems retain only the stated domain/control conditions.

The resumed task has completed automatic parameter selection in
`GridCycleRecoveryParameters.lean`. Set
`R=max(1,32E/(cε²))`, `η=exp(-1-128E/(cε²))`,
`d=ceil(R/ρ_E)`, `A=2^(d+1)(d+2)`, and `τ=ε/(2A)`.
The literal finite family is closed, has maximum order `d+2`, and uses at
most `2(ceil(2R/η)+1)` observations. Every discrepancy at most `τ`, or total
fitting residual at most `τ`, guarantees global error at most `ε`.
All 21 new public declarations have transitive standard-axiom audits, and
the canonical leaf passed its final direct source check without diagnostics.
Its umbrella import and corpus indexing are verified.

The card remains at stage 2 while the arbitrary-finite-net and corresponding
measured-array recovery draft undergoes its source and transitive axiom audit.
This is the remaining explicit ancillary coverage check; item 9 is not yet
declared closed.

Evidence: `/tmp/leftovers-cycle-public-names.json`,
`/tmp/leftovers-cycle-complete-audit-r2.log`, and
[the frozen-scope tracker](../../1-in-progress/leftovers-unconditional-formalization.md).

2026-10-18 checkpoint: `EnergyControlledClosedCycleRecovery.lean` now proves the energy-derived κ=1/2 reconstruction protocol, with explicit mesh size/order and signed trace error retained. `EnergyCycle.global_recovery` and `fixed_integer_grid_recovery` passed a direct named-source Lean check with no warnings and are wired into the field umbrella. The modulus-based collar is exp(-(1+32 max(K,0)/exp(-1/2))); no derivative bound is assumed. The arbitrary-κ statement and the other unchecked gates above remain separate. This formalizes existing paper work and is not counted as a new contribution in the 100-contribution programme; its associated exact-order obstruction is tracked in `../../3-formalized/biscale-energy-controlled-cycle-observability-2026-10-18.md`.

## Final source checks for the started scope

Every row passed a direct `lake --old env lean -j 1` check from `formal/`,
without writing an olean. The first five leaves supplied the only new oleans
needed by the remaining started modules in the historical first batch.
The source statements retain the exact paper constants; new checks are
appended below. The resumed parameter leaf additionally required the missing
`GridFiniteCycleRecovery` and `ClosedCycleDataResiduals` oleans; both built
successfully by direct commands, without rebuilding any existing olean.

| Leaf | SHA-256 | Final direct-check log |
|---|---|---|
| `FirstOrderEnergyCollar` | `d96b38f6be1733f17fb4178235a3a9349aa91f1e7221920aa2e133cde1849170` | `/tmp/leftovers-cycle-collar-final.log` |
| `ClosedCycleScalarRecovery` | `6dd9cb09d8c4164977a4606d57edb6dc86cecb66f6a0a16d9d781eb199349ef2` | `/tmp/leftovers-cycle-scalar-final.log` |
| `CompactSourceDerivativeEnergy` | `d68db0038dcdfccb63ca5ae375a5b027d5004543affc8e009f613ac2653fd427` | `/tmp/leftovers-cycle-source-derivative-final.log` |
| `CompactCorrelationDerivativeBounds` | `c7c1b6f0e218e24f717f105da2c6560535b9da20d105a55a7ef616db5b1ed989` | `/tmp/leftovers-cycle-correlation-derivative-final.log` |
| `ControlledClosedCycleRecovery` | `5bef47bf1618886765dda55f48368c3001e2336f6f42aaa2653617c41c33d66c` | `/tmp/leftovers-cycle-controlled-final.log` |
| `GridFiniteCycleRecovery` | `860048b5293a00b1aa3bdcea19d636ecf6008cf30f5f044f8611a3f6d3981141` | `/tmp/leftovers-cycle-grid-final.log` |
| `ControlledSharpCycleSources` | `59bd4dde72fff6960ba69987df9aaa0041bde8a45a1d362c0821286bb2720aac` | `/tmp/leftovers-cycle-sharp-final.log` |
| `DerivativeCycleConditioning` | `a636c585ded88d88feb2cefb216c8254b412e4fbb63b016a8a3ca769a9c878e4` | `/tmp/leftovers-cycle-conditioning-final.log` |
| `ClosedCycleDataResiduals` | `2c6240f3264fa3d0268ee73e742d2d4041b7198a57d6674026967585d7b674aa` | `/tmp/leftovers-cycle-residuals-final.log` |
| `UnitMassCompactSources` | `e25513b2ddf29de14278ed9edaba87a3cac69cd4dc1bca461af8e902d307a38a` | `/tmp/leftovers-cycle-unit-mass-final.log` |
| `GridCycleRecoveryParameters` | `9aba018dce162eb2d792fc34587a546921693300f07cca511692a845cf8f7931` | `/tmp/leftovers-cycle-parameters-final.log` |
