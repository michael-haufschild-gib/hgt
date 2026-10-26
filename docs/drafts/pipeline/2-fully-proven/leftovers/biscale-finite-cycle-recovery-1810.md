# Finite closed-cycle recovery on controlled correlations

- **ID:** biscale-finite-cycle-recovery-1810
- **Stage:** 2-fully-proven for the elementary recovery estimate; source-bound and sharpness gates below remain open
- **Type:** BRIDGE; quantitative extension of existing cycle completeness
- **Parent:** [field programme](../1-in-progress/biscale-field-development-1810.md), item 9

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
- [ ] Actual smooth-source derivative bounds, explicit normalization and nonempty controlled classes; no assumed convergence or assumed recovery.
- [ ] Existing distant-copy obstruction transported into the controlled class with quantified parameters.
- [x] Formalize the singular-energy collar and the grid/energy finite-accuracy theorem above by reusing the existing modulus and tail estimates; inspect the exact corpus query before claiming any extension absent.
- [ ] Named-source/axiom audits, umbrella wiring, index and lint.

This component does not close item 9.

2026-10-18 checkpoint: `EnergyControlledClosedCycleRecovery.lean` now proves the energy-derived κ=1/2 reconstruction protocol, with explicit mesh size/order and signed trace error retained. `EnergyCycle.global_recovery` and `fixed_integer_grid_recovery` passed a direct named-source Lean check with no warnings and are wired into the field umbrella. The modulus-based collar is exp(-(1+32 max(K,0)/exp(-1/2))); no derivative bound is assumed. The arbitrary-κ statement and the other unchecked gates above remain separate. This formalizes existing paper work and is not counted as a new contribution in the 100-contribution programme; its associated exact-order obstruction is tracked in `../3-formalized/biscale-energy-controlled-cycle-observability-2026-10-18.md`.
