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

## Scope, obstruction and gates

- The existing smooth distant-copy family has exact first distinguishing order `floor(T)+1` and support radius of size `T+1`. Its normalized origin correlation agrees with the normalized seed on a fixed neighborhood when `T>2`; consequently the order cannot be bounded independently of `L/ρ`. Formalize this controlled-class embedding and its constants.
- [Jaming–Kolountzakis](https://nyjm.albany.edu/j/2003/9-12p.pdf) studies triple-correlation reconstruction and stability. The observations here are products of correlation values along closed cycles. Those two observation models must not be identified without a proved transfer.
- Corpus query `closed cycle positive collar quantitative recovery finite order noise` returned all-orders cycle recovery and collar-energy results, without this finite sampling estimate among returned candidates. Coverage was a source snapshot, semantic completeness unmeasured.
- [x] Finite-cycle factorization and elementary conditional noise estimate proved symbolically.
- [ ] Lean finite-cycle and sampling identities, including zero-radius and endpoint cases.
- [ ] Actual smooth-source derivative bounds, explicit normalization and nonempty controlled classes; no assumed convergence or assumed recovery.
- [ ] Existing distant-copy obstruction transported into the controlled class with quantified parameters.
- [ ] Determine whether the incidence/energy hypotheses developed elsewhere supply these controls, or give an actual-source obstruction.
- [ ] Named-source/axiom audits, umbrella wiring, index and lint.

This component does not close item 9.
