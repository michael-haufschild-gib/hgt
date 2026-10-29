# Product conjugation precision is determined by the mean current

- **ID:** asrp-product-conjugation-precision-is-the-mean-current
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** ASRP open topic 6; measure of the fixed-real-source conjugation family.
- **Statement:** Fix a torus gauge `t` and arbitrary probabilities `q_p∈[0,1]` of keeping each prime phase; otherwise conjugate its whole Euler factor. Write `B_(t,q)(x)=Σ_(p≤x) (2q_p−1) sin(2πt_p) log p`. Almost surely, the complex count holds exactly when RH, `D_t=O(√x log²x)` and `B_(t,q)=O(√x log²x)` hold. Every real prime-power coefficient stays fixed. For fair choices, almost every conjugation is a complex count lift of the real source.

## Proof

Put `a_n=sin(2πt_n)log n` on primes and zero elsewhere. Independently choose `ε_n=1` with probability `q_n`, otherwise `−1`. Centered coefficients `X_n=ε_n a_n−(2q_n−1)a_n` have mean zero and variance `4q_n(1−q_n)a_n²≤a_n²`. Also `|X_n|≤2|a_n|`, so all finite second moments and the maximal inequality apply.

For `N=2^(K+1)`, `Σ_(n≤N)a_n²≤N(K+1)²`, using `|a_n|≤log n≤(K+1)log 2≤K+1`. Kolmogorov's inequality bounds the probability of any partial sum through `N` exceeding `√N(K+1)²` by `(K+1)⁻²`. This is summable. Borel–Cantelli therefore bounds every partial sum below all sufficiently large dyadic horizons. Taking `K=floor(log₂ floor x)` gives `Σ_(n≤x)X_n=O(√x log²x)` almost surely.

Conjugating the entire Euler factor at prime `p` changes `sin(2πt_p)` by `ε_p` and preserves `cos(2πkt_p)` for every power `p^k`. Thus the real source is unchanged, and its prime sine current differs from `B_(t,q)` by the centered partial sum. Proper prime powers contribute `O(√x)` to the imaginary source, by `imaginary_partialSum_sub_current_isBigO`. The existing component criterion `complexCount_iff` now gives exactly the stated equivalence, using `count_torusGauge_iff` for the real component.

For fair signs `B=0`. Retaining finitely many prescribed phases changes the prime current by a finitely supported weight, whose partial sum belongs to the square-root class. Hence the fair conclusion also holds with any finite phase prefix retained.

## Gates

- [x] Corpus reuse and novelty audit.
- [x] Dependency-closed paper proof.
- [x] Both leaves checked directly; exact theorem and transitive dependencies audited; umbrellas wired.

## Contribution and calibration

This resolves the measure question for each fixed-real-source conjugation family and classifies every independent product bias by a deterministic precision invariant. Existing full-torus generic cancellation changes the real source; this theorem fixes every real coefficient. Corpus searches found the probability tools and fixed-orientation criterion, but no such fiberwise classification. No global novelty claim.

Precision survives exactly when both the real deficit and the mean current have square-root size; random centered fluctuations add no obstruction. Sign gauges, the Liouville twin and cofinite flips have zero sine current, so their existing real-count verdicts remain unchanged. Finite modifications remain invisible. Scaling and additive power perturbations are outside this fixed-real-source family and acquire no new count. Over a finite field, conjugation preserves the real power sums and spectral moduli, hence cannot remove an outer eigenvalue or repair the golden datum. The proof preserves the Euler-source identity and bounds only the centered extraction; it supplies neither an integrality ceiling nor a new inversion estimate.

## Boundary

This classifies all independent product biases, including deterministic orientations and fair conjugations. It does not select the arithmetic point from a Haar-null exceptional set or prove RH. Count the bias criterion and its fair and finite-prefix consequences as one contribution.

## Formalization

Arithmetic leaf: `ArithmeticOfSquareRootPrecision/ProductConjugationPrecisionIsTheMeanCurrent.lean`.
Probability tool: `HTGeometry/LogarithmicIndependentSigns.lean`.

Main declarations: `ae_gaugeCurrent_sub_mean_isBigO`,
`ae_complexCount_conjugatedGauge_iff_rh_distance_mean`, `ae_fair_complexCount_iff`,
`ae_prefix_complexCount_iff`. The generic bound is
`HTGeometry.LogarithmicSigns.ae_eventually_norm_partialSum_floor_le`.

Both direct `lake --old env lean` leaf checks passed without warnings. The production proof body
matches the audited source. All five axiom audits contain only `propext`, `Classical.choice`,
`Quot.sound`; output: `logs/asrp-product-conjugation-axioms.txt`.
