# Five structural mechanisms for Weil positivity

- **ID:** WEIL-FIVE-STRUCTURAL-MECHANISMS
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** [opportunities O1–O5](../../../reports/review-3010/obstacles-summary.md#25-breakthrough-opportunities-on-weil-positivity)
- **Goal:** Resolve and formalize each complete mechanism. A criterion, estimate, finite test, or obstruction to a restricted construction does not close an item.

| Mechanism | Required mathematical conclusion | Current gap |
|---|---|---|
| O1: successor-shell squares | Exact decomposition of the complete Weil form; agreement-shell squares and a pole-paid edge remainder, for all coefficient vectors | Exact conductor/shell decomposition and edge payment on a specified growing-overlap schedule |
| O2: local–global index | Integer signature formula for the global Weil kernel, with proved local terms and archimedean gluing | Transfer from the matched prime form to the complete Weil form and its infinite assembly |
| O3: heat Lyapunov functional | Global dissipation controlling the actual nonreal count, with an unconditional finite source/flux budget yielding the claimed heat-count improvement | Global positive-time dissipation is formalized; an adequate source bound as time tends to zero remains open |
| O4: additive integer margin | A theta-source bound below the actual collision/index quantum, with approximation error proved small enough | Source bound, not integrality or convergence of readings |
| O5: second prime bridge | Intrinsic adelic or indefinite carrier with the specified Weil dilation and critical Haar readings and finite negative index, or complete impossibility with positive survivors resolved | The nonzero-Haar obstruction is audited on rational affine groups and on `ℚ⁺ ⋉ (ℝ × 𝔸_f)` with diagonal scalar action; the canonical relative split and exact residual index are audited; broader O5 closure remains open |

## Verified starting points

- O1: `completedConductorEnergy_nonneg`, `nonRatioForm_eq_sum_shellForm`, and the successor-disagreement identity cover the stated conductor and shell pieces. [Uniform top-band cancellation](../3-formalized/joint-top-band-payment-uniform-in-overlap.md) gives `|κ_N(c)| ≤ Kφ G(c + 1 + log N)` on `1 ≤ c ≤ N/4`; general signed repayment remains open.
- O1 conductor order: [Coprime Fourier domination](../3-formalized/the-completed-conductor-energy-dominates-its-rescaled-pole.md) proves `E_m(c) ≥ E_1(c/m)` and `E_m(c) ≥ log(m/c) + min(0, completeWeilSelfFinitePart φ 1)`, uniformly in `m,c`. These scalar laws do not identify the finite-horizon matrix with its conductor limit.
- O1 exact surplus: [Positive Abel decomposition](../3-formalized/positive-abel-decomposition-of-the-conductor-surplus.md) expresses `E_m(c)−E_1(c/m)` as a convergent sum of nonnegative harmonic-sieve coefficients times Fourier-band squares. The boundary vanishes by the finite Euler limit and Fourier-tail decay.
- O2: [Finite-sieve Hodge index](../3-formalized/matched-prime-form-hodge-index-uniform-in-the-sieve.md) is formalized. `eventually_sieveHodgeGram_one_positive_direction` proves that `P_N − (log N − γ − η)I`, for `0 < η < 2 log 2`, has exactly one positive direction on every full finite-sieve partition, with one horizon independent of the sieve. It follows from the existing all-vector prime gap and pole estimate. Arbitrary finite profile Grams inherit at most one positive direction; fixed depth truncations can omit the pole. The complete Weil form and infinite assembly remain open.
- O3: [Global squared-depth dissipation](../3-formalized/the-global-heat-depth-energy-dissipates.md) now proves `E(b)+2∫_a^b N(t)dt≤E(a)` for the actual full heat divisor and `0<a≤b`, through collisions. The endpoint `heatGlobalVerticalEnergy_add_integral_count_le` and its dependencies have direct Lean checks and standard axiom closures. The unheated energy and the required growth bound as `t↓0` remain unproved.
- O4: `riemannHypothesis_of_eventually_horizontalCollisionCharge_lt_two` still requires the charge bound.
- O5 rational obstruction: [Cyclic Haar averaging and scalar normalization](cyclic-haar-averages-force-infinite-index-at-continuous-dilations.md) prove `negIndex_eq_top_of_nonzero_haar_continuous_dilation` and its positive-slope counterpart, with direct Lean audits and standard axiom closures. Every Hermitian rational-affine kernel with a nonzero integer-Haar multiple and dilation reading continuous at one has infinite index, without Hecke support or a mixed-coefficient bound. `not_exists_finite_index_adelic_haar_coefficient_weil_state` also excludes the actual Haar overlap integral and pure Weil dilation reading on `ℚ⁺ ⋉ (ℝ × 𝔸_f)` with diagonal scalar action; its direct audit has the same standard axiom closure.
- O5 mechanism: [The canonical polynomial correction](../3-formalized/finite-index-periodic-affine-kernels-have-a-zero-axis-polynomial-correction.md) is unique, Hermitian, finite rank, and zero on both axes; its subtraction leaves a finite-index bi-integer-invariant kernel. Its translation moving spaces are nonnegative, their cyclic correlations have a reciprocal-denominator bound, and fixed-projection Grams converge to `J−I`.
- O5 sharp boundary: [The logarithmic carrier](../3-formalized/the-haar-successor-admits-one-negative-square.md) has index one. [Mixed polynomial carriers](../3-formalized/axis-invisible-affine-polynomials-realize-arbitrary-finite-index.md) preserve both Haar axis readings and realize every index at least two. Their dilation readings are discontinuous; the [quadratic example](../3-formalized/mixed-polynomial-affine-perturbations-preserve-both-axis-readings.md) cannot split as positive plus slope.
- O5 finite structure: [The affine period-defect orbit](../3-formalized/haar-period-defects-have-a-finite-affine-orbit.md) has dimension at most `r²`. [Zero-axis kernels](../3-formalized/axis-invisible-finite-index-kernels-have-finite-rank.md) also have rank at most `r²`, and their [polynomial fibres](../3-formalized/the-negative-index-bounds-zero-axis-translation-degree.md) have degree below `r`.
- O5 positive survivor: [Positive Haar carriers preserve slope index](../3-formalized/positive-haar-carriers-preserve-the-index-of-slope-corrections.md): `κ(p+ψ∘slope)=κ(ψ)`. The [unique relative splitting](../3-formalized/finite-index-haar-carriers-split-modulo-polynomial-kernels.md) is formalized, with `κ(k)=κ(ψ∘slope+Q)≥κ(ψ)`.

## Completion gates

- [ ] O1 fully resolved; exact unconditional Lean theorem and axiom audit.
- [ ] O2 fully resolved; exact unconditional Lean theorem and axiom audit.
- [ ] O3 fully resolved; exact unconditional Lean theorem and axiom audit.
- [ ] O4 fully resolved; exact unconditional Lean theorem and axiom audit.
- [ ] O5 fully resolved; exact unconditional Lean theorem and axiom audit.

A claimed impossibility must cover the full mechanism and eliminate its positive survivors. None is currently established here.
