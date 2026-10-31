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
| O5: second prime bridge | Intrinsic adelic or indefinite carrier with the specified Weil dilation and critical Haar readings and proved finite negative index | Construction and finite-index proof; positive affine carriers are already excluded |

## Verified starting points

- O1: `completedConductorEnergy_nonneg`, `nonRatioForm_eq_sum_shellForm`, and the successor-disagreement identity cover the stated conductor and shell pieces. [Uniform top-band cancellation](../3-formalized/joint-top-band-payment-uniform-in-overlap.md) gives `|κ_N(c)| ≤ Kφ G(c + 1 + log N)` on `1 ≤ c ≤ N/4`; general signed repayment remains open.
- O1 conductor order: [Coprime Fourier domination](../3-formalized/the-completed-conductor-energy-dominates-its-rescaled-pole.md) proves `E_m(c) ≥ E_1(c/m)` and `E_m(c) ≥ log(m/c) + min(0, completeWeilSelfFinitePart φ 1)`, uniformly in `m,c`. These scalar laws do not identify the finite-horizon matrix with its conductor limit.
- O1 exact surplus: [Positive Abel decomposition](../3-formalized/positive-abel-decomposition-of-the-conductor-surplus.md) expresses `E_m(c)−E_1(c/m)` as a convergent sum of nonnegative harmonic-sieve coefficients times Fourier-band squares. The boundary vanishes by the finite Euler limit and Fourier-tail decay.
- O2: [Finite-sieve Hodge index](../3-formalized/matched-prime-form-hodge-index-uniform-in-the-sieve.md) is formalized. `eventually_sieveHodgeGram_one_positive_direction` proves that `P_N − (log N − γ − η)I`, for `0 < η < 2 log 2`, has exactly one positive direction on every full finite-sieve partition, with one horizon independent of the sieve. It follows from the existing all-vector prime gap and pole estimate. Arbitrary finite profile Grams inherit at most one positive direction; fixed depth truncations can omit the pole. The complete Weil form and infinite assembly remain open.
- O3: [Global squared-depth dissipation](../3-formalized/the-global-heat-depth-energy-dissipates.md) now proves `E(b)+2∫_a^b N(t)dt≤E(a)` for the actual full heat divisor and `0<a≤b`, through collisions. The endpoint `heatGlobalVerticalEnergy_add_integral_count_le` and its dependencies have direct Lean checks and standard axiom closures. The unheated energy and the required growth bound as `t↓0` remain unproved.
- O4: `riemannHypothesis_of_eventually_horizontalCollisionCharge_lt_two` still requires the charge bound.
- O5: `translation_eq_of_continuousAt_dilation` assumes positive definiteness; it does not exclude finite negative index.
- O5 beyond Hecke support: [Finite-index Mautner conjecture](finite-index-mautner-rigidity-for-the-haar-successor.md) isolates possible finite-dimensional isotropic transport. [Isotropic translation unipotence](../3-formalized/isotropic-translation-defects-are-unipotent.md) is formalized without dilation invariance of the subspace. Scalar dilation continuity does not yet control the mixed coefficients.
- O5 Haar reading alone: [an explicit logarithmic perturbation](../3-formalized/the-haar-successor-admits-one-negative-square.md) preserves the Haar successor and has index exactly one. Its dilation reading is discontinuous, so it does not provide the required Weil carrier.
- O5 finite-dimensional component: [Rational affine unitary rigidity](../3-formalized/finite-rational-affine-unitary-representations-kill-translations.md) proves factorization through dilations. [Without unitarity](../3-formalized/finite-rational-affine-representations-have-unipotent-translations.md), translations are unipotent with exponent at most the dimension. Both are unconditional algebraic laws without continuity; the missing covariant decomposition cannot be inferred from the existing finite-rank correction.
- O5 exact index law: [Positive integer-successor carriers preserve slope index](../3-formalized/positive-haar-carriers-preserve-the-index-of-slope-corrections.md) proves `κ(p+ψ∘slope)=κ(ψ)` for every positive affine `p` with integer successor and every Hermitian slope kernel. No Hecke support is needed. A general indefinite carrier need not have this separable form.
- O5 continuous dilations: [The separable-carrier obstruction](../3-formalized/separable-haar-carriers-cannot-have-continuous-dilations.md) proves infinite index when `p+ψ∘slope` has a continuous dilation reading, including Weil's spline correlation. Its positive structural survivor is the exact index law above. Arbitrary mixed affine carriers remain outside this class.
- O5 mixed coefficients: [The quadratic construction](../3-formalized/mixed-polynomial-affine-perturbations-preserve-both-axis-readings.md) preserves both Haar axis readings and has index exactly three, but cannot split as a positive affine kernel plus a slope kernel. Its dilation reading is still discontinuous. The [subgroup zero-set law](../3-formalized/null-kernels-of-index-one-have-subgroup-zero-sets.md) proves that a nonzero perturbation vanishing on both axes needs at least two negative squares.
- O5 zero-axis structure: [The finite-rank law](../3-formalized/axis-invisible-finite-index-kernels-have-finite-rank.md) bounds column dimension by `r²`; the [degree law](../3-formalized/the-negative-index-bounds-zero-axis-translation-degree.md) bounds nonzero polynomial fibres by degree `<r`. The [sharp power family](../3-formalized/axis-invisible-affine-polynomials-realize-arbitrary-finite-index.md) attains index `d+1` in every degree `d≥1`, unchanged by any positive-definite addition. These are formalized; decomposition of arbitrary Haar-successor carriers remains open.
- O5 covariant defects: [The affine period-defect orbit](../3-formalized/haar-period-defects-have-a-finite-affine-orbit.md) is invariant and has dimension at most `r²`, formalized for every periodic translation reading. The canonical polynomial correction and the positive-plus-slope decomposition of the remaining bi-integer-invariant carrier remain open.

## Completion gates

- [ ] O1 fully resolved; exact unconditional Lean theorem and axiom audit.
- [ ] O2 fully resolved; exact unconditional Lean theorem and axiom audit.
- [ ] O3 fully resolved; exact unconditional Lean theorem and axiom audit.
- [ ] O4 fully resolved; exact unconditional Lean theorem and axiom audit.
- [ ] O5 fully resolved; exact unconditional Lean theorem and axiom audit.

A claimed impossibility must cover the full mechanism and eliminate its positive survivors. None is currently established here.
