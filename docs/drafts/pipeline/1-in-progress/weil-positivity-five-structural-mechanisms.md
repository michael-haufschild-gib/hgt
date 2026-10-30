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
| O3: heat Lyapunov functional | Global dissipation controlling the actual nonreal count, with an unconditional finite source/flux budget yielding the claimed heat-count improvement | Summation over heights; localized energy evolution alone gives no global budget |
| O4: additive integer margin | A theta-source bound below the actual collision/index quantum, with approximation error proved small enough | Source bound, not integrality or convergence of readings |
| O5: second prime bridge | Intrinsic adelic or indefinite carrier with the specified Weil dilation and critical Haar readings and proved finite negative index | Construction and finite-index proof; positive affine carriers are already excluded |

## Verified starting points

- O1: `completedConductorEnergy_nonneg`, `nonRatioForm_eq_sum_shellForm`, and the successor-disagreement identity cover the stated conductor and shell pieces. [Uniform top-band cancellation](../3-formalized/joint-top-band-payment-uniform-in-overlap.md) gives `|κ_N(c)| ≤ Kφ G(c + 1 + log N)` on `1 ≤ c ≤ N/4`; general signed repayment remains open.
- O1 conductor order: [Coprime Fourier domination](../3-formalized/the-completed-conductor-energy-dominates-its-rescaled-pole.md) proves `E_m(c) ≥ E_1(c/m)` and `E_m(c) ≥ log(m/c) + min(0, completeWeilSelfFinitePart φ 1)`, uniformly in `m,c`. These scalar laws do not identify the finite-horizon matrix with its conductor limit.
- O1 exact surplus: [Positive Abel decomposition](../3-formalized/positive-abel-decomposition-of-the-conductor-surplus.md) expresses `E_m(c)−E_1(c/m)` as a convergent sum of nonnegative harmonic-sieve coefficients times Fourier-band squares. The boundary vanishes by the finite Euler limit and Fourier-tail decay.
- O2: [Finite-sieve Hodge index](../3-formalized/matched-prime-form-hodge-index-uniform-in-the-sieve.md) is formalized. `eventually_sieveHodgeGram_one_positive_direction` proves that `P_N − (log N − γ − η)I`, for `0 < η < 2 log 2`, has exactly one positive direction on every full finite-sieve partition, with one horizon independent of the sieve. It follows from the existing all-vector prime gap and pole estimate. Arbitrary finite profile Grams inherit at most one positive direction; fixed depth truncations can omit the pole. The complete Weil form and infinite assembly remain open.
- O3: `exists_uniform_heatLocalizedVerticalEnergy_evolution` has outer-energy flux. `ImaginaryEnergyLyapunov.lean` proves the two-point algebra and scalar implications; its prose about the global Ξ sum is not a theorem about that sum.
- O4: `riemannHypothesis_of_eventually_horizontalCollisionCharge_lt_two` still requires the charge bound.
- O5: `translation_eq_of_continuousAt_dilation` assumes positive definiteness; it does not exclude finite negative index.
- O5 beyond Hecke support: [Finite-index Mautner conjecture](finite-index-mautner-rigidity-for-the-haar-successor.md) isolates possible finite-dimensional isotropic transport. Scalar dilation continuity does not yet control the mixed coefficients.

## Completion gates

- [ ] O1 fully resolved; exact unconditional Lean theorem and axiom audit.
- [ ] O2 fully resolved; exact unconditional Lean theorem and axiom audit.
- [ ] O3 fully resolved; exact unconditional Lean theorem and axiom audit.
- [ ] O4 fully resolved; exact unconditional Lean theorem and axiom audit.
- [ ] O5 fully resolved; exact unconditional Lean theorem and axiom audit.

A claimed impossibility must cover the full mechanism and eliminate its positive survivors. None is currently established here.
