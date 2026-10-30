# Five structural mechanisms for Weil positivity

- **ID:** WEIL-FIVE-STRUCTURAL-MECHANISMS
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** [opportunities O1–O5](../../../reports/review-3010/obstacles-summary.md#25-breakthrough-opportunities-on-weil-positivity)
- **Goal:** Resolve and formalize each complete mechanism. A criterion, estimate, finite test, or obstruction to a restricted construction does not close an item.

| Mechanism | Required mathematical conclusion | Current gap |
|---|---|---|
| O1: successor-shell squares | Exact decomposition of the complete Weil form; agreement-shell squares and a pole-paid edge remainder, for all coefficient vectors | Signed shell–pole–archimedean payment outside conductor packets |
| O2: local–global index | Integer signature formula for the global Weil kernel, with proved local terms and archimedean gluing | Transfer from the matched prime form to the complete Weil form and its infinite assembly |
| O3: heat Lyapunov functional | Global dissipation controlling the actual nonreal count, with an unconditional finite source/flux budget yielding the claimed heat-count improvement | Summation over heights; localized energy evolution alone gives no global budget |
| O4: additive integer margin | A theta-source bound below the actual collision/index quantum, with approximation error proved small enough | Source bound, not integrality or convergence of readings |
| O5: second prime bridge | Intrinsic adelic or indefinite carrier with the specified Weil dilation and critical Haar readings and proved finite negative index | Construction and finite-index proof; positive affine carriers are already excluded |

## Verified starting points

- O1: `completedConductorEnergy_nonneg`, `nonRatioForm_eq_sum_shellForm`, and the successor-disagreement identity cover the stated conductor and shell pieces, not general signed repayment.
- O2: `eventually_isHyperbolic_classHodgeGram` concerns one prime and fixed valuation depth. The stronger existing `eventually_atomicWeilForm_le_two_log_two` controls all vectors orthogonal to the pole, with one horizon independent of the sieve. Together with `eventually_atomicWeilForm_truncPole_ge`, it implies that `P_N − (log N − γ − η)I` has exactly one positive direction for `0 < η < 2 log 2`. Every finite profile Gram inherits at most one positive direction; full sieve partitions contain the pole and therefore inherit exactly one. A fixed depth truncation need not contain the pole.
- O3: `exists_uniform_heatLocalizedVerticalEnergy_evolution` has outer-energy flux. `ImaginaryEnergyLyapunov.lean` proves the two-point algebra and scalar implications; its prose about the global Ξ sum is not a theorem about that sum.
- O4: `riemannHypothesis_of_eventually_horizontalCollisionCharge_lt_two` still requires the charge bound.
- O5: `translation_eq_of_continuousAt_dilation` assumes positive definiteness; it does not exclude finite negative index.

## Completion gates

- [ ] O1 fully resolved; exact unconditional Lean theorem and axiom audit.
- [ ] O2 fully resolved; exact unconditional Lean theorem and axiom audit.
- [ ] O3 fully resolved; exact unconditional Lean theorem and axiom audit.
- [ ] O4 fully resolved; exact unconditional Lean theorem and axiom audit.
- [ ] O5 fully resolved; exact unconditional Lean theorem and axiom audit.

A claimed impossibility must cover the full mechanism and eliminate its positive survivors. None is currently established here.
