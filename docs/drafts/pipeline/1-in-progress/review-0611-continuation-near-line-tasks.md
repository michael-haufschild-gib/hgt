# Review-0611 §2.1 Continuation and near-line tasks (A23–A37)

- **ID:** review-0611-a23-a37
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean), one per task
- **Source:** [Obstacles summary §2.1](../../../reports/review-0611/obstacles-summary.md)
- **Statement:** Each task A23–A37 gets a complete unconditional Lean theorem, easiest first. Certified numerical scans are out of scope (goal rule: no computations).

## Status

| Task | Status | Lean / note |
|---|---|---|
| A26 | done | NGF and MZF modules all committed and wired into `NodalGeometryOfTheDeBruijnFlow.lean`, `MultiscaleMollifiedZetaField.lean` |
| A36 | done (scans excluded: no computations) | `CompletedArithmeticForms/EisensteinDivisorTrace.lean`, `TheApertureSpectrumIsAnEulerProduct.lean`: `S = Σ_N τ_b(N) A(log N)`, `τ_b` is the coefficient of `E*`, `τ_b(p^k) = U_k(cos(b log p))`, `Σ τ_b(N) N^{−s} = ζ(s−ib) ζ(s+ib)`, `S = Π_p T_p A`, exponentials are eigenfunctions with eigenvalue `Π‖1−p^{−s+ib}‖⁻²`, `A` is not a positive Laplace mixture |
| A24 | done | `ZeroConfigurationGeometry/HeatScaleRepulsion/TheExceptionalSetHasAPowerSaving.lean`: `exists_volume_localNewman_scaled_gt_le_rpow`, `exists_volume_nonreal_heat_le_rpow`; mechanism `TheComplexSaddleOfAGaussianAverage.lean` |

## A24: paper proof plan

Polylog typical heights need `|ζ′/ζ| = o(√log T)` because the corpus model freezes `ζ` across the Gaussian window. At level `T^ε` the slope error is `θα`, so the phase of `ζ` rotates by `θ√(κα) → ∞` across the window and the real-line model fails.

Fix: shift the contour to the complex saddle. `F(w) = ξ(½+w+iX)`, `ℓ = F′/F`, `u* = y + 2τℓ(u*)` by Banach (Lipschitz constant `2τ|ℓ′| ≲ θ/η`). On `w = u* + v`, the Gaussian times `F` is `F(u*) e^{−τℓ*²} g_τ(v) R(u*+v)`, `R(u*)=1`, `R′(u*)=0`, `|log R| ≲ (θα/η)|v|²`, and `(θα/η)τ ≲ θ/η` is small. Hence `S(y) = F(u*)e^{−τℓ*²}(1+small)` and `S′/S = ℓ* + O((θα/η)√τ) = α(1+O(θ)) + o(α)`.

Constants: `ε ≍ η³`. Exceptional set from `exists_volume_not_zetaTypicalHeight_le_rpow`.

## Log
- 2026-11-06 — created; A26 verified, A36 started.
