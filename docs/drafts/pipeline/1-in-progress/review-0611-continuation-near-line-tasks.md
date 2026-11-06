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
| A37 | done | `SquareRootThreshold/EffectiveHorizons/TheEGCContourIsExplicit.lean`: `Σ_{|γ|>T}|ρ|⁻² ≤ 4 log T/T` above `xiMassHeight (1/100)`; contour error `≤ 32ε² log T/T`; `egcHeight n` gives `< 1/(n+1)` |
| A33 | done | `RenormalizedIntersectionTheory/GaussMayerEffectiveBoundary.lean`: `norm_riemannZeta_boundary_lower`: `\|ζ(1+2it)\| ≥ 1/(50000 t³ log²(2t))` for `t ≥ 10⁷`; `norm_riemannZeta_one_add_mul_I_lower`. Maass–Selberg norm against the exact Mellin test of the first Whittaker mode; no Euler product |
| A25 | done | `ZeroConfigurationGeometry/HeatScaleRepulsion/TheSharpDepthLaw.lean`, `TheQuotientByAnIsolatedZero.lean`: `localNewman_scaled_mem_Icc`: `d − 7η ≤ Λ_X log(X/2π) ≤ d + 17η` on a window of depth `d` around a simple isolated zero of depth `d ≥ 30η` (`IsolatedZero`, `depthWindow`, level `η³/40000`). Mechanism: `c H_τ = (½+iz−ρ) 𝓖 + 2τ D` for `Λ = cξ/(s−ρ)`, so zeros of `H_τ` are fixed points of a holomorphic map of a disc |
| A23, A27–A32, A34, A35 | not started | stopped on request |

## Log
- 2026-11-06 — created; A26 verified, A36 started.
- 2026-11-06 — A33, A25 formalized; work stopped on request with the remaining tasks not started.
