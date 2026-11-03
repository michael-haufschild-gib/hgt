# The critical boundary adds its null directions

- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper; Lean in progress)
- **Wall:** Σ1k / A4, finite-family sign at jump thresholds.
- **Statement:** For every fixed linearly independent finite family of compact C² windows and every `K>0`, the tilted-spline horizon Gram matrix on the canonical clock eventually has inertia
  `(n₊(P_K), n₋(P_K)+n₀(P_K), 0)`.

Here `P_K` is the leading pencil. All its zero directions enter the negative phase, so the complete family counts jump multiples with `K_i≤K`, including equality. The starting index depends on the family.

## Paper proof

Let `G_N` denote the horizon Gram matrix normalized by the positive atom mass and overlap. Polarize the quadratic correction on `h_i+h_j` and `h_i−h_j`. On the exact critical clock,

`c_N²(P_K−G_N) → (D/K) C_10`,

entrywise, where `C_10(i,j)=∫e^(−10y)H_iH_j` and `D>0` is the next alias coefficient. Independence makes `C_10` positive definite. Finite-dimensional openness of positive definiteness therefore gives `G_N<P_K` for all sufficiently large `N`.

The sum of the negative and null eigenspaces of `P_K` has dimension `n₋(P_K)+n₀(P_K)` and nonpositive form. Strict decrease makes `G_N` negative definite on this whole subspace. Thus `n₋(G_N)≥n₋(P_K)+n₀(P_K)`. Meanwhile `G_N→P_K`, so lower semicontinuity gives `n₊(G_N)≥n₊(P_K)`. These two lower bounds exhaust the ambient dimension. Both are equalities and `n₀(G_N)=0`. Positive normalization preserves inertia.

## Novelty and Lean obligations

`TheWindowIndex` proves only `n₋(P_K)≤n₋(G_N)`; `TheWindowIndexCountsTheJumpMultiples` counts strict jumps of the limiting pencil. The new assertion includes its null directions in the complete family's eventual negative index. Required: polarize the proved scalar correction, prove strict-order passage on the nonpositive spectral subspace, assemble and audit the inertia identity.
