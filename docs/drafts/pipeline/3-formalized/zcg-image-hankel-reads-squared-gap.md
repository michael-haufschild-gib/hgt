# The image Hankel determinant reads the squared gap of a near-coincident pair

- **ID:** zcg-image-hankel-reads-squared-gap
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** docs/reports/review-0411/obstacles-summary_v2.md §2.5.5 (B44 in prime form) · ZCG README §6 Q3
- **Statement:** Let `Z` be a tempered configuration with Riemann–von Mangoldt local counts at
  height `T`, and `p₁, p₂` the only points of `Z` (simple, or one double point) in a disc of radius
  `r ≤ T^{−(M' + κ_λ + 1)}`, with all other points `T^{−M'}`-far. Then three window images
  `W_j = Z.W F_j G` of aperture `λ · ½ log(T/2π)` satisfy
  `|4(W₁² − W₀W₂)/W₀² − (γ_{p₁} − γ_{p₂})²| ≤ pairReadError r δ₀ δ₁ δ₂`, with
  `δ_j = 2r^{j+1} T^{M' + κ_λ} + e^{−K' log³(T/2π)}`, uniformly in `T`.

## Goal
Reality of near-coincident pairs (B44) as a statement about the image alone. An on-line pair has
squared gap `(Im p₁ − Im p₂)² > 0`, an FE pair `−4(Re p₁ − ½)² < 0`. So, once the gap exceeds the
error, the sign of `Re 4(W₁² − W₀W₂)/W₀²` decides which. For `ζ` the image values are the arithmetic
side of the explicit formula.

## Proof
1. **Readout.** Compare `Z` with the empty configuration. The relative moment theorem
   (`discMoment_readout_slow`, at polynomial scale `discMoment_readout_rvm`) gives windows `F_j, G`
   and the image `Φ` at the target with `m_j := W_j/((−i)^j Φ)` and `|m_j − μ_j| ≤ δ_j`, where
   `μ_j = Σ_{disc} (γ_z − ω)^j`. For the pair, `μ₀ = 2`, `μ₁ = a₁ + a₂`, `μ₂ = a₁² + a₂²` with
   `a_i = γ_{p_i} − ω`, `|a_i| ≤ r`.
2. **Hankel determinant.** `μ₀μ₂ − μ₁² = (a₁ − a₂)²`. Writing
   `m₀m₂ − m₁² − (a₁ − a₂)² = (m₀ − 2)(μ₂ + (m₂ − μ₂)) + 2(m₂ − μ₂) − (m₁ − μ₁)(2μ₁ + (m₁ − μ₁))`
   gives `|m₀m₂ − m₁² − w²| ≤ ε_H = δ₀(2r² + δ₂) + 2δ₂ + δ₁(4r + δ₁)`.
3. **Normalization.** `|m₀ − 2| ≤ δ₀ ≤ 1` gives `|m₀| ≥ 1` and `|4 − m₀²| ≤ 5δ₀`, so
   `|4h/m₀² − w²| ≤ (4r² + ε_H)·5δ₀ + ε_H` for `h = m₀m₂ − m₁²`. Since `(−i)² = −1`, `Φ` cancels:
   `4h/m₀² = 4(W₁² − W₀W₂)/W₀²`.
4. **Types.** `γ_{1 − ρ̄} = conj γ_ρ` gives `w² = −4(Re ρ − ½)²` for an FE pair; on the line `γ` is real.

The error is `O(r³ T^{M' + κ_λ}) + O(e^{−K' log³ T})` (with `rT^{M' + κ_λ} ≤ T^{−1}` and
`e^{−K' log³ T} ≤ ½` for `K' ≥ 1`).

## Lean
`formal/GaloisForLFunctions/ZeroConfigurationGeometry/TheImageHankelReadsTheSquaredGap.lean`:
`pairReadError`, `norm_hankel_sub_le`, `hankel_ratio_eq`, `sq_gammaOf_sub_reflect`,
`sq_gammaOf_sub_of_onLine`, `pair_hankel_rvm`, `pair_type_of_hankel`. Readout layer in
`IsolatingWindowsVarySlowlyAtTheirTarget.lean`: `discMoment_readout_slow`, `rvm_readout_core`,
`discMoment_readout_rvm`. Unconditional.

## Clusters of `k` points
The moment Hankel matrix `(μ_{i+j})_{i,j<k}` is `VᵀV` for the Vandermonde matrix of the cluster,
so `det = Π_{i<j}(a_j − a_i)²` (`HTGeometry.det_powerSum_hankel`). Rescale the entries by
`r^{i+j}`. The rescaled exact entries are `≤ k`, and the read entries are within
`δ = krT^{M' + κ_λ} + E/r^{2k−2}`, so the Leibniz expansion bounds the determinant error by
`(Π_i r^i)² k! · kC^kδ`, `C = k + δ`. The factor `(k/m₀)^k` costs `2^{k+1}(krT^{M' + κ_λ} + E)`.
The image discriminant `(k/W₀)^k (Π_i (−i)^{−i})² det(W_{i+j})` is free of the normalization `Φ`.
Lean: `TheImageReadsTheDiscriminantOfACluster.lean` (`norm_det_sub_le`, `det_hankel_scale`,
`imageDiscriminant_eq`, `cluster_disc_of_moments`, `cluster_discriminant_rvm`).

## Locating the points
Heine's formula: `det[x^j; μ_{i+j}]_{i<k, j≤k} = Disc(a) Π_l (a_l − x)`. The bordered matrix is
`C · V(x, a)`, with `V` the Vandermonde matrix of `(x, a₀, …)` and `det C = det V(a)` by Laplace
expansion along the first row. Splitting `det V(x, a)` with `Fin.prod_Ioi_zero` and
`Fin.prod_Ioi_succ` gives the formula. With read moments to order `2k − 1`, rescale rows and columns
by `r^i`, `r^j`. The rescaled entries are within `δ = krT^{M' + κ_λ} + E/r^{2k−1}`, so the read
polynomial is within `(Π_{j≤k} r^j)(Π_{i<k} r^i)(k+1)!(k+1)C^{k+1}δ` of `Disc Π(a_l − x)` on the
disc. A zero `x` then has `|Disc| Π|a_l − x| ≤ R`, so `min_l |a_l − x|^k ≤ R/|Disc|`. Lean:
`TheImageLocatesTheClusterPoints.lean` (`det_bordered_hankel`, `bordered_of_moments`,
`exists_near_point_of_bordered_zero`, `cluster_location_rvm`).

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven
- [x] 2 → 3  formalized

## Log
- 2026-11-05 — created; formalized
