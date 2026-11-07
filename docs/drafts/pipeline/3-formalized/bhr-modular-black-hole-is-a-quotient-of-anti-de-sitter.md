# BHR — the modular black hole is a quotient of the Rindler wedge of AdS₄

- **ID:** bhr-local-ads4 (review-0711 A27, first item)
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** `Φ(t,r,x,y) = (r Y(x,y), √(r²−1) cosh t, √(r²−1) sinh t)`, `Y = ((x²+y²+1)/2y, (x²+y²−1)/2y, x/y)`, maps the exterior `r>1, y>0` of `−(r²−1)dt² + dr²/(r²−1) + r²(dx²+dy²)/y²` bijectively and isometrically onto the wedge `{−X₀²+X₁²+X₂²+X₃²−X₄² = −1, X₃>|X₄|, X₀>X₁}` of AdS₄ ⊂ ℝ^{3,2}, and `Φ(t,r,γz) = Λ_γΦ(t,r,z)` with `Λ_γ` an isometry of ℝ^{3,2} for `γ ∈ SL₂(ℤ)`.

## Proof
`⟨Y,Y⟩₂,₁ = −1` and `cosh²−sinh² = 1` put `Φ` on the quadric. The Gram matrix of the coordinate derivatives: `⟨∂_t,∂_t⟩ = −(r²−1)`, `⟨∂_r,∂_r⟩ = ⟨Y,Y⟩ + r²/(r²−1) = 1/(r²−1)`, `⟨∂_x,∂_x⟩ = ⟨∂_y,∂_y⟩ = r²/y²`, mixed terms vanish (`⟨Y,∂Y⟩ = ½∂⟨Y,Y⟩ = 0`). Inverse: `r = √(1+X₃²−X₄²)`, `t = arsinh(X₄/√(X₃²−X₄²))`, `y = r/(X₀−X₁)`, `x = X₂y/r`. Equivariance: with `M = (1/y)[[x²+y², x],[x,1]]`, `M(γz) = γMγᵀ` (entry `11` uses `N²+y² = |az+b|²|cz+d|²`, i.e. `ad−bc=1`), and `M ↦ γMγᵀ` multiplies `det M = −⟨Y,Y⟩` by `det γ²`.

## Lean
`formal/GaloisForLFunctions/BlackHoleRingdown/TheModularBlackHoleIsAQuotientOfAntiDeSitter.lean`: `ambientForm_adsEmbedding`, `hasDerivAt_adsEmbedding_t/r/x/y`, `ambientForm_partial`, `adsEmbedding_mem_wedge`, `adsEmbedding_injective`, `exists_adsEmbedding_eq`, `ambientForm_ambientLorentz`, `hyperboloid_moebius`, `adsEmbedding_smul`. Checked with `lake --old env lean`.

## Scope
Local geometry only: the arithmetic of the horizon lies entirely in the discrete group `SL₂(ℤ) ⊂ SO(2,1) ⊂ SO(3,2)`.
