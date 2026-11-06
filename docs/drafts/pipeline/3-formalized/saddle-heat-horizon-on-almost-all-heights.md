# The heat horizon reaches the saddle on almost all heights

- **ID:** saddle-heat-horizon-on-almost-all-heights
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** review-0511 §2.1, A51.
- **Statement:** for `0 < ε ≤ ¼` there are `C, T₀` with
  `|{X ∈ [T, 2T] : Λ_X > (½+ε)/log((X−1)/2π)}| ≤ C T^{1−ε²/32}` for `T ≥ T₀`.
- **Lean:** `GaloisForLFunctions/ZeroConfigurationGeometry/HeatScaleRepulsion/TheSaddleHorizonOnAlmostAllHeights.lean`:
  `exists_volume_localNewmanConstant_gt_le`; standard axioms only.

## Proof

1. The half-Gauss engine uses its Euler-anchored comparison only at the height of the zero, so
   `re_slope_zero_and_ne_zero_of_profile` now takes that comparison at one height `X`.
2. If `|ζ| ≤ 2X^e` on `½ ≤ Re s ≤ 1 + ε/4` at height `X`, Stirling for `Γ` and the Euler lower bound for
   `ζ` give the comparison with the constant profile `E ≡ e` (`norm_xiLine_le_of_norm_zeta_le`).
3. For `e = ε²/32`, `δ₀ = ε²/16`, `m = 3ε²/8` the margin
   `(c−w)² − 4ce − 2δ₀c ≥ m` holds for all `c ≥ ½ + ε`, `0 ≤ w ≤ ½ + ε/4` (`typical_margin`). So `H_t` has no
   non-real zero at such a height once `X ≥ 2πe^{(½+ε)/t}`.
4. If this holds on the unit window about `X`, then `Λ_X ≤ (½+ε)/log((X−1)/2π)`.
5. `exists_volume_zetaLargeNear_le_rpow` bounds the bad heights by `O(T^{1−e})`.

## Limit

The saddle at `t = (½+ε)/log X` lies at `Re s = 1 + ε`, right of the Euler boundary. So `½` is the limit
of this anchor, and B73 (`Λ_X log X → 0` on density-one heights) needs a different source.
