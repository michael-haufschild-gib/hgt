# WD heat: per-pair positivity and λ_WD ≤ 1/12

## Claim
For every height t and λ ≥ 1/12, the x-heated slice e^{(λ/2)∂_x²}S_0(t,·) of Ξ has nonnegative
Taylor coefficients. More generally (heated hyperbola criterion): if every zero ζ of an even real
order-one entire f satisfies (Im ζ)² ≤ (Re ζ − t)² + 6s, then e^{s∂_x²}S^f(t,·) is coefficient-positive.

## Paper proof
1. Product closure. For polynomials, heat s (heat(−s)A · heat(−s)B) = Σ_k (2s)^k/k! A^{(k)}B^{(k)}.
   Proof by induction on deg B: heat s (X p) = X heat s p + 2s D heat s p (and with −s);
   L(a, X b') = X L(a,b') + 2s L(Da, b'); both sides satisfy the same recursion; base B constant uses
   heat s ∘ heat(−s) = id. Hence heat s A, heat s B ≥ 0 ⇒ heat s (AB) ≥ 0 (s ≥ 0).
2. Factors. Pair z = a + ic at offset d = a − t: |w|²(1 + x²/w)(1 + x²/w̄) = x⁴ + 2Qx² + R², Q = d² − c²,
   R = d² + c²; heat s: x⁴ + (12s + 2Q)x² + (12s² + 4sQ + R²) ≥ 0 iff 6s ≥ c² − d² (constant term
   ≥ (Q + 2s)² + 8s²). Real zero: 1 + (x² + 2s)/w ≥ 0.
3. Limit. Hadamard partial products over conjugation-closed sets; uniform bound
   |Π(1 + x²/w_q)| ≤ (1 + |x|²/m²)^{N_K} e^{ε(K)|x|²} with ε(K) → 0 (tail of Σ1/|z_q − t|²); Tannery /
   dominated convergence for the heat series (needs 4sε < 1); generic t (not a zero ordinate),
   then continuity of T_n(λ,0,t) in t.
4. Ξ: (Im ζ)² < ¼ ≤ 3λ for λ ≥ 1/12.

## Lean plan
- Stage A: `PolynomialHeatProduct.lean` (polyHeat, semigroup, X-commutation, product identity, closure).
- Stage B: factor positivity; finite products.
- Stage C: limit to Ξ (uniform bound, exchange).
- Stage D: `xiSliceHeatTransfer_nonneg_twelfth`, `wdHeatThreshold_le_twelfth`, heated hyperbola.

## Status
- 2026-10-11: paper proof done (rows 273/274); Stage A started.
- 2026-10-11: Stage A DONE [L] `HTGeometry/PolynomialHeatProduct.lean`: `forwardPolyHeat` (= `polyHeat (−s)`), `forwardPolyHeat_X_mul`, `heatPair`, `derivative_heatPair`, `heatPair_X_mul_right`, `forwardPolyHeat_mul` (product identity), `coeffNonneg_forwardPolyHeat_mul/_prod` (closure). Standard axioms; wired into HTGeometry.
- 2026-10-11: Stages B–D DONE [L]. `HTGeometry/PolynomialHeatFactorBounds.lean` (heated quadratic factors, factorial coefficient bounds, heat-weight summation); `RHTower/XiSliceHeatPerPairPositivity.lean` (`xiSliceHeatTransfer_nonneg_of_heatedCone`, `xiSliceHeatTransfer_nonneg_of_im_sq_le`, `wdHeatThreshold_le_twelfth`). All standard axioms, wired. Open extension: x₀-shifted (heated hyperbola) version e² ≤ d² + x₀² + 3λ, giving the trade-off curve x₀² + 3λ = ¼.
- 2026-10-11: x₀-extension DONE [L] (row 275): heated hyperbola criterion and trade-off curve x₀² + 3λ = ¼ (`xiSliceHeatTransfer_nonneg_perPair`). Card complete at stage 3 (formalized); remaining question is beyond per-pair: compensation (WD-KKL, below).
- Next conjecture (WD-KKL): for every λ > 0 there is T with T_n(λ,0,t) ≥ 0 for all n and |t| ≥ T. Mechanism sketch: heat caps the curvature of any cluster of exposed zeros at 1/(4s) while the bulk atom mass Σ1/|z−t|² ≳ log t (dense-lattice model: threshold ≈ e/(3 log t)). Corpus inputs: KKL finiteness `riemannHeat_nonreal_zeros_finite`, large-height H_λ slice positivity `exists_nonnegTaylorAtZero_riemannHeat_slice`, high-order positivity `exists_xiSliceCoeff_pos_high_order` (c_{2k}(t) > 0 for k ≥ max(K, κ log t), which already gives T_n(λ,0,t) ≥ 0 for n ≥ 2max(K, κ log t)). Open core: the orders n < 2κ log t, uniformly in t.
- 2026-10-11: consolidated into 3-formalized/wd-heat-threshold-theory.md (stage 3).
