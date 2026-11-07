# BHR — Zagier's theorem: the horocycle rate is the zero-free region

- **ID:** bhr-zagier-horocycle (review-0711 A27, Zagier–Sarnak item)
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** For `φ` smooth with compact support in `(1,∞)`, let `F_φ(z) = Σ_{(c,d)=1} φ(Im M_{c,d}z)` (pseudo-Eisenstein series, `SL₂(ℤ)`-invariant) and `A_φ(y) = ∫₀¹ F_φ(x+iy) dx`. Then:
  1. for `Re s > 1`, `∫₀^∞ A_φ(y) y^{s−2} dy = 2φ̃(s−1) + 2(Λ(2s−1)/Λ(2s)) φ̃(−s)`;
  2. (converse) if `‖A_φ(y) − c_φ‖ ≤ C_φ y^α` on `(0,1]` for every such `φ` (any constants), every zero of `ζ` with `Re ρ > 0` has `Re ρ ≤ 2 − 2α`;
  3. (forward) if `ξ` has no zeros in `Re z > θ` and `1/ζ` is polynomially bounded on each `θ+δ ≤ Re z ≤ d`, `|Im z| ≥ 2`, then `‖A_φ(y) − (6/π)∫φ(y)y^{−2}dy‖ ≤ C y^{1−θ/2−ε}`. Unconditionally (`θ = 1`): rate `y^{1/2−ε}`. Under RH (`θ = ½`): rate `y^{3/4−ε}`;
  4. RH ⟺ for every `ε>0` and every such `φ`, `A_φ(y) = c_φ + O(y^{3/4−ε})`.

## Proof
1. `∫ A_φ y^{s−2} = ∫_strip F_φ Im^s` (Fubini on the strip). Unfolding the strip over coprime rows and `F_φ(M_v z) = F_φ(z)` give `½∫_𝒟 F_φ Σ_v Im(M_v z)^s`; the row sum is `2E*(z,s)/Λ(2s)`. On `𝒟` only the rows `(0,±1)` reach height `> 1`, so `F_φ = 2φ∘Im` there, and the band integral against `E*` is the constant term `Λ(2s)y^s + Λ(2s−1)y^{1−s}`.
2. `A_φ − c1_{(0,1]}` has Mellin transform holomorphic on `Re s > 1−α`. By (1) and the identity theorem on the convex quarter plane `Re s > max(1−α,0)`, `Im s > 0`: `Λ(2s)(M(s) + c/(s−1) − 2φ̃(s−1)) = 2Λ(2s−1)φ̃(−s)`. At `s₀ = ρ/2` (`Im ρ > 0` by conjugation; no real zeros in `(0,1)`) the left side vanishes and `Λ(ρ−1) = Λ(2−ρ) ≠ 0`, so `φ̃(−s₀) = 0` for every bump. The fundamental lemma of the calculus of variations makes `y^{−s₀−1}` vanish a.e. on `(1,∞)`, impossible.
3. With `Q(s) = sξ(2s−1)/ξ(2s)`, `Λ(2s−1)/Λ(2s) = Q(s)/(s−1)`; set `c = 2Q(1)φ̃(−1) = (6/π)φ̃(−1)` and `N(s) = 2Q(s)φ̃(−s) − cΓ(s)`, `N(1) = 0`. Then `Ψ(w) = 2φ̃(w) + dslope N 1 (w+1)` is the Mellin transform of `A_φ − ce^{−y}` on `Re w > 0`, holomorphic on `Re w > θ/2−1`, and decays faster than every power on closed substrips: `φ̃` by iterated Euler integration by parts; `Q(s) = (s−1)(Γℝ(2s−1)/Γℝ(2s))ζ(2s−1)ζ(2s)⁻¹` polynomially (`|Γℝ(2s−1)/Γℝ(2s)| = √π|Γ(s−½)||Γ(s)|⁻¹` with the corpus strip bounds for `Γ` and `1/Γ`); `Γ(s)` exponentially. Mellin inversion on `Re w = 1`, shift to `Re w = θ/2−1+ε`, and `|e^{−y}−1| ≤ y`.
4. (2) with `α = 3/4−ε` for all `ε`, and (3) with `θ = ½` (RH gives `ξ(z) ≠ 0` off the critical line and `|1/ζ| ≪ |t|` from `exists_invZeta_shift_data_of_rh`).

The exponent dictionary is `α = 1 − θ/2`: `3/4 = 1/2 + 1/4`, the volume exponent plus the universal rate, matching the graph form `ArithmeticScatteringHolography.horocycle_rate_iff`.

## Lean
- `formal/GaloisForLFunctions/BlackHoleRingdown/TheHorocycleReadsTheZeros.lean`: `pseudoEisenstein`, `horocycleMean`, `pseudoEisenstein_smul`, `pseudoEisenstein_of_mem_fd`, `integrableOn_stripIntegrand`, `mellinConvergent_horocycleMean`, `two_mul_setIntegral_stripIntegrand`, `mellin_horocycleMean` (1); `msB_mul_mellin_eq_zero_of_rate`, `msB_ne_zero_of_zero`, `re_le_of_horocycle_rate` (2); `riemannHypothesis_of_horocycle_rate`.
- `formal/GaloisForLFunctions/BlackHoleRingdown/TheHorocycleRateIsTheZeroFreeRegion.lean`: `exists_norm_mellin_le_decay_pow`, `scatterQ`, `msB_div_msA_eq`, `scatterQ_eq`, `exists_norm_scatterQ_le`, `continuousAt_horocycleMean`, `regularPart`, `mellinRegularStrip_regularPart`, `mellin_sub_exp_eq_regularPart`, `norm_horocycleMean_sub_le_of_zeroFree`, `residueConst_eq` (3); `horocycle_rate`, `horocycle_rate_of_riemannHypothesis`, `riemannHypothesis_iff_horocycle_rate` (4).
- Both checked with `lake --old env lean`; `#print axioms` on `riemannHypothesis_iff_horocycle_rate` and `horocycle_rate`: `propext, Classical.choice, Quot.sound`.

## Scope
The test functions are pseudo-Eisenstein series with profile supported above height `1`. The unconditional rate is `y^{1/2−ε}`; Sarnak's exact `y^{1/2}` would need the shift onto `Re s = ½` itself, where `ξ(2s)` has no zeros but no open zero-free strip exists.
