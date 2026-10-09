# Burnol's multiplicity-weighted lower bound for the Báez-Duarte distances

- **ID:** baez-duarte-burnol-multiplicity
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean, unconditional, standard axioms; MUST-872, MUST-874)
- **Source:** frontier map, "Other receivers and falsifiers", Báez–Duarte row: "full multiplicity-weighted lower bound not asserted"; Opus loop row 635.
- **Statement:** For every critical zero `ρ` (`Re ρ = ½`, `Im ρ > 0`) of multiplicity `m`,
  `liminf_{N→∞} d_N² log N ≥ 2m²/|ρ|²`. Summed over all critical zeros, `liminf d_N² log N ≥ Σ_ρ 2m_ρ²/|ρ|²`.
  The corpus has the multiplicity-blind version (`eventually_le_bdDistDiscrete_sq_mul_log_of_lt_tsum`).

## Paper proof

Notation: `ψ = Smooth1 ν ε`, `Y = N^{1+η}`, `L = log Y`. Duals `a_{ρ,j}(k) = (log k)^j k^{−ρ}ψ(k/Y)`, `j < m`. Dual-sequence inequality (corpus `one_le_bdDistDiscrete_sq_mul_energy`): `1 ≤ d_N²·E(A)` for every real `A` with `A_1 = 1`, `A` supported in `[1,K]`, and exact divisor constraints for `2 ≤ m' ≤ N`. Defects are repaired by the corpus Möbius correction at bounded energy.

1. **Defects of log-weighted duals (Cauchy estimates).** For any `ρ` in a closed disc `B̄(ρ₀, r)` inside `{¼ < Re < ¾}`,
   `Σ_n n^{−ρ}ψ(n/X) = ζ(ρ) + c(ρ)X^{1−ρ} + E_ρ(X)` with `|E_ρ(X)| ≤ C X^{−A}`, uniformly on the disc.
   This is the corpus Perron shift with the residue `ζ(ρ)ν̃(0) = ζ(ρ)` at `s = 0` kept.
   - The divisor defect is `D_{m'}(ρ) = Σ_{m'|k}a_ρ(k) − (1/m')Σ_k a_ρ(k)`. The main terms cancel, as in the corpus, so `D_{m'}(ρ) = ζ(ρ)(m'^{−ρ} − 1/m') + R_{m'}(ρ)` with `|R| ≤ 2C m'^A Y^{−A}` on the disc.
   - `D_{m'}` is entire in `ρ` (finite sums), so `R_{m'}` is holomorphic on the disc. The log-weighted defect is `(−∂_ρ)^j D_{m'}` at `ρ₀`.
   - The first term contributes `Σ_i C(j,i)ζ^{(i)}(ρ₀)(…) = 0` for `j < m`. Cauchy gives `|R^{(j)}(ρ₀)| ≤ j!r^{−j}·2Cm'^AY^{−A}`.
2. **Energy of polynomial-log duals.** For a real polynomial `p` and `P(t) = p(t/L)`, the dual `A_k = Re(P(log k)k^{−ρ})ψ(k/Y)` satisfies
   `E(A) ≤ (|ρ|²/2)·L∫_0^1 p² + O_p(1)`, uniformly in `Y ≥ e`.
   - The increments are `Re((ρP − P′)k^{−ρ−1})ψ + O(k^{−3/2}·(…))`.
   - `Re(z)² = (|z|² + Re z²)/2`. The `Re z²` terms carry the phase `k^{−2iγ}` and are bounded by Abel summation with bounded-variation weights.
   - The main term is `Σ(ψ²/2k)|ρP(log k) − P′(log k)|² ≤ (|ρ|²/2)L∫_0^{1+o(1)}p² + O(1)`, since `P′ = O(1/L)`.
3. **Legendre optimum.** With `c_j = (−1)^jC(m,j+1)C(m+j,j)/m` and `p_m = Σ_{j<m}c_jx^j`, `p_m(0) = 1`, the reproducing identity is
   `∫_0^1 p_m x^i dx = [i = 0]/m²` for `i < m`. This is the partial-fraction identity `Σ_j c_j/(z+j+1) = ∏_{k=1}^{m−1}(z−k)/(m·∏_{k=1}^m(z+k))·(−1)^{m−1}(m−1)!·…` evaluated at `z = i`; check normalisation at `z = 0`. Hence `∫_0^1 p_m² = c_0/m² = 1/m²`.
4. **Assembly.** `A = Re Σ_j c_jL^{−j}a_{ρ₀,j}`, i.e. `P(t) = p_m(t/L)`, plus the Möbius correction. Then `1 ≤ d_N²((|ρ|²/2)(1+η)log N/m² + K)`, and `η → 0`. For several zeros use weights `λ_ρ ∝ m_ρ²/|ρ|²`; the cross energies of distinct zeros are `O(1)` (both phases oscillate).

Checks: `m = 1` recovers the corpus bound (`p₁ = 1`). For `m = 2`, `p₂ = 1 − 3x/2` and `∫p₂² = 1/4`. For `m = 3`, `p₃ = 1 − 4x + (10/3)x²` and `∫p₃² = 1/9`.

## Lean plan
- M1 `ZetaSmoothedPartialSumsUniform`: uniform-in-`ρ` version of `exists_norm_tsum_smooth1_zeroCoeff_sub_le` with the `ζ(ρ)` residue.
- M2 `BaezDuarteLogDualDefect`: Cauchy estimates give defect bounds for `a_{ρ,j}`, `j < m`.
- M3 `BaezDuarteLogDualEnergy`: energy upper bound for `Re(P(log k)k^{−ρ})ψ`.
- M4 `LegendreEndpointExtremal`: `p_m` and `∫_0^1 p_m² = 1/m²`.
- M5 `BaezDuarteBurnolMultiplicity`: assembly, single zero, then all zeros.

## Lean status
- M1 `ZetaSmoothedPartialSumsDisc.exists_norm_tsum_smooth1_cpow_sub_le_disc` [L].
- M2 `BaezDuarteLogDualDefect.exists_norm_bdModDefect_logZeroSmoothDual_le` [L].
- M3 `BaezDuarteLogDualEnergy.exists_bdDualEnergy_polyLogDual_le` [L].
- M4 `HTGeometry/LegendreEndpointExtremal.integral_endpointExtremalPoly_sq` [L] (built by hgt-8a).
- M5 single zero: `BaezDuarteBurnolMultiplicity.eventually_le_bdDistDiscrete_sq_mul_log_of_analyticOrderAt` [L], standard axioms. The hypothesis is `(m : ℕ∞) ≤ analyticOrderAt riemannZeta ρ`.
- Cross energies: `BaezDuarteLogDualCrossEnergy.exists_bdDualBilin_polyLogDual_le_of_ne` [L].
- M5 finite sets: `BaezDuarteBurnolMultiplicity.eventually_le_bdDistDiscrete_sq_mul_log_of_multipleZeros` [L].
- M5 all zeros: `BaezDuarteBurnolMultiplicityAllZeros.eventually_le_bdDistDiscrete_sq_mul_log_of_lt_tsum_order` [L]. The sum is in `[0, ∞]` with `m_ρ = analyticOrderNatAt ζ ρ`, so no summability input is needed.

## Log
- 2026-10-09 — card created; paper proof complete modulo the partial-fraction identity in step 3. Values checked for m = 1, 2, 3.
- 2026-10-09 — M1–M5 single-zero in Lean (MUST-872).
- 2026-10-09 — cross energies and all-zeros sum in Lean (MUST-874); moved to 3-formalized.
