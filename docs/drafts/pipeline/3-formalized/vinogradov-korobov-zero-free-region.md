# Vinogradov–Korobov zero-free region in Lean

- **ID:** vk-zfr
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean programme)
- **Source:** rh-goal-loop-opus-2026-09-29.md rows 214+; corpus Route-T chain (width `log^{-9/10}`)
- **Statement:** `ζ(σ+it) ≠ 0` for `σ ≥ 1 − c/((log t)^{2/3}(log log t)^{1/3+o(1)})`, `t ≥ t₀`.

## Goal
Move the corpus zero-free exponent (mean-spacing units) from `1/10` (Route-T, `log^{-9/10}`) to `1/3`.
Consumers: Möbius/PNT rates, MR corridor, seam contraction on the known zero-free region.

## Diagnosis of the Route-T ceiling (2026-10-03)
- `vinogradov_mean_value_bound` (Linnik/Bertrand reservoir recursion) has exponent
  `E_{r+1} = E_r + 2k − 2`: loss `Δ_r = k(k−1)/2 − 2r + 2`, admissible only up to `r ≈ k²/4`, so
  `Δ ≈ 2k` with `s = kr ≈ k³/4` variables.
- Cause: the colliding-block term `((k²−k)N^{k−1})² J_b(N)` (`card_vinogradovCollidingBlockCompletion_le_moment`)
  has exponent `E_b + 2k − 2` whatever `Δ_b` is. The good (injective) term already has the classical exponent
  `E_b + 2k − Δ_b/k`.

## Plan
1. **Collision by pair removal.** A noninjective block has `x_i = x_j`; removing the pair and using
   `finiteFiberCorrelation_le_energy` gives `#colliding completions ≤ (k²−k)² N² J_{k+b−2}(N)`.
2. **Exponential-decay VMVT.** Strong induction on all `s` with `λ(s) = 2s − K + K θ^s`, `K = k(k+1)/2`,
   `θ = (1−1/k)^{1/k}`: good term `θ^{s−k}(1−1/k) = θ^s` exactly; collision needs `K θ^{s−2}(1−θ²) ≤ 2`;
   base `s ≤ k` needs `Kθ^s ≥ K − s`. Both from `log(1−1/k) ≥ −1/(k−1)` for `k ≥ 3`.
   Result: `J_s(N) ≤ C_{k,s} N^{2s − K + K(1−1/k)^{s/k}}`; `s = k⌈k log K⌉` gives loss `≤ 1`.
3. Weyl sums for `n^{−it}` with saving `≍ 1/s` from `norm_vinogradovBilinearSum_pow_le_mixedProduct`
   (general `X, Y, b, k`), Taylor/shift steps from the Route-T chain.
4. Growth `ζ(σ+it) ≪ t^{B(1−σ)^{3/2}}` (up to `log` factors) and Landau discs → zero-free region.

## Log
- 2026-10-03 — created; diagnosis and plan above.
- 2026-10-03 — Steps 1–2 CLOSED in Lean (MUST-700): `card_vinogradovCollidingBlockCompletion_le_pairRemoval`,
  `vinogradov_moment_bertrand_recurrence_pairRemoval`, `exists_vinogradov_mean_value_decay`, `exists_vinogradov_mean_value_exp`.
- 2026-10-03 — Explicit constants CLOSED in Lean (MUST-702): `card_vinogradovDiagonalSolution_le_explicit`:
  `J_s ≤ z^{kK}Λ^s2^{s²/k}N^{λ(s)}`, `z = max(2²⁴,81R²,k)`, `Λ = 4R²k!16^{k²}` (Chebyshev reservoir in `(y,4y]`).
  Route-T's `log^{-9/10}` traced to its Bertrand constants `2^{k⁴}` per step forcing `log Q ≳ u⁶`.
  Next: Weyl sum for `n^{-it}` (shift `n ↦ n + lm`, `l,m ≤ Q`, Taylor to degree `k ≈ 2ρ+2`,
  `norm_vinogradovBilinearSum_pow_le_mixedProduct`, useful `j ∈ [ρ + sav/2, 2ρ + 1 − sav]`).
- 2026-10-03 — Step 3 CLOSED in Lean (MUST-705): `norm_sum_logPhase_le_vinogradov`:
  `‖Σ_{A<n≤A+L} n^{it}‖ ≤ 4M_r L P^{−δ_r} + 400P²` for `P^{4r} ≤ t ≤ P^{4r+4}`, `(A,A+L] ⊂ [4P⁴,162P⁴]`, `r ≥ 4`.
  Next (step 3b): `M_r ≤ M` absolute (`C_{k,b}^{2/(4b²)}` with `b ≥ k²`), `δ_r ≥ c/(r² log² r)` (`n_r⌊r/4⌋ ≥ r²/20` for
  `r ≥ 20`, `b ≤ 8r²·log₂(8r²)`). Then step 4: ζ growth near `σ = 1` (blocks `N ≤ t^{1/16}` via Vinogradov, larger
  via the third-derivative test `ThirdDerivativeTestSharp`), step 5: Landau discs.
- 2026-10-03 — Step 3b CLOSED (MUST-707): `norm_sum_logPhase_le_vinogradov_uniform` (`M ≤ e^{20}`, `δ_r ≥ 1/(5184r²m_r²)`, `r ≥ 22`).
  Large blocks (`N ≥ t^{1/88}`): corpus `dirichlet_block_bound` (k-th derivative test) with `k = ⌈ρ+1/2⌉`, `k−ρ ∈ [1/2,3/2]`.
  Landau: corpus `zeta_landau_of_bound` (general radius/growth).
- 2026-10-03 — Step 4 CLOSED (MUST-711): `norm_riemannZeta_le_vinogradovKorobov` (`‖ζ‖ ≤ C log τ` on `σ ≥ 1 − θ(log τ)`).
  Next: zero-free region via corpus `dlvp_inequality_of_bound` (R₀ = θ(log 5γ), R = R₀/2, δ = 7ε, ε = θ/(K log log γ)).
- 2026-10-03 — Step 5 CLOSED (MUST-713): `riemannZeta_ne_zero_vinogradovKorobov`:
  `ζ(β+iγ) ≠ 0` for `γ ≥ γ₀`, `β > 1 − (log γ)^{−2/3}(log log γ)^{−5/3}/10⁸`. Programme goal reached (exponent 2/3,
  loglog power 5/3 instead of the literature's 1/3 — cost of the classical VMVT with `s ≈ k² log k`).
  Modules: VinogradovCollisionPairRemoval, VinogradovMeanValueExponentialDecay, VinogradovChebyshevReservoir,
  VinogradovMeanValueExplicit, VinogradovBilinearExplicitSaving, VinogradovLogPhaseShift, VinogradovLogRatioExplicit,
  VinogradovLogPhaseWeyl, VinogradovWeylParameters, VinogradovDyadicBlock, VinogradovZetaGrowthLemmas,
  VinogradovZetaGrowthBlocks, VinogradovZetaGrowth, VinogradovKorobovZeroFree.

## Consumer: prime number theorem at VK strength (2026-10-03, MUST-717)

- `chebyshevPsi_sub_id_isBigO_vinogradovKorobov`: `ψ − id =O x·exp(−c(log x)^{3/5}(log log x)^{−5/3})`,
  `c = 1/(288·10⁸)`; real form `exists_abs_sum_vonMangoldt_sub_self_vk_rate`.
- Modules: VinogradovKorobovLogDeriv (two-sided region, `ζ'/ζ` bound, uniform regular-part bound),
  VinogradovKorobovChebyshevParameters (`vkScale`, height/saving/width, `eventually_vk_conditions`),
  VinogradovKorobovChebyshevContour (contour data, five-term shaping, smoothed rate),
  VinogradovKorobovPrimeNumberTheorem (bracket, sharp transfer, mass, absorption, final forms).
- Loglog exponent −5/3 (not the optimal −1 for this width, nor the literature's −1/5) because the
  height is chosen as `log T = κσ(N)` with `σ = L^{3/5}ℓ^{−5/3}` to keep every threshold elementary.

## Consumer: `1/ζ` and the Möbius sum at VK strength (2026-10-03, MUST-720)

- `exists_norm_inv_riemannZeta_le_vk`: `‖1/ζ(σ+it)‖ ≤ e^{49}(C log(t+1))^7(1+2/w(t+1))^7`,
  `σ ≥ 1 − w(t+1)/4` (Borel–Carathéodory via `RHTower.borel_caratheodory`,
  `exists_analyticOnNhd_exp_eq_ball`); uniform rectangles `exists_bound_invZeta_vk_uniform`.
- `sum_moebius_isBigO_vinogradovKorobov`: `M(x) =O x·exp(−c(log x)^{3/5}(log log x)^{−5/3})`.
- Modules: VinogradovKorobovInvZeta, VinogradovKorobovMoebius.
