# HCF spectral dictionary: heat windows compute even Weil Rayleigh quotients

- **ID:** C600
- **Stage:** 3-formalized
- **Type:** THEOREM (MUST-1289)
- **Source:** hcf-exact-layer-loop rows 593–600; MUST-1261, 1274, 1285
- **Statement:** For every smooth even pole-free source u of half-width A with A² < 4K, there are real hyperplane polynomials P_n (deg ≤ n) with Re H_{K/n}(P_n,P_n) → Re Σ F_u(z_q)² and ∫ heatTest(K/n, P_n)² → ∫u². Hence the limsup of the hyperplane ground Rayleigh quotient at window K is at most the even Weil ground energy at any half-width < 2√K. With an ε-sharp MUST-1261 (margin μ − ε in place of μ/4, even sector), the limit equals the even Weil ground energy at 2√K whenever the latter is continuous there.

## Goal
HCF becomes a provably convergent Hermite–Galerkin scheme for the even Weil ground energy, with truncation error (θe^{1−θ})^{2n}. Not a producer: a structural law. It makes certified window computations equivalent to certified Weil-energy computations.

## Approach
1. Heat smoothing converges in L²: |u_a − u| ≤ ‖u'‖_∞ √(2a/π) on |x| ≤ 2A, and Gaussian tails outside (`abs_heatSmooth_le_of_far`).
2. The sharp-witness error → 0 (witnessErr ≤ ξC₀ for every ξ, eventually), so Re H(P_n) → Re ΣF_u².
3. ∫ g_n² → ∫ u² from witnessE1 → 0 and step 1.
4. Sharpen MUST-1261 with even margin and ε-slack.

## Log
- 2026-10-12 — created after the producer-status check (row 600).
- 2026-10-12 — steps 1–3 proved in Lean (MUST-1289), module `RHTower/XiGaussianHeatSpectralDictionary`, standard axioms. Main statements: `eventually_exists_poleHyperplane_near_source` (energy and L² within ε) and `eventually_exists_poleHyperplane_rayleigh_lt` (Rayleigh form). Step 4 (ε-sharp converse) is open; the existing converse MUST-1261 loses a factor 4, so the window ground energy is bracketed but not pinned.

## Paper proof (as formalized)
1. u_a → u in L²: pointwise by the Gaussian average u_a(x) = ∫u(x − √a σ)φ(σ)dσ; dominated by (2B)² on |x| ≤ max(2A,1) and by (2U₁(2π)^{-1/2})² e^{−2x²} outside, since (2πa)^{-1/2}e^{−x²/(8a)} ≤ 2(2π)^{-1/2}e^{−x²} for a ≤ 1/16 and |x| ≥ 1 (√y e^{−y} ≤ 1/2 with y = 1/(16a)).
2. The corrected test is g − cG_a with c = P₀(−1/4), and |c| ≤ ∫|g − u_a|e^{|x|/2} ≤ ι + √E σG + τ. Each of ι, σ, τ is at most ξ/Y. Since ∫G_a² = (2πa)^{-1}√(πa) ≤ Y², we get ∫(g_P − u_a)² ≤ 2e₁ + 2c²∫G_a² ≤ ξ²(2 + 2(2 + √E G)²).
3. The energy error is ≤ ξC₀, as in MUST-1274. The source energy Σ F_{u_a}² → Σ F_u², and the triangle inequality finishes the proof.
4. Rayleigh form: |∫g² − ∫u²| ≤ (1 + 1/t)∫(g − u)² + t∫u².
- 2026-10-12 — step 4 done (MUST-1291), module `RHTower/XiGaussianHeatWindowSpectralIdentity`. The even-floor converse is ε-sharp and holds for floors of any sign. `heatWindow_spectral_bracket` traps the window ground Rayleigh quotient in [μ_A − ε, R(u) + ε], so the window ground energy equals the even Weil ground energy m(2√K) at continuity points of m. Conditioning (CANNOT-507): m(A) ≤ C e^{12A} e^{−π e^{2A−1/2}}.
