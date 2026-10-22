# Computer-free Weil positivity at the prime-2 threshold: the bathtub certificate

- **ID:** WEIL-BATHTUB-001
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper) → Lean
- **Source:** weil-polar-bombieri-yoshida-prime-two-entry.md (P2); weil-positivity-soft-prime-entry.md (Theorem D)
- **Statement:** `ccmRestrictedWeilPolarGroundEnergy ((log 2)/2) ≥ κ₀ > 0` with an explicit rational `κ₀`,
  proved without numerical computation; hence (Theorem D, Lean) pole-vanishing Weil positivity holds on
  `[λ⁻¹, λ]` for all `λ < λ₁` with some `λ₁ > √2`, the prime 2 included.

## Literature position (Sept 2026)
Connes–Consani 2021 (positivity at `√2`, one computer-checked L¹ estimate, margin 0.3 %);
arXiv 2608.24827 (Aug 2026): interval-arithmetic certificate on support `[−0.8, 0.8]`, margin `8.9e−18`,
Landau–Widom decay `−ln λ_min(L) ~ 2π²N(T*)/ln N(T*)`. New here: a proof with no computer step and an
order-one margin at `√2`. No RH content (CANNOT-330; the margin decays doubly exponentially).

## Paper proof

Notation: `a = (log 2)/2`, `S = 2a = log 2`, `u` a real smooth core on `(−a, a)` with
`∫ e^{±x/2} u = 0`, `g = u ⋆ u`, `F(ξ) = |𝓕u(ξ)|²`, `η = 2πξ`, `θ = aη`.

1. **Form.** `Q(u) = ∫ F(ξ) m_S(2πξ) dξ` (corpus `suzukiRestrictedWeilForm_eq_integral_multiplier_of_moment_eq_zero`),
   `m_S = A(S) + Λ_S − 2 w₂ cos(η log 2)`. Since `supp u ⊂ [−r, r]`, `r < a`, `g(log 2) = 0`, so
   `Q(u) = ∫ F · M`, `M(η) = A(S) + Λ_S(η)`.
2. **Bathtub.** If `w ≥ 0` is bounded measurable and `M ≥ t − w`, then `Q(u) ≥ t g(0) − ∫ F w`.
3. **Pointwise constrained Fourier bound.** For real `A, B`, the moments give
   `𝓕u(ξ) = ∫ u (e^{−iηx} − A cosh(x/2) + iB sinh(x/2))`, so by Cauchy–Schwarz
   `F(ξ) ≤ g(0) · ∫_{−a}^{a} [(cos ηx − A cosh(x/2))² + (sin ηx − B sinh(x/2))²] dx = g(0)·a·T_{A,B}(θ)`,
   `T_{A,B}(θ) = ∫_{−1}^{1} [(cos θs − A cosh(as/2))² + (sin θs − B sinh(as/2))²] ds`.
   Band transfer: `|e^{−iθs} − e^{−iθ_c s}| ≤ |θ − θ_c||s|` gives on `|θ − θ_c| ≤ h`:
   `T(θ) ≤ (1+ε) T_{A,B}(θ_c) + (1 + 1/ε) (2/3) h²`.
4. **Integration.** With `w = Σ_j w_j 1{θ ∈ band j}` (bands in `|θ|`), `∫ F w ≤ g(0) (1/π) Σ_j w_j Δθ_j T_j`.
5. **Multiplier.** `K₊(h) ≥ 1/h + r₀` on `(0, log 2]` (`r₀ = 0.44`), so
   `Λ_S(η) ≥ Cin(2θ) + r₀ S (1 − sin(2θ)/(2θ))`, `Cin(x) = ∫_0^x (1 − cos t)/t dt` increasing.
   `A(log 2) = −γ − log π + log(4/3) − J`, `J = 5 log 2 − log 3 − 2 log(1+√2) + arctan(√2/4)`.
6. **Certificate.** `t = 1/4`; bands `Δθ = 1/10` on `[1/2, 23/10]`, one band `[0, 1/2]`, tail `2θ ≥ 27/5`
   (`m ≥ A_lo + Cin(27/5) + r₀S(1 − 5/27) ≥ 1/4`). Estimated `Σ w_j Δθ T_j ≈ 0.25`, `κ₀ ≈ 0.17`.
7. **Transfer.** Complex smooth pole-vanishing sources split into real cores (`ccmRestrictedWeilSourceQuadratic_complexSmooth_eq`);
   near-minimizers are smooth (`exists_polarConstrained_smooth_rayleigh_lt`) ⇒ `μ₀(a) ≥ κ₀`; Theorem D
   (`eventually_ccmRestrictedWeilPolarGroundEnergy_pos`) ⇒ positivity past `√2`.

## Lean plan
- `HTGeometry/SinCosAlternatingTaylorBounds` — `(−1)^n (cos x − C_n(x)) ≥ 0`, `(−1)^n (sin x − S_n(x)) ≥ 0`, `x ≥ 0`, `n ≥ 1`.
- `RHTower/ConstrainedWeilBathtubFloor` — steps 1–4.
- `RHTower/ConstrainedWeilPrimeTwoMultiplierBounds` — step 5 and constants.
- `RHTower/ConstrainedWeilPrimeTwoBathtubCertificate` — step 6–7.

## Log
- 2026-09-26 — created; design by hand estimates (fact log EOC-F17–F19).
- 2026-09-26 — superseded: closed in Lean by a parallel session (`RHTower.PoleVanishingWeilPositivityHalfLogTwo`:
  `one_tenth_le_ccmRestrictedWeilPolarGroundEnergy_halfLogTwo`, `exists_polarGroundEnergy_pos_past_halfLogTwo`).
  Own duplicates removed; kept `HTGeometry.SinCosAlternatingTaylorBounds` (all-order alternating sin/cos bounds, wired).
