# Heat detection from the local zero configuration

- **ID:** heat-detect-local-config
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `1-in-progress/reboot-programme-conjecture-loop-2026-10-30.md` #5; `reboot-final.md` WP-A3
- **Statement:** With `u_q = z_q − t` and `Ψ_{t,r}(ρ) = Σ_q log⁺((|u_q|² + ρ²)/|u_q² + r²|)`: for
  `t ≥ e^{16}`, `L = log t`, `Ξ(t) ≠ 0`, an off-line zero `½ + δ + it` with `δL ≥ 1`, and
  `δ/8 ≤ r ≤ δ/4` with `f_t(r) ≠ 0`, if `Ψ_{t,r}(ρ) ≤ cLρ + bδL` on `[0, 3/2]` (`c ≥ 2`, `b ≥ 0`) then
  some `T_n(κ/L, 0, t)` is negative for every `0 < κ ≤ δ/(3000(b + c + 1))`.

## Lean
Module `RHTower/Heat/HeatDetectionFromTheLocalZeroConfiguration.lean` (namespace `RHTower`):
- `zeroGrowthSum`, `summable_zeroGrowthTerm`, `zeroGrowthSum_mono`;
- `xiSliceReal_le_mul_exp_zeroGrowthSum` — growth law `f_t(y) ≤ f_t(r) e^{Ψ_{t,r}(y)}`;
- `xiSliceReal_le_shifted`, `xiSliceReal_le_envelope_of_zeroGrowth`, `heatedSliceReal_le_of_zeroGrowth`;
- `coeff_mul_pow_le_of_growth`, `xiSliceReal_le_heatedSliceReal_add` — reverse Hermite bound;
- `re_xiSliceHeatTransfer_neg_of_zeroGrowth` — the detection law (general `α, B, λ`);
- `re_xiSliceHeatTransfer_neg_of_zeroGrowth_linear` — the statement above.
Axioms: `propext`, `Classical.choice`, `Quot.sound`.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven
- [x] 2 → 3  formalized

## Paper proof
1. **Growth law.** `f_t(y)/f_t(0) = Π_q (1 + y²/u_q²)` (finite-product limit). The ratio of the
   factors at `y` and `r` is `|u² + y²|/|u² + r²| ≤ exp log⁺((|u|² + y²)/|u² + r²|)`; the terms are
   `≤ 2(ρ² + r²)/|u|²` once `|u|² ≥ 2r²`, so summable. Hence `f_t(y) ≤ f_t(r) e^{Ψ_{t,r}(y)}`.
2. **Envelope.** For `|y| ≤ 3/2` use 1 with `Ψ ≤ α|y| + B`. For `|y| ≥ 3/2`, Stirling growth from
   `3/2` gives `f_t(y) ≤ f_t(3/2) e^{A(|y| − 3/2) + (|y| − 3/2)²}`, `A = log t + K₀ ≤ α`, and
   `f_t(3/2) ≤ f_t(r)e^{3α/2 + B}`. So `f_t(y) ≤ f_t(r) e^{B + α|y| + y²}` for all `y`.
3. **Gaussian.** `H(R) ≤ √2 f_t(r) e^{B + 2α²λ} e^{αR + 2R²}` (`integral_gauss_mul_expEnvelope_le`).
4. **Reverse Hermite.** `f_t(r) = Σ p_n(r) a_n`, `|p_n(r)| ≤ (r + 2√(λn))ⁿ`. For `n ≤ n₁ = ⌊r²/(4λ)⌋`
   this is `≤ (2r)ⁿ`, so that part is `≤ H(2r)`; the rest is `≤ 3√2 f_t(r) e^{B + 2α²λ + c₁}(2/3)^{n₁+1}`,
   `c₁ = 2αr + 16r² + 32α²λ`, which the tail condition makes `≤ f_t(r)/2`. So `f_t(r) ≤ 2H(δ/2)`.
5. **Relative growth.** `H(R) ≤ 2√2 e^{B + 2α²λ} H(δ/2) e^{αR + 2R²}`; the main condition is the
   hypothesis of `re_xiSliceHeatTransfer_neg_of_relative_growth`.
6. **Numerics** at `α = cL`, `B = bδL`, `λ = κ/L`, `κ ≤ δ/(3000(b + c + 1))`: both left sides are
   `≤ 3P + bP + 2.02cP + P/2` with `P = δL ≥ 1`, the right sides `≥ 3.9(b + c + 1)P` and
   `≥ 250(b + c + 1)P` (`zeroGrowthLinear_numerics`).

## What it changes
This is WP-A3 as an unconditional local law: heat detection at height `t` is governed by the
zero-growth functional `Ψ_{t,r}`, a sum over the actual zeros. A slope `O(log t)` and an offset
`O(δ log t)` give the linear rate `κ ≍ δ`; the offset collects the zeros within `O(δ)` of `½ + it`,
so `B = O(δ log t)` is exactly the local count at scale `δ` (WP-A1). With the cards
`heat-detection-rate-is-quadratic-in-the-depth.md` (unconditional `δ²`),
`a-central-cluster-hides-an-off-line-zero-from-heat.md` (`δ²` sharp for clusters) and
`heat-repair-from-local-depth-and-count.md` (repair at `128δ²/N(t, √2δ)`), the heat threshold at a
height is determined, up to constants, by depth² over the local zero degree.

## Log
- 2026-10-31 — created; proved; formalized.
