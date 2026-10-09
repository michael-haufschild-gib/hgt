# Littlewood short windows under RH: ≥ m zeros in every (t, t + C/log log t]

- **ID:** littlewood-short-window-zero-count-lean
- **Stage:** 3-formalized (paper proof below; Lean closed, standard axioms)
- **Type:** THEOREM (classical, Littlewood 1924). This is the form consumed by CANNOT-497 and by hgt-0f's route-candidates rows 661–664.
- **Statement (L):** `RiemannHypothesis → ∃ C > 0, ∀ m : ℕ, ∃ t₀, ∀ t ≥ t₀, xiZeroCount(t + C/log log t) − xiZeroCount t ≥ m`. One `C` works for every `m`.

## Proof (paper; uses only Zeta23's unconditional explicit formula)
1. **Tests.**
   - `Φ(u) = ϑ(1 − u²)`, where `ϑ` is the smooth transition. `Φ` is C^∞, even, `0 ≤ Φ ≤ 1`, supported in `[−1, 1]`, with `Φ(0) = 1`.
   - `Φ_ℓ(u) = Φ(u/ℓ)`, so `Φ_ℓ^{(k)}(u) = Φ^{(k)}(u/ℓ)/ℓ^k`.
   - `f_k = Φ_ℓ^{(k)} e^{−iTu}`, supported in `[−ℓ, ℓ]`, with `L = 2ℓ` and `X = e^{2ℓ}`.
   - `f̂_k(z) = (Φ_ℓ^{(k)})^(z − T)`.
2. **RH makes the zero side a sum of squares.** Write `ψ_k = |(Φ_ℓ^{(k)})^|²`. Under RH, `γ_ρ = Im ρ` is real, so `Σ_ρ m_ρ ψ_k(γ_ρ − T) = ∫ ψ_k(τ − T) ν_X(τ) dτ`.
3. **Counting.**
   - `ψ_{k+1}(x) = x² ψ_k(x)`, by integration by parts.
   - `ψ₀ ≤ (ℓA)²`, where `A = ∫Φ`.
   - Hence `ψ₀(x) ≤ (ℓA)² 1_{(−δ,δ]}(x) + ψ₁(x)/δ²`, and so `S₀ ≤ (ℓA)² N(T−δ, T+δ) + S₁/δ²`.
4. **The density.** `|ν_X − μ| ≤ 3X²` for `X ≥ 1`. This uses `|Π_X| ≤ (2/π)(X+2)` and `|P_X| ≤ X²/π`, the latter from `Λ(n) ≤ log n ≤ n`.
5. **Pointwise μ comparisons** (μ even, monotone, `μ > −1`, Stirling with `C ≥ 0`):
   - `ψ₀(x)μ(x+T) ≥ μ(T/2)ψ₀ − (μ(T/2)+1)(4/T²)ψ₁`;
   - `μ(x+T) ≤ μ(3T/2) + (1/2π + C)·4x²/T²`, which gives `ψ₁ μ ≤ μ(3T/2)ψ₁ + c(4/T²)ψ₂`.
   - No integrals over regions are needed: the tails are absorbed by `ψ₁` and `ψ₂`.
6. **Plancherel.** `∫ψ₀ = 2πℓE`, `∫ψ₁ = 2πF₁/ℓ` and `∫ψ₂ = 2πF₂/ℓ³`.
7. **Assembly.**
   - Take `δ = D/ℓ` with `D² = 2F₁/E + 1`, so `F₁/D² ≤ E/2`.
   - This gives `ℓA²N ≥ (E/2)log T − M − 3πE(1 + 3e^{4ℓ})` for `ℓ ≥ 1` and `T ≥ 2`.
8. **Choice of ℓ.** Take `ℓ = (log log t)/8`, so `e^{4ℓ} = √(log t)`, and `T = t + δ`.
   - The right side of step 7 is `≥ (E/4) log t`.
   - Since `ℓ ≤ √(log t)/4`, `A²N ≥ E√(log t) → ∞`.
   - The window is `(t, t + 16D/log log t]`.

## Lean (closed)
- `RHTower/LittlewoodWindowTest.lean` (222 lines):
  - definitions: `bump`, `sc`, `cb`, `window`;
  - lemmas: `iteratedDeriv_scaled`, `paperFT_cb_succ`, `norm_paperFT_cb_le(_div)`, `integral_norm_sq_paperFT_cb`, `paperFT_window`.
- `RHTower/LittlewoodShortWindowZeroCount.lean` (847 lines), namespace `RHTower.Littlewood`:
  - zero side and counting: `explicitFormula_window`, `tsum_psi_zero_le`, `tsum_window_mult`, `integrable_psi`, `integral_psi_*`;
  - density and μ: `abs_nuX_sub_mu_le`, `psi_zero_mul_mu_ge`, `mu_add_le`, `mu_half_sub_ge`;
  - integrated bounds: `integral_psi_zero_nuX_ge`, `integral_psi_one_nuX_le`;
  - assembly: `exists_window_count_bound`, `xiZeroCount_sub_eq`;
  - headline: **`riemannHypothesis_eventually_xiZeroCount_window_ge`** (uniform `C`) and **`riemannHypothesis_xiZeroCount_window_ge`** (the requested per-`m` form).
- Axioms: `propext`, `Classical.choice`, `Quot.sound`. Wired into `RHTower.lean`; built with `lake --old build`.
- **Import note.** `HorizontalSimplicityTradeoffDensity` and `ZetaSymbolArchimedeanHorizon` cannot be imported together: `RHTower.integrable_mul_cexp` is declared in both `IsolatedDeepZeroHodgeIndex` and `WindowTransformSamplingParseval`. This pre-existing collision also breaks a full `RHTower` umbrella build. The ξ bridge goes through `Zeta23SimpleCriticalDensity` instead.

## Log
- 2026-10-09: created; requested by hgt-0f for CANNOT-497. Zeta23's explicit formula makes (L) reachable without `S(t)` theory.
- 2026-10-09: closed in Lean, with uniform `C` for all `m`. Novelty: none (classical); value: the first unconditional-Lean RH ⇒ short-window statement in the corpus.
