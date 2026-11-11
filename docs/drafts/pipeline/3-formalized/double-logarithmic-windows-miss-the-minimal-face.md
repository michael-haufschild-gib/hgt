# Double-logarithmic windows miss the minimal face

- **ID:** A89 (survivor)
- **Stage:** 3-formalized
- **Lean:** `SurfaceOfSpecZ/ScaleLocality/DoubleLogarithmicWindowsMissTheMinimalFace.lean`

## Statement

For `γ_min > 0`, `C > 0`, `0 < Θ ≤ 1/2` there is one `Z ∈ 𝒵(γ_min, C)` of simple zeros with
`Re ρ < 1/2 + Θ` and `sup Re ρ = 1/2 + Θ` such that for **every** `R : ℝ → ℝ` with
`R(T) ≤ (C/256) log log T` for large `T`, and all `K, U`, some `T ≥ U` has
`2 Re S_Z(u) ≥ K` on `|u − T| ≤ R(T)`.

Corollary: no radius with `R → ∞` and `R(T) ≤ (C/256) log log T` decides `𝒵`.

Declarations: `exists_classZ_doubleLog_windows_bddBelow_beyond_every_bound`,
`not_forall_doubleLog_radius_decides_classZ`, `log_log_dlT_le`, `RadiusTower`.

## Proof

1. **Free radii.** `RadiusTower` collects the constraints on `(T_k, Γ_k, ρ_k)` under which the
   phase-split binomial level `k` (harmonic step `1/(4(ρ_k+1))`, degree `m₀ = 4(ρ_k+1)Γ_k`) is
   `≥ 2r₀/64^{m₀}` on `|u − T_k| ≤ ρ_k + 1`, dominates levels `< k` there, and keeps the
   configuration tempered with `N(t, t+1) ≤ 32ρ_k + 40 ≤ C log t`. Every such tower gives
   `2 Re S_Z ≥ k + 1` on the window of level `k + 1`.
2. **Explicit tower.** `ρ_{k+1} ≥ C(k+2), C², CΘU_k/224, (C/64) log(2Γ_k + ⌈γ_min⌉ + ⌈16/Θ⌉ + 14)`
   with `U_k = T_k + ρ_k + 1`, and `Γ_k = ⌈exp(64(ρ_k+1)/C)⌉`. Then `exp(64y/C)` dominates the
   weight constraint `8192y·2^k·exp(ΘU_{k−1}/7)` (split `64 = 16 + 16 + 32`; `exp(16y/C) ≥ 128y`
   from `exp z ≥ z²/2` and `y ≥ C²`), the count `exp((32ρ+40)/C)` and the separation.
3. **Centres.** Each term of `T_k` is `≤ exp(Γ_k²)`: the phase precision
   `(m₀+1)·80(y+8)·64^{m₀}(4Γ/x)^8 ≤ exp(28yΓ + 80y + 640 + 16Γ)`, the dominance threshold
   `≤ Γ⁴/65536`, and `U_{k−1} ≤ 7Γ_k²/16`. Hence `log log T_k ≤ 2 log Γ_k ≤ 2 + 128(ρ_k+1)/C`,
   i.e. `(C/256) log log T_k ≤ ρ_k + 1`.

Axioms of the headline theorems: `propext`, `Classical.choice`, `Quot.sound`.

## Scope

Radii between `log log T` and `o(log T)` stay open (A89 card): a level near height `Γ` needs
`Γ ≳ e^{cR/C}` (harmonic density) and phase precision `log T ≳ ΓR`.
