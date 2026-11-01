# Excited resolvent of a zero-density twin: the asymptotic `ρ_N ~ c_N² W_P(s)`

- **ID:** rit-zero-density-resolvent-asymptotic
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper)
- **Programme:** RenormalizedIntersectionTheory, open topic 3
- **Statement:** Let `P` have relative log density `κ ∈ (0, 1/4)` (`O(1)` error), `0 < s < t < 2 log 2`,
  `ρ_N = Σ_{i≠i₀} ⟨v_P, e_i⟩²/(E_i − γ − s)` the excited resolvent off the ground `e_{i₀}` (every other
  energy `≥ γ + t`). Then `W_P(s) = Σ_{m≥2} w_P(m)/(E_m − γ − s) < ∞` and `ρ_N/c_N² → W_P(s)`.

## Goal
Lower half of the spectral-weight asymptotic (the upper half is
`eventually_inner_sq_le_conductorSeries`): the conductor series is exactly the excited spectral
weight of the twisted horizon vector at precision `c_N²`.

## Proof

Notation: `F = P ∩ [1, T)`, `δ = δ_F`, `v_F` the finite-flip horizon vector, `G(w) = Q_N(w) − s|w|²`,
`ρ_F = ρ_{i₀}(v_F)`.

**Step A (decomposition with remainder).** For `θ > 0` and `T₀` there is `T ≥ T₀` such that eventually,
for every ground `i₀` and `w ⊥ e_{i₀}`: `|⟨w, v_P⟩ − (c_N/δ)⟨w, v_F⟩| ≤ θ c_N √G(w)`. This is the
fixed-scale term and the rough term of the main estimate: choose `T` with
`K₁(log T)^{2κ−1/2}√C_D ≤ θ c'/4`, then the fixed-scale defect `≤ (θ/4)²(t − s)` and `N` large.

**Step B (finite flip, two-sided).** `ρ_F → δ² W_F(s)`, `W_F(s) = Λ_F(s) + 1/s`: the full resolvent
tends to `δ²Λ_F(s)` and the ground term to `−δ²/s` (`tendsto_finiteFlipFiniteResolvent`, the ground
eigenline).

**Step C (test vector).** `w* = Σ_{i≠i₀} ⟨v_F, e_i⟩/(E_i − γ − s) e_i` has `w* ⊥ e_{i₀}`,
`⟨w*, v_F⟩ = ρ_F`, `G(w*) = ρ_F`. Step A: `⟨w*, v_P⟩ ≥ (c_N/δ)ρ_F − θ c_N √ρ_F`. Cauchy–Schwarz off the
ground: `⟨w*, v_P⟩² ≤ ρ_N G(w*) = ρ_N ρ_F`. If `√ρ_F ≥ θδ`: `ρ_N ≥ c_N²(√ρ_F/δ − θ)²`.

**Step D (packets).** For `T > max S`, `w_F(m) = w_P(m)` on `S`, so `W_F(s) ≥ A_S := Σ_{m∈S} w_P(m)/(E_m − γ − s)`.
Given `ε`, take `η, θ` with `(√(A_S − η) − θ)² ≥ A_S − ε`; then eventually `ρ_N ≥ c_N²(A_S − ε)`.

**Step E (upper bound in resolvent form).** `w = Σ_{i≠i₀} ⟨v_P, e_i⟩/(E_i − γ − s) e_i`:
`⟨w, v_P⟩ = G(w) = ρ_N`, so the main estimate gives `ρ_N² ≤ c_N²(W + ε)ρ_N`.

**Step F (convergence for `κ < 1/4`).** `w_P(m) = 4^{ω(m)}/φ(m)` on `P`-supported `m`, `0` otherwise;
`f_σ(m) = w_P(m) e^{−σ(E_m − γ)}` is multiplicative (`E − γ = log m + Σ_{p|m} log p/(p−1)` is additive).
Euler product over the `P`-primes below `max S`: `Σ_{m∈S} f_σ(m) ≤ ∏_{p∈F}(1 + 4p^{1−σ}/(p−1)²)
≤ exp(4 Σ_{p∈P, p≤X} p^{−1−σ} + 16)`. Abel with `g(n) = n^{−σ}/log n` decreasing and
`A(n) ≤ κ log n + C`, `Δlog n/log n ≤ Δ log log n`, `(b − a)e^{−σb} ≤ (e^{−σa} − e^{−σb})/σ`:
`Σ_{p∈P, p≤X} p^{−1−σ} ≤ κ log(1/σ) + C'` for `σ ≤ 1`. So `Σ_{m∈S} f_σ(m) ≤ C'' σ^{−4κ}`. Dyadic Laplace
upper bound: for `x ≥ x₀ > 0`, `1/x ≤ 2e Σ_{j≥0} σ_j e^{−σ_j x}`, `σ_j = 2^{−j}/x₀`; with
`x = E_m − γ − s ≥ 2 log 2 − s`, `Σ_{m∈S} w_P(m)/x_m ≤ 2e C'' Σ_j σ_j^{1−4κ} e^{σ_j s} < ∞` uniformly in `S`.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  paper proof above
- [ ] 2 → 3  formalized

## Log
- 2026-11-01 — created
