# Spectral weight of a zero-density twin at precision c_N²

- **ID:** rit-zero-density-spectral-weight
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper), formalization in progress
- **Programme:** RenormalizedIntersectionTheory, open topic 3 (ACP open question 2 for `κ < 1/4`)
- **Statement:** Let `P` have relative log density `κ ∈ (0, 1/4)`:
  `|Σ_{p∈P, p≤n} log p/p − κ log n| ≤ C`. Let `e_0` be the ground eigenvector of the prime matrix,
  `Q_N(w) = (log N − γ)|w|² − P_N(w)`, `ω̂ = (ω_P(n) n^{−1/2})/√H_N`, `c_N = Σ_{n≤N} ω_P(n)/n / H_N`.
  For `0 < s < 2 log 2` and every `ε > 0`, eventually, for all `w ⊥ e_0`:
  `⟨w, ω̂⟩² ≤ c_N² (W_P(s) + ε) (Q_N(w) − s|w|²)`, `W_P(s) = Σ_{m≥2} w_P(m)/(E_m − γ − s)`.
  Consequently the twin has margin `2 log 2` iff `W_P(s) ≤ 1/s` on `(0, 2 log 2)`.

## Goal
Upper half of `c_N^{−2} Σ_{i≠0} ⟨ω̂, e_i⟩²/(λ_i − s) → W_P(s)`: above bounded energies the excited
spectral mass of the twisted horizon vector is exactly the conductor series, at precision `c_N²`.
With the packet criterion (`hodgeSeparates_primeSetFlip_of_packet`) this classifies the margins of all
prime-set twins of log density `κ < 1/4`.

## Proof

Notation: `π(n) = 1/n` on `[1, N]`; vectors `u ∈ ℝ^N` with `y_n = √n u_n`; `H = H_N`;
`ω⃗_n = ω(n)/√n`; `V_Q = {u : √n u_n depends only on the Q-smooth part of n}`, `P_Q` its orthogonal
projection; `S_Q(Y) = Σ_{r≤Y, Q-rough} ω(r)/r`, `R_Q(Y) = Σ_{r≤Y, Q-rough} 1/r`; `β = 1 − 2κ ∈ (1/2, 1)`.

**Step 1 (rough Wirsing, uniform in Q).** `f = ω·1_{Q-rough}` is completely multiplicative, `|f| ≤ 1`.
Chebyshev: `S(Y) log Y − M(Y) = Σ_{d≤Y} Λ(d) f(d)/d S(Y/d)`, `M(Y) = Σ_{n<Y} S(n) log(1 + 1/n)`.
The prime mean `A(k) = Σ_{Q≤p≤k} ω(p) log p/p` is `B(k) + O(1)` with `B(k) = β(log k − log(Q−1))` for
`k ≥ Q`, `0` below. Abel summation (total variation of `k ↦ S(Y/k)` at most `R_Q(Y)`) gives
`|S(Y) log Y − M(Y) − β Σ_{Q≤k≤Y} log(k/(k−1)) S(Y/k)| ≤ C₂ R_Q(Y)`.
With the running maximum `Ŝ` and `Î(Y) = Σ_{n<Y} Ŝ(n) log(1+1/n)`: the block sum
`Σ_{Q≤k≤Y} log(k/(k−1)) Φ(⌊Y/k⌋) ≤ Σ_{n≤Y/(Q−1)} Φ(n) log(1+1/n)` for nondecreasing `Φ` (Abel in
`ΔΦ ≥ 0`), so for `Q ≥ 3`: `Ŝ(Y) log Y ≤ (1 + β) Î(Y) + C₂ R_Q(Y)`.
Integrating factor `g = Î/(log Y)^{1+β}` (Bernoulli): `g(Y+1) ≤ g(Y) + C₂ R_Q(Y) δ_Y/(log Y)^{2+β}`.
With `R_Q(Y) ≤ C₃(1 + log Y/log Q)` and `g(Q) = (log Q)^{−β}`:
`|S_Q(Y)| ≤ A (log Y/log Q)^β + B` for all `Y`, `Q ≥ 3`, with `A, B` depending only on `κ, C`.

**Step 2 (positive Wirsing constant).** `S_N = c (log N)^β + O(1)` (Wirsing asymptotic). If `c ≤ 0`,
`S_N ≤ G`; Abel gives `Σ_{n≤N} ω(n) n^{−1−σ} ≤ G` for all `N, σ > 0`. Euler: the series is
`lim_X Π_{p<X} (1 − ω(p) p^{−1−σ})^{−1} ≥ exp Σ_{p<X} ω(p) p^{−1−σ}` (`(1 ∓ x)^{−1} ≥ e^{±x}`), and Abel with
`t^{−σ}/log t` makes `Σ_p ω(p) p^{−1−σ} ≥ β e^{−1} log(1/σ) − O(1) → ∞`. So `c > 0`,
`c_N ≥ c'(log N)^{−2κ}`.

**Step 3 (fixed scale T).** Peeling one prime: `S_p(X) − (ω(p)/p) S_p(X/p) = S_{p+1}(X)`, and
`|(log X)^β − (log X/p)^β| ≤ (log p)^β`; induction over `p < T` gives
`S_T(Y) = c Π_{p<T}(1 − ω(p)/p) (log Y)^β + O_T(1)`, `R_T(Y) = Π_{p<T}(1 − 1/p) log Y + O_T(1)`, so
`m_T(Y) = S_T/R_T = (c/δ_F)(log Y)^{−2κ} + O_T(1/log Y)`, `F = P ∩ [1, T)`, `δ_F = Π_{p∈F}(p−1)/(p+1)`.
With `μ = c_N/δ_F`: for `a ≤ N^ε`, `|m_T(N/a) − μ| ≤ (K ε + o(1)) c_N`; Rankin bounds the `T`-smooth
mass beyond `N^ε` by `N^{−ε/2} Π_{p<T}(1 − p^{−1/2})^{−1}`. Since `ω⃗_F ∈ V_T` and
`⟨ω⃗ − μω⃗_F, φ⃗⟩ = Σ_a φ(a) ω(a)(S_T − μR_T)(N/a)/a`, Cauchy–Schwarz gives
`|P_T(ω⃗ − μω⃗_F)|² ≤ Σ_a R_T(N/a)/a · (m_T(N/a) − μ)² = o(c_N² H)`.

**Step 4 (multiscale).** `Q_j = T^{2^j}`, `j ≤ J` with `Q_J ≥ √N`. For nested projections
`|⟨w, (1 − P_{Q_0})ω⃗⟩| ≤ Σ_j |P_{Q_j} ω⃗| |(1 − P_{Q_{j−1}})w| + |ω⃗| |(1 − P_{Q_J})w|`.
Rough Poincaré (`sum_fibreVar_le`): `|(1 − P_Q)w|² ≤ (K/log Q) D_N(w)`. Step 1 with
`R_Q ≥ c log Y/log Q` and `Σ_{a Q-smooth} 1/a ≤ C log Q`:
`|P_Q ω⃗|² ≤ Σ_a S_Q(N/a)²/(a R_Q(N/a)) ≤ K' (log N)^{1−4κ} (log Q)^{4κ}`.
Geometric in `j` since `2κ < 1/2`: `|⟨w, (1 − P_T)ω̂⟩| ≤ (C(log T)^{2κ−1/2} + O((log N)^{2κ−1/2})) c_N √D_N(w)`.

**Step 5 (finite flip, exact).** ACP: the finite-flip resolvent tends to `δ_F²(−1/s + W_F(s))`, the
ground coordinate to `δ_F²`, the ground energy to `0`, every other eigenvalue eventually `> s`. So
`ρ_N = Σ_{i≠0} ⟨v_F, e_i⟩²/(λ_i − s) → δ_F² W_F(s)` and `⟨w, v_F⟩² ≤ ρ_N (Q_N(w) − s|w|²)` for `w ⊥ e_0`.

**Step 6 (assembly).** `⟨w, ω⃗⟩ = μ⟨w, ω⃗_F⟩ + ⟨w, P_T(ω⃗ − μω⃗_F)⟩ + ⟨w, (1 − P_T) ω⃗⟩`. For `w ⊥ e_0`:
`|w|² ≤ G/(t − s)`, `(1 − ε) D_N(w) ≤ Q_N(w) + ε|w|²`, `G = Q_N(w) − s|w|²`; `W_F ≤ W_P`. Hence
`⟨w, ω̂⟩² ≤ c_N² (√W_P + C(log T)^{2κ−1/2} + o(1))² G`; let `T → ∞`.
Gap: `u ⊥ ω⃗`, `u = a e_0 + w`: `Q − s|u|² = a²(λ_0 − s) + G(w)`, `a = −⟨w, ω̂⟩/⟨e_0, ω̂⟩`;
`⟨e_0, ω̂⟩ = c_N(1 + o(1))/⟨e_0, b̂⟩` (the main estimate applied to `b̂ − ⟨b̂,e_0⟩e_0`, whose `G → 0`
because `Q_N(b̂) → 0`). With `W_P(s) < 1/s` (strict by monotonicity), `Q − s|u|² ≥ 0`.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  paper proof above (dependency-closed on corpus inputs listed below)
- [ ] 2 → 3  formalized

## Corpus inputs
RAPT: `sum_Icc_eq_smooth_rough`, `sum_fibreVar_le`, `exists_harmonicVar_le_glauberForm_rough`,
`walkEnergy_small_add_large`, `eventually_atomicWeilForm_add_poleDefect_le`,
`mertensPrimeProduct_mul_log_le_roughHarmonic`, `exists_mertensPrimeProduct_mul_log_ge`,
`exists_roughHarmonic_shell_le`, `sum_roughInterval_eq_levels`, `tendsto_mertensSum_sub_log`.
ACP: `tendsto_finiteFlipFiniteResolvent`, `exists_finiteFlip_conductor_eigenline`,
`eventually_fullPrime_ground_count_one`. RIT: Wirsing module. Mathlib: smooth-number Euler products.

## Lean plan (RenormalizedIntersectionTheory)
1. `TheRoughWirsingBoundIsUniform` (Step 1)
2. `TheWirsingConstantOfAFlipTwinIsPositive` (Step 2)
3. `TheRoughMeanAtAFixedScale` (Step 3)
4. `TheMultiscaleProjectionBound` (Step 4)
5. `TheExcitedResolventOfAFiniteFlip` (Step 5)
6. `TheZeroDensityTwinCarriesTheConductorSeries` (Step 6, gap theorem, classification)

## Log
- 2026-11-01 — created; paper proof complete; formalization started
