# Bulk entries along a growing overlap

- **ID:** BEGO
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper), Lean in progress
- **Source:** AHD README §9 item 2 (after BEOC: bulk entries at every overlap `0 < c < 1`)
- **Statement:** along `c = c_N → ∞`, `c² log² N/N → 0`, for every pair of conductors
  `X_N(e,e') := ⟨W R_e, R_{e'}⟩ − E_e(c)⟨R_e, R_{e'}⟩ = [e = e' = 1] c κ_φ (2 + γ − log 4π) + o(c)`,
  `κ_φ = (∫φ)²/∫φ²`, `E_e` the completed conductor energy. At the critical curve `c^{β+1}/log N → K`:
  `c^β ⟨W r_e, r_{e'}⟩ → J(e) δ_{ee'} + [e = e' = 1] K κ_φ (2 + γ − log 4π)`.

## Goal
The second order of every bulk entry when the atoms overlap. The arithmetic constants of the separated regime
(Stieltjes `D(e,e')`, the center's `Λ(e)/φ(e)`, the cross error) all drop to `o(c)`; the only surviving second-order
datum is the archimedean genus `Σ_ρ 1/(ρ(1−ρ)) = 2 + γ − log 4π` at the pole, which is exactly the contribution of the
zeros below the resolution height (`tendsto_sum_bulkLedger_belowResolution`). Hence the zeros above `N^θ` carry only
the first-order count, and the rescaled conductor Gram at the critical curve is the Jordan form plus a positive
rank-one gluing at the pole.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  paper proof (below), numerically confirmed
- [ ] 2 → 3  Lean

## Numerics (tilted-cubic profile `(u(1−u))³`, `κ = 0.612857`, exact matrix with overlapping atoms)
`X_N(1,1)` at `N = 16000`: `c = 2: 0.0564` (pred `0.0566`), `c = 4: 0.1128` (`0.1132`), `c = 8: 0.2247` (`0.2265`).
`X_N(e,e)`, `e = 2,3,4`: `≈ 0` once `c ≫ e` (`c = 8`: `|X| < 10⁻³`; `X(6,6) = −0.15`). Off-diagonal symmetric parts `≈ 0`.
Check at `c = 0.5`: `X(1,1) = −0.0957` vs BEOC `−0.0953`. Script: scratchpad `overlap/run.py`.

## Paper proof
Notation: `w = c/N`, `s_n = cn/N`, `ℓ = log(j/n)/w`, `F = c_e/√φ(e)`, `F' = c_{e'}/√φ(e')`, `M = ∫φ²`,
`G = φ ⋆ φ` (support `[−1,1]`, `∫G = (∫φ)²`), `ū(h) = mean_n F(n)F'(n+h) = [e=e'] c_e(h)/φ(e)`, `ū₀ = [e=e'=1]`.
RAPT exact decomposition at every overlap: `W = (log N + F(c) − γ + s_N)I − P + Cen_α − Cr^{sep} + Pe + Ov − NR`,
`E_e = E^{ref}_e − S_e` (shell correction). Hence
`X = s_N g − (P-residual) + (Cen − [e=1]αg) − Cr^{sep} + Pe + (Ov − NR + S_e g)`, `g = ⟨R_e, R_{e'}⟩`.

1. **Known blocks.** P-residual `→ D(e,e')` (BSOS), `s_N g → 0`, `Pe → 0`; center `= α·(c-free) → α·Cen(e,e')`, `α = cκ`.
2. **Non-ratio primes are near pairs.** `G(log(kn/j)/w)Λ(k)R_e(n)/√k = Λ(k)c_e(m/k)G(·)/√(φ m)`, `m = kn`; summing
   `k | m`: `(Λ ∗ c_e)(m) = c_e(m) log m − J_e(m)`, `J_e(m) = Σ_{d|(e,m)} μ(e/d) d log d` (periodic, mean `Λ(e)`).
   So `⟨NR R_e, R_{e'}⟩ = Σ_{near (n,j)} [F(n)F'(j) log(nj) − J(n)F'(j) − F(n)J'(j)] G(ℓ)/(M√(nj))` + exterior edge `O(c² log N/N)`.
3. **Near archimedean pairs** (mixed Robin expansion on the window `w(1+|ℓ|)`): for `|ℓ| ≤ 2`,
   `Arch/(wM) = G(ℓ)(log(1/w) + κ₀)/M + R(ℓ)/M + O(w)`, `κ₀ = 2θ'(0) + c_∞ = −log 2π − γ`,
   `R(ℓ) = ∫_0^{1+|ℓ|} (2G(ℓ) − G(y−ℓ) − G(y+ℓ))/(2y) dy − G(ℓ) log(1+|ℓ|)`. `Ov` adds `(α/N)ω(L)`, and
   `ω(log(j/n))/√(nj) = ½(1/|j−n| + 1/(j+n))` exactly.
4. **The logarithms cancel.** In `Ov − NR` the coefficient of `F(n)F'(j)G(ℓ)` is `log(1/w) − log(nj) = −log(N/c) − log(s_n s_j)`.
   `Σ_{near} F F' G/(M√(nj)) = [e=e'] S_e + O(q c log c/N + c²/N)` (periodic averaging; `Σ_n G(h/s_n)/n → ∫_{|h|/c}^1 G/u`),
   so `−log(N/c)·(that) + S_e g = S_e(g − [e=e'] log N) + [e=e'] S_e log c + o(1)`.
5. **Rows.** Periodic Riemann sums: `Σ_{0<|h|≤2s} ū(h)K(h/s) = s ū₀ ∫K + O(q(sup K + Lip K))`, and
   `Σ_n (1/n)·s_n ū₀ c' = c ū₀ c'`. Harmonic add-back: `Σ_{h≤x} ũ(h)/h = ū₀(log x + γ) + C_ū + o(1)`,
   `C_ū = −Λ(e)/φ(e)` on `(e,e)`, `e > 1`, `0` off the diagonal. Jets: mean `b₀ = [e'=1]Λ(e)/√φ(e) + [e=1]Λ(e')/√φ(e')`.
   Cross error (`|ℓ| > 2`): kernel `(1/2M)∫G(t)(1/|ℓ| − 1/(|ℓ|+t))dt + O(w)`, coefficient `χ₂ = (1/M)∫G(t) log((2+t)/2) dt`.
6. **Coefficients of `c`.** center `κ Cen(e,e')/√(φφ')`; shells `κ[e=1](γ[e'=1] − [e'>1]Λ(e')/√φ(e'))` + `[e=e'=1]κ log c`;
   `−2 log s` part `ū₀κ(−2 log c + 2)`; `κ₀` part `ū₀κκ₀`; `R` part `ū₀∫_{−2}^2 R/M`; add-back `κ(ū₀(log 2c − 1 + γ) + C_ū)`;
   jets `κ b₀`; cross `ū₀ χ₂`. Identity: `∫_{−2}^2 R = −∫G(t) log(2+t) dt` (Fubini: `∫_{−T}^T R = −∫G(t) log(T+t)dt`), so
   `∫R/M + χ₂ = −κ log 2`. Summing: `(e,e), e>1`: `κΛ(e)/φ(e) − κΛ(e)/φ(e) = 0`; `(e,1)`: `−κΛ(e)/√φ(e) + κΛ(e)/√φ(e) = 0`;
   `(1,e')`: `−κΛ(e')/√φ(e') + κΛ(e')/√φ(e') = 0`; distinct `e,e' > 1`: `0`;
   `(1,1)`: `κ(1 − log 2) + κγ + κ(2 + κ₀) + κ(log 2 − 1 + γ) − κ log 2 = κ(2 + γ − log 4π)`. All remainders `O(log² c)`.

## Log
- 2026-11-03 — numerics, paper proof; Lean in progress.
