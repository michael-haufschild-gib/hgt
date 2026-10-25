# Cross-programme contributions to the eighteen research programmes

- **ID:** cross-programme-250-2026-10-25
- **Stage:** 1-in-progress
- **Type:** RESEARCH PROGRAMME
- **Source:** user `/goal` of 2026-10-25 (eighteen programme READMEs, frontier map).
- **Statement:** 250 significant unconditional Lean contributions: answers to programme open
  questions, missing tools, cross-programme theorems, or frontier arithmetic problems.

## Gates
- [x] 0 → 1  frontier map and READMEs surveyed; counting rule fixed (log: `logs/cross-programme-250-2026-10-25.md`)
- [ ] per contribution: paper proof → Lean (`lake --old env lean`, clean axioms) → umbrella wiring

## Active conjecture

C1 (SSA §7.5): the lag-two floor is exactly `1/4`; every odd shift has floor exactly `1/3`,
attained by the conductor-two twin `(−1)^{v₂(n)}`.
Proof: three signs `f(n), f(n+1), f(n+2)` have at least one agreeing pair, so odd positions pay
`1 − a(n) − a(n+1)`; even positions give `L₁/2`; the two lower bounds sum to `H/2`.

C2 (SSA §7.4): every zero-defect sign has `f(2) = −1` (the `f(2) = 1` branch dies at `n = 25`);
`(−1)^{v₂(n)}` is a zero-defect sign that is not a conductor-three twin.
Open conjecture C2′: the zero-defect signs are exactly `(−1)^{v₂}` and the two conductor-three
twins (verified numerically: only these three patterns on primes `≤ 13` extend to `n ≤ 400`).

C3 (BVI §7.7, THIM §7.3): closed form of the cofinal Möbius slope
`κ = ρ Σ_j S(j) log(1+1/j)`:

    κ = (ρ/2π) ∫_ℝ H(t) / |t ζ(1+it)|² dt,   H(t) = Σ_δ μ(δ) w(δ)² |B_δ(it)|²
      = (ρ/2π) ∫_ℝ |B(it)|² ∏_p (1 − |p+1−p^{−it}|^{−2}) dt / |t ζ(1+it)|²,

`w = μ/σ`, `B_δ(s) = Σ_n b_δ(n) n^{−s}`, `b_δ(n) = n^{−1} ∏_{p|n, p∤δ} (p+1)^{−1}` (absolutely
convergent on `Re s ≥ 0`), `B = B_1`. Numerically `≈ 0.4408` (corpus value `0.4407`).
Paper proof: (1) `S(⌊e^u⌋) = Σ_δ μ(δ)w(δ)² g_δ(u − log δ)²`, `g_δ(v) = T_δ(⌊e^v⌋)` (coprimality
sieve); integrate and translate: `κ = ρ Σ_δ μ(δ)w(δ)² ‖g_δ‖₂²`, absolutely by
`|T_δ(Y)| ≤ Cδ^{1/4}(1+log Y)^{−2}`. (2) `∫ g_δ e^{−sv} = L(c_δ,s)/s` (`Re s > 0`,
`c_δ = 1_{(·,δ)=1} w`); `L(c_δ,s) ζ(1+s) = B_δ(s)`; dominated convergence at `σ ↓ 0` and
`ζ(1+it) ≠ 0` give `ĝ_δ(t) = B_δ(it)/(it ζ(1+it))`; Plancherel. (3) swap `Σ_δ`, `∫`.
(4) `B_δ = B/∏_{p|δ}(1 − p^{−s}/(p+1))`, Euler product in `δ`.

C4 (THIM §7.7): divergent critical-line mass. For `f(p) = (1 − c g(p)) cos(t₀ log p)`,
`g(p) = Σ_k w_k p^{−s_k}`, the half-damped receiver is paid iff `∫_0^1 e^{−cΛ(ρ)} dρ/ρ < ∞` or
`ζ(1/2+it₀) = 0`, `Λ(ρ) = Σ_k w_k log(1/(s_k+ρ))`.
Paper proof: Euler product gives `log|F(w)| = ½(Z(w−it₀)+Z(w+it₀)) − (c/2)Σ w_k(Z(w+s_k−it₀)+Z(w+s_k+it₀)) + O(1)`,
`Z = log|ζ|`; on boxes `Z(v) = −log|v−1| + O(1)`, hence `|F|² ≍ h(ρ) = e^{−cΛ(ρ)}/ρ`. Payment: `h` almost
decreasing, majorant `u⁻¹1_{|τ|<u} + h(|τ|)` uniform in `u`; zero case `|ζ|² ≤ L²ρ²`. Obstruction:
integrand `≥ κh(u+τ) − C'` on the segment, so `∫_u^r h ≤ (4πE + C'r)/κ`. Harmonic defect:
`Λ = log log(1/ρ) + O(1)`, threshold `c = 1`; mass divergent via `Σ_p cos² p^{−1−σ} ≥ ½log(1/σ) − C`.
C6: `1 − c/log log p` has the same threshold (harmonic defect `= 1/y + O(1/y²)`, `Σ_p 1/(p ℓ²) < ∞`).

C5 (THIM §7.7): non-completely-multiplicative patterns at half damping. `f' = g ⋆ f`, `g = f' ⋆ μf`,
`g(p) = 0`, `|g(p^k)| ≤ 2`; inverse `h` with `Σ_k |h(p^k)|p^{−k} ≤ (1−r_p)^{−1}` (truncations
`S_K ≤ 1 + r S_K`). `r_p ≤ 3/p²` (odd `p`); `r_2 = 1` iff all two-adic steps extremal iff tails
`−1` or `(−1)^{k+1}`. Off them `h d^{−1/2}` critical Wiener, `f = h ⋆ f'`: classes coincide. On the
tail `−1` at `t₀ = 2πm/log 2`: series `(1 − 2^{1−w})F_{t₀}`, factor `≤ 2 min(1,|z|)` cancels
`|z|^{−1/2}`: paid; companion paid iff `ζ(1/2+it₀) = 0`.

## Log
- 2026-10-25 — created; C1, C2 paper proofs complete.
- 2026-10-25 — C1 formalized (#1). C2 formalized (not counted). C3 formalized (#2).
- 2026-10-25 — C4 formalized (#3).
- 2026-10-25 — C5 formalized (#4).
- 2026-10-25 — C6 formalized (#5).
