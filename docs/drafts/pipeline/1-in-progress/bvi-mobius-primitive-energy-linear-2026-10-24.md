# The Möbius primitive energy grows linearly

- **ID:** BVI-MOBIUS-PRIMITIVE-LINEAR-2026-10-24
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper) → Lean
- **Source:** THIM README §3.8 ("for the Möbius row the top octave forces linear growth, capped at
  `N log N`"); corpus bounds `⌊N/2⌋ ≤ 3456 E_prim(N; μ)` and `12 E_prim(N; μ) ≤ 64 N (1 + log N)`.
- **Statement:** `12 E_prim(N; μ)/N → c = Σ_{j ≥ 1} T(j)/(j(j+1))`, with
  `T(j) = Σ_{a,b ≤ j} μ(a)μ(b) δ([a,b])/(ab)` and
  `δ(m) = Σ_{(d,m)=1} μ(d) D(dm)/d³ = ρ ∏_{p∣m} p/(p+1) ∏_{p∤m} (1 − 1/((p+1)p²))`, the mean of
  `μ(q)² (J₂(q)/q²) [(q,m)=1]`. The period discrepancy of the Möbius row is diffusive with an exact
  constant; the logarithm of the corpus cap is absent.

## Paper proof
1. Jordan spectrum: `12 E = Σ_{2 ≤ q ≤ N} J₂(q) Y(q)²`, `Y(q) = μ(q) m_q(N/q)/q`, so
   `12 E = Σ_q μ(q)² j(q) m_q(⌊N/q⌋)²` with `j(q) = J₂(q)/q² = Σ_{d∣q} μ(d)/d²`.
2. Fibres `⌊N/q⌋ = j`: `m_q(j)² = Σ_{a,b ≤ j} μ(a)μ(b)/(ab) [([a,b],q)=1]`, so the fibre is
   `Σ_{a,b} μ(a)μ(b)/(ab) U_{[a,b]}(N,j)` with `U_m(N,j) = Σ_{q ∈ fibre, (q,m)=1} μ(q)² j(q)`.
3. `j(q) = Σ_{d∣q} μ(d)/d²` and `q = dq'` turn `U_m` into coprime squarefree counts of `q'` on the
   fibre of `⌊N/d⌋`: `U_m(N,j) = δ(m) N/(j(j+1)) + O(τ(m) √N log N)`.
4. Head `j ≤ J = ⌊N^{1/16}⌋`: error `≪ J³ √N log N`. Tail `⌊N/q⌋ > J`: `|m_q| ≤ q/φ(q)` and
   `Σ_{q ≤ x} (q/φ(q))³ ≪ x` give `≪ N/J`. `|T(j)| ≪ log² j`, so `c` converges.

Numerics (exploratory): `12E/N = 0.32973, 0.33138, 0.33111, 0.33112, 0.33112` for
`N = 10³ … 10⁶`; the formula gives `c ≈ 0.331122`.

## Gates
- [x] 0 → 1  well-posed, attack
- [ ] 1 → 2  paper proof closed
- [ ] 2 → 3  Lean, audit

## Log
- 2026-10-24 — created in 1-in-progress
