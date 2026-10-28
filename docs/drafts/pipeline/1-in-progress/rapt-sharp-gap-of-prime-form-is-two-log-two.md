# The gap of the prime form below its pole is 2 log 2

- **ID:** rapt-sharp-gap-of-prime-form-is-two-log-two
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper)
- **Source:** RP29 (non-sharp gap); `0-backlog/rapt-top-spectrum-of-prime-form-is-log-integers.md`.
- **Statement:** For every `ε > 0`, eventually in `N`: `P_N ≤ (log N − γ − 2 log 2 + ε)|x|²` on
  `x ⊥ n^{−1/2}`, and some `x ⊥ n^{−1/2}` has `P_N(x) ≥ (log N − γ − 2 log 2 − ε)|x|²`.
  Equivalently `λ₂(P_N) = log N − γ − 2 log 2 + o(1)`; the first excited state is the 2-adic
  valuation step.

## Gates
- [x] 0 → 1  in-progress
- [ ] 1 → 2  fully-proven
- [ ] 2 → 3  formalized

## Approach (two scales)

Pole gauge `y = √n x`, harmonic measure `1/n` on `[1, N]`, defect `D = Σ Λ(t)/(mt)(y_{mt} − y_m)²`.
Target: `D ≥ (2 log 2 − ε) Var` (then RP29's assembly). Fix `Q₀` large, `S` = primes `< Q₀`;
`n = a b`, `a` the `S`-part, `b` the `Q₀`-rough part; `D = D_S + D_L` (small / large prime edges).

1. **Sharp 1D ladder.** On a `p`-ladder of length `J + 1` the pairwise bound gives gap
   `log p · W(J)`, `W(J) = Σ_{j ≤ J} p^{−j}`; numerically this is the exact gap (1.0397, 1.213,
   1.2997, … for `p = 2`), `→ p log p/(p − 1)`.
2. **Finite products.** On a box `Π_{p ∈ S} {0..J_p}` with product weights `1/a`, Efron–Stein (exact for
   product measures, by induction over coordinates with commuting conditional expectations) and step
   1 give `D_box ≥ min_p log p W(J_p) · Var`.
3. **Truncated S-chain (large horizon).** For `h` on `S`-smooth `a ≤ X`: zero-extend `h − c` to a
   box containing `[1, X]`. The extension costs only edges leaving `{a ≤ X}`, weight
   `Σ_{ap^k > X} log p/p^k`: tiny for `a ≤ √X`, `≤ Σ_{p∈S} log p/(p−1)` on the halo; the halo mass is
   `≤ (2D + 2M_S Var)/(½ log X)` (down-edges carry `log a`). Hence gap `≥ 2 log 2 − ε` for `X ≥ X₀`.
4. **Within fibres.** For fixed `b`, the fibre `{a ≤ N/b}` is the truncated S-chain at horizon
   `N/b`: `Σ_b Var_fibre ≤ D_S/(2 log 2 − ε)` for `b ≤ N/X₀`; fibres with `b > N/X₀` lie at the top,
   paid by top control.
5. **Across fibres.** `h_b = E[y | b]` on rough `b ≤ N/Y₁` with weights `F_S(N/b)/b`,
   `F_S(Y) = Σ_{a ≤ Y} 1/a ↑ Z_S` (saturated within `1 − η`): crude tensorization of rough intervals
   gives `Var(h_b) ≤ (C/log Q₀) D_L`. The Jensen commutation error of a jump `q^k` is the `S`-smooth
   mass beyond `N/(bq^k)`, `≤ C_σ (bq^k/N)^σ` (Rankin, finite `S`), summing to `O(Y₁^{−σ}/σ)`.
6. **Assembly.** `D ≥ min(2 log 2 − ε, log Q₀/C) Var − o(D + Var)`; choose `Q₀` with
   `log Q₀/C ≥ 2 log 2`.

Lower bound: the valuation step `1_{2|n} − 1_{2∤n}` (times `n^{−1/2}`), projected off the pole.

## Log
- 2026-10-28 — created; plan above. Not yet formalized.
