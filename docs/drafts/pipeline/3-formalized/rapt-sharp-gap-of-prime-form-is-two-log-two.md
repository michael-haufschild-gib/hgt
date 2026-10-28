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

## Progress

- **Steps 1–3 formalized** (`RAPT/TheValuationChainOfFinitelyManyPrimesHasGapTwoLogTwo.lean`, axiom-clean,
  olean built, not yet wired): `smoothBox`, `mem_smoothBox`, `sum_smoothBox_succ`, `boxVar_le_boxGlauber`
  (Efron–Stein), `two_mul_sum_mul_wVar`, `boxLadderVar_le` (sharp ladder), `boxGap_le_ladder`,
  `boxGap_mul_boxVar_le`, `smoothSet`, `smoothVar`, `smoothEnergy`, `sum_smoothSet_eq_ladders`,
  `log_eq_sum_factorization`, `sum_log_mul_sq_le_smoothEnergy` (halo), `zeroExt`,
  `smoothVar_le_boxVar`, `boxEnergy_zeroExt_le`, `inv_pow_le_sqrt`, `sum_boundary_weight_le`,
  `smoothBoundary_le`, `smoothVar_mul_le`, **`eventually_smoothVar_le_smoothEnergy`**:
  `(2 log 2 − ε) Var ≤ E` on `Q`-smooth numbers of `[1, X]`, `X ≥ X₀(Q, ε)`.
- **Step 4–6 (Module B) design, conditioning on the `S`-part `a`:**
  (B1) `Var(y) = Σ_a (1/a) harmonicVar Q₀ (N/a) (y(a·)) + Var_ν(h)`, `h(a)` = fibre mean,
  `ν(a) = F(N/a)/a`, `F` = rough harmonic mass. (B2) within fibres: crude tensorization
  (`exists_harmonicVar_le_glauberForm`, needs the general-`Q` export) and ladder base edges give
  `Σ_a (1/a) harmonicVar ≤ (K/log Q₀) D_L`. (B3) Jensen on small-prime edges; commutation error =
  rough shells `(F(N/a) − F(N/(ap^k)))/F(N/a) ≤ k C_sh log Q₀/(c log(N/a))` (thin shells + rough mass
  lower bound), finite sum over `p < Q₀`; large `a` by the halo on `[1, N]` (`sum_smoothSet_eq_ladders`
  with `Q = N + 1`). (B4) `Var_ν(h)`: restrict to `a ≤ N^δ`, compare with Module A at `X = N^δ`;
  weights `F(N)/F(N^{1−δ}) ≤ (1 + O(δ))(1 + o(1))` from `F(Y) ≥ M log(Y+1)` and the upper bound via
  `H(Y) ≥ F(Y^{1−δ′}) F_S(Y^{δ′})`, `F_S → Z_S = 1/M`. (B5) top control (#6) and assembly.

## Log
- 2026-10-28 — created; plan above. Module A (steps 1–3) formalized.
