# All-height heated slice positivity for every order above `C/λ`

- **ID:** heated-slice-order-uniform-positivity
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `1-in-progress/wd-la-sign-producer-loop-2026-10-25.md`, row 8
- **Statement:** There is `C > 0` such that `T_{2n}(λ, 0, t) > 0` for every `0 < λ ≤ 1`, every
  height `t` and every `n ≥ C/λ`.

## Gates
- [x] 0 → 1
- [x] 1 → 2
- [x] 2 → 3 `RHTower/XiSliceHeatOrderUniformPositivity`
  (`exists_xiSliceHeatTransfer_pos_order_ge_inv_heat`), standard axioms, wired
- [ ] 3 → 4

## Paper proof
Above `max(t₀, e^{100/λ})` the effective slice Ki–Kim–Lee theorem gives every order. Below it,
`½ log t ≤ max(½ log t₀, 50/λ) ≤ C/λ ≤ n`, so every `c_{2m}(t)` with `m ≥ n` lies in the sharp
window `m ≥ max(K, ½ log t)` and is positive; the heat series `T_{2n} = Σ_k w_k c_{2n+2k}`
(`w_0 = 1`, `w_k ≥ 0`) is then positive. Negative heights by evenness of even orders.

## Position
At heat `λ` the RH content of the heated slice lies in the box `n < C/λ`, `|t| < e^{100/λ}`.

## Log
- 2026-10-25 — proved and formalized.
