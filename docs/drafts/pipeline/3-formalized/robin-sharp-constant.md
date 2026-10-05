# Robin's sharp constant from the Weil-lag ceiling

- **ID:** robin-sharp-constant
- **Stage:** 3-formalized (2026-10-05)
- **Type:** THEOREM target (Lean), under RH
- **Source:** RH goal loop cycle 252
- **Statement.** Under RH, with `D(n) = log(σ(n)/n) − γ − log log log n` and `κ = a₁ + 2 − 2√2`
  (`a₁ = 2 + γ − log 4π`): `limsup_n D(n) √(log n) log log n = κ`. Equivalently
  `liminf (e^γ log log n − σ(n)/n) √(log n) = e^γ(2√2 − 4 − γ + log 4π)` (Robin 1984, Thm 2).

## Paper
* Extremal numbers `N_x` (MUST-751): `a_p ≥ 2` for `p ≤ c₁√x` (`c₁ < √2`), `a_p = 1` for `c₂√x < p ≤ x`
  (`c₂ > √2`), eventually.
* Upper: `D(N_x)√x log x ≤ Δ√xL + G√xL − S_{c₂}√xL + (ψ − θ)/√x − θ(c₁√x)/√x + o(1)
  → Φ + 1 + 1 − 2/c₂ − c₁`; let `c₁, c₂ → √2`. General `n` via the Lagrangian bound (MUST-751),
  `κ < 0` absorbs the scale ratio `√ℓ log ℓ/(√x log x) ≥ 1`.
* Lower at `N_x`: `E_N ≤ (1 + 2/(c₁²x)) S_{c₁} + O(x^{−2/3} log x)`; `log N ≤ θ(x) + θ(c₂√x) +
  O(x^{1/3} log^{4/3} x)`; tangent bound `log log u − log log x ≤ (u − x)/(x log x)`; so
  `D(N_x)√xL ≥ Φ + 2 − c₂ − 2/c₁ − o(1)`. Along primes with `Φ(log p) > a₁ − ε` (MUST-736).

## Lean plan
- [x] generalize thresholds to `c₁ < √2 < c₂`.
- [x] PNT upper bound for `Σ_{c√x<p≤x} p^{−2}`.
- [x] sharp upper at `N_x`, then all `n`.
- [x] sharp lower at `N_x`, attainment.

## Lean status (complete)
`RHTower.robinDefectOf_sharp_constant` (RobinSharpConstant.lean), MUST-754.
