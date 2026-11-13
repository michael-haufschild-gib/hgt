# The order law of the edit exponential at every multiple

- **ID:** A155
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Lean:** `WorldsOfTheZeroConfiguration/TheOrdersOfTheEditExponentialObeyALawAtEveryMultiple.lean`
- **Source:** docs/reports/review-1311/obstacles-summary.md §2.1 "Models and laws of world I", A155
- **Statement:** for an edit with count `Ax + O(x^β)`, summable at `θ`, whose exponential `e^{E}`
  continues to `F` on `Re s > c₀`, the orders `n(z) = ord_z F` satisfy
  `Σ_{j=2}^{k} n(js)/j ∈ ℤ` at every `s` with `Re s > max(β, c₀, θ/(k+1))`.

## Goal
`even_order_of_count` is the case `k = 2`. The law at every `k` says which zero orders of the edit
exponential a count rate allows, and so what a count below `x^{Re ρ/k}` costs.

## Lean
| Statement | Declaration (namespace `WorldsOfTheZeroConfiguration.BalanceLaw`) |
|---|---|
| remainder `r_{k+1}`, bound, `Q_{k+1}` holomorphic on `Re s > θ/(k+1)` | `logRemOf`, `norm_logRemOf_le`, `editRemOf`, `differentiableOn_editRemOf` |
| Euler product to order `k` | `editRem_eq_sum_add` |
| Theorem 1 | `factorial_dvd_sum_order_of_count` |
| Corollary 2 | `prime_dvd_order_of_count` |
| Corollary 3 | `dvd_order_of_count_of_ne_zero` |
| Theorem 5 | `re_div_le_of_count_multiple_edit` (with `lseriesHasSum_mul_target`) |

Axioms of the headline theorems: `propext`, `Classical.choice`, `Quot.sound`.

## Setting
`e : ℕ → ℤ` an edit (signs on the primes), `E(s) = Σ_p e(p)p^{−s}`, `Σ_k |e(k)|k^{−θ} < ∞`,
`θ > 0`; count `|N(x) − Ax| ≤ Cx^β`, `0 ≤ β ≤ 1`; `F` holomorphic on `Re s > c₀`, `F = e^{E}` on
`Re s > 1`. `u(s) = (s−1)ζ(s)` (entire), `G` the continuation of `(s−1)ζ_B` to `Re s > β`
(`exists_continuation_of_count`).

## Theorems

**Theorem 1 (the order law at multiple `k`).** Let `k ≥ 1` and `Re s₁ > c := max(β, c₀, θ/(k+1))`.
Then `k! | Σ_{j=2}^{k} (k!/j) · n(j s₁)`.

**Corollary 2 (prime multiples).** If `p` is prime and `Re ρ > p · max(β, c₀, θ/(p+1))`, then
`p | n(ρ)`.

**Corollary 3 (isolated multiples).** If `k ≥ 2`, `Re ρ > k · max(β, c₀, θ/(k+1))` and
`F(jρ/k) ≠ 0` for `2 ≤ j < k`, then `k | n(ρ)`.

**Corollary 4 (the cost of an order).** If `p` is prime, `p ∤ n(ρ)`, then
`max(β, c₀, θ/(p+1)) ≥ Re ρ/p`.

**Theorem 5 (`M`-fold twins).** For a non-real `ρ` with `½ < Re ρ`, `M ≥ 1` and a prime `p ∤ M`
with `Re ρ (1 − 1/p) < 13/30`, every count exponent `β` of the greedy edit of the target
`M · (−2 Re k^{ρ−1})` satisfies `β ≥ Re ρ/p`.

## Proof

*Remainder of order `k`.* `r_{k+1}(z) = −log(1−z) − Σ_{i=1}^{k} z^i/i`,
`|r_{k+1}(z)| ≤ |z|^{k+1}/((k+1)(1−|z|))` for `|z| < 1` (Mathlib
`norm_log_one_sub_inv_add_logTaylor_neg_le`). `Q_{k+1}(s) = Σ_p e(p) r_{k+1}(p^{−s})` converges
locally uniformly on `Re s > θ/(k+1)`: `|p^{−s}|^{k+1} ≤ p^{−θ}` and `|p^{−s}| ≤ 2^{−θ/(k+1)} < 1`.
So `Q_{k+1}` is holomorphic there.

*Euler product to order `k`.* On `Re s > 1`, `−log(1 − p^{−s}) = p^{−s} + Σ_{j=2}^{k} p^{−js}/j +
r_{k+1}(p^{−s})`, so with `editRem e s = Σ_p e(p)(−log(1−p^{−s}) − p^{−s})`:
`editRem e s = Σ_{j=2}^{k} E(js)/j + Q_{k+1}(s)`, and
`(s−1)ζ_B(s) = u(s) e^{E(s)} Π_{j=2}^{k} e^{E(js)/j} e^{Q_{k+1}(s)}`.
With `N = k!` and `j | N`: `(e^{E(js)/j})^N = (e^{E(js)})^{N/j} = F(js)^{N/j}`. Hence on `Re s > 1`

`G(s)^N = P(s)^N · Π_{j=2}^{k} F(js)^{N/j}`,   `P = u · F · e^{Q_{k+1}}`.

*Continuation.* On `Re s > c` every factor is holomorphic: `G` (`c ≥ β`), `F(s)` (`c ≥ c₀`),
`F(js)` (`Re(js) ≥ Re s > c₀`, using `Re s > θ/(k+1) > 0`), `Q_{k+1}` (`c ≥ θ/(k+1)`). The
half-plane is connected, so the identity holds on `Re s > c`.

*Orders at `s₁`.* `G ≢ 0` (`G(2) = ζ_B(2) ≠ 0`), so `a = ord_{s₁} G < ∞`. `ord(G^N) = N a`. On the
right, `ord_{s₁} F(j·) = ord_{js₁} F = n(js₁)` (composition with `s ↦ js`, derivative `j ≠ 0`),
and orders add over products and multiply over powers. If `ord_{s₁} P = ⊤` the right side has
order `⊤ ≠ N a`; so `b = ord_{s₁} P < ∞` and `N a = N b + Σ_{j=2}^{k} (N/j) n(js₁)`. Hence
`N | Σ (N/j) n(js₁)`. ∎ (Theorem 1)

*Corollary 2.* Take `k = p`, `s₁ = ρ/p`; `Re s₁ > max(β, c₀, θ/(p+1))`. The orders `n(jρ/p)` are
finite (`F ≢ 0` on the connected half-plane `Re s > c₀`, and `Re(jρ/p) > c₀`). For `j < p`,
`p | p!/j` (since `p!/j = p · (p−1)!/j` and `j | (p−1)!`). Reducing Theorem 1 mod `p`:
`p | (p−1)! · n(ρ)`, and `p ∤ (p−1)!`, so `p | n(ρ)`. ∎

*Corollary 3.* `n(jρ/k) = 0` for `2 ≤ j < k`; Theorem 1 at `s₁ = ρ/k` gives
`k! = (k−1)! · k | (k−1)! · n(ρ)`, so `k | n(ρ)`. ∎

*Corollary 4.* Contrapositive of Corollary 2. ∎

*Theorem 5.* Choose `c₀` with `Re ρ − 13/30 < c₀ < Re ρ/p` (possible by hypothesis), and a prime
window exponent `α`, `17/30 < α < 1`, `α − (1 − Re ρ) ≤ c₀` (corpus window bound at `17/30`).
The target `m = M · target ρ` has `|m(k)| ≤ 2M k^{−(1−Re ρ)}`, so its greedy edit has discrepancy
`O(n^{c₀})` (`exists_abs_gdisc_le_rpow_of_abs_le`). With `L(s) = ((s−ρ)(s−ρ̄))^M`,
`L′/L = M (1/(s−ρ) + 1/(s−ρ̄)) = −Σ m(k)k^{−s} − M(ζ_reg(s−ρ+1) + ζ_reg(s−ρ̄+1))`, so the
prescribed-factor theorem gives `e^{E} = C L e^{K}` on `Re s > 1`, `K` holomorphic on
`Re s > c₀`: `F = C L e^{K}` has `n(ρ) = M`. The edit has mass `O(n^{Re ρ})`, so it is summable
at `θ = Re ρ(1 + 1/(2p))`, and `θ/(p+1) < Re ρ/p`. If `β < Re ρ/p`, Corollary 2 gives `p | M`,
a contradiction. ∎

## Remarks
- `k = 2` is `even_order_of_count`; the pair twin (`M = 1`, `p = 2`) is `half_re_le_of_count_edit`.
- The relations of Theorem 1 alone do not force `k | n(ρ)` at composite `k`: `n(w) = 6`,
  `n(w/2) = 1`, `n = 0` elsewhere, with `4c < Re w < 5c`, satisfies every relation at every level
  (`4 ∤ 6`). Whether this pattern is realized by an edit is not decided here.
- The double twin (`M = 2`) is not seen by `k = 2`; at `p = 3` it pays `β ≥ Re ρ/3` when
  `Re ρ < 13/20`: its zeta function has a cube-root branch point at `ρ/3`.

## Log
- 2026-11-13 — created; Theorems 1, 5 and Corollaries 2–4 proved on paper.
- 2026-11-13 — formalized (Corollary 4 is the contrapositive of Corollary 2, not a separate declaration).
