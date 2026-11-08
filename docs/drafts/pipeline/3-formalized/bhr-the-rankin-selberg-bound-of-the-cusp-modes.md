# BHR — the Rankin–Selberg bound of the cusp modes

- **ID:** bhr-cusp-rankin-selberg
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** C12/C13 had absolute convergence of the cusp L-functions only on `Re s > 3/2` (from `|ρ(n)| ≤ C√|n|`).
- **Statement:** Let `g ∈ S(λ)` with Whittaker coefficients `ρ(n)`.
  1. There is `A` with `Σ_{n} |ρ(n)|² |n|^{−σ} ≤ A/(σ − 1)` for `σ ∈ (1, 2]` (and the series converges).
  2. `Σ_{|n| ≤ N} |ρ(n)|² ≤ A' N log N` for `N ≥ 3`.
  3. `Σ_n |ρ(n)| |n|^{−σ} < ∞` for every `σ > 1`.
  4. For Hecke eigenforms the Euler product of `L(s)` holds for every `Re s > 1`.

## Paper proof
1. *Mass decay.* By the modal bound `|a_n(y)| ≤ b_n √y e^{−2πy}` (`Σ b_n = B`), the horocycle mass
   `m(y) = Σ_n |a_n(y)|² ≤ B² y e^{−4πy}` for `y ≥ 1`; also `m ≤ sup|g|²`.
2. *Upper bound.* For `σ ∈ (1, 2]`: `∫_0^∞ m y^{σ−2} ≤ sup|g|² ∫_0^1 y^{σ−2} + ∫_1^∞ m ≤ C/(σ−1) + T`.
3. *Lower bound.* Pick `X ≥ 1` with `Re K_ν > 0` on `[X, ∞)` and `κ₀ = min_{[X,2X]}|K_ν|² > 0`. On
   `2π|n|y ∈ [X, 2X]`, `|a_n(y)|² y^{σ−2} = |ρ(n)|² y^{σ−1}|K_ν(2π|n|y)|² ≥ |ρ(n)|² (X/c)^{σ−1} κ₀`, `c = 2π|n|`,
   on an interval of length `X/c`: the modal transform is `≥ |ρ(n)|² κ₀ X^σ (2π|n|)^{−σ}`.
4. *Tonelli* (`m = Σ_n |a_n|²` pointwise, nonnegative): `κ₀ X^σ (2π)^{−σ} Σ_n |ρ(n)|²|n|^{−σ} ≤ C/(σ−1) + T`, and
   `κ₀X^σ(2π)^{−σ} ≥ κ₀X(2π)^{−2}`.
5. *Mean square.* `σ = 1 + 1/log N`: `|n|^{−σ} ≥ N^{−σ}` for `|n| ≤ N` and `N^σ = eN`.
6. *Convergence.* `|ρ| |n|^{−σ} ≤ ½(|ρ|² + 1)|n|^{−min(σ,2)}`; the Euler product theorem of C13 needs only this.

## Lean certificate
`formal/GaloisForLFunctions/BlackHoleRingdown/TheRankinSelbergBoundOfTheCuspModes.lean`, wired into
`BlackHoleRingdown.lean`, checked with `lake --old env lean`, no messages. Axioms of `mean_square_le`,
`cusp_euler_product_one`: `propext`, `Classical.choice`, `Quot.sound`. Supporting refactors: `CuspL.norm_mode_le`
(C12 module), `CuspEuler.cusp_euler_product_of_summable` (C13 module).

| Claim | Theorems (namespace `BlackHoleRingdown.CuspRS`) |
|---|---|
| (1) | `exists_window`, `slice_le_decay`, `lintegral_slice_le`, `lintegral_mode_ge`, `summable_sq` |
| (2) | `mean_square_le` |
| (3) | `summable_abs` |
| (4) | `cusp_euler_product_one` |

## Scope
"Ramanujan on average" for the cusp modes, without the Eisenstein unfolding. The sharp `Σ_{|n|≤N}|ρ(n)|² ~ cN`
and the continuation of `Σ|ρ(n)|²|n|^{−s}` (which carries `ξ(2s)` through `∫|g|²E(·,s)`) are not formalized.

## Log
- 2026-11-08 — created and formalized.
