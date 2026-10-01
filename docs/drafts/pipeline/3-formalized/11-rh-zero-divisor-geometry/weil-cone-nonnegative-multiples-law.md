# Multiples-of-a-prime law for the nonnegative Weil cone

- **ID:** MC-181
- **Stage:** 3-formalized (STATUS MUST-614)
- **Type:** THEOREM (Lean)
- **Source:** MC conjecture loop cycle 181; strengthens MC-180 (MUST-611, `weil-cone-multiples-of-prime-law.md`)
- **Statement:** If `lam ≥ 0` on `n ≥ 2` is full-cone Weil-positive, then `Σ_{p∣n, n>p} lam(n)/n < ∞` for every prime `p`. Hence no nonnegative semiprime floor `lam(pq) ≥ c > 0` (fixed `p`) is Weil-positive.

## Goal
MUST-611 needed `|lam − Λ| ≤ C(1 + Λ)`. The proof used that hypothesis only through the local harmonic mass `Σ_{|log n − Z| ≤ ½} |lam − Λ|(n)/n`. For nonnegative `lam`, Weil positivity bounds this mass by itself. So the law holds on the whole nonnegative cone.

This is the uniqueness half of the corpus split RH ⟸ PBAP ∧ (`W ⊆ {Λ}`) (MUST-508/535). Every nonnegative cone member must look like `Λ` multiplicatively: up to a harmonically summable part, its mass sits on `z`-rough integers for every fixed `z`.

## Paper proof
1. **Local mass of nonnegative `lam`.** The profile `φ ≥ 0` (supported in `[−½, ½]`, `Φ(1) = ∫φ > 0`) has harmonic windows of `d = lam − Λ` at most `C/L²` for `L ≥ L₁` (`exists_profile_window_le_inv_sq`). For `|log n − Z| ≤ ½`, `Φ(log n − Z + 2) − Φ(log n − Z − 2) = Φ(1)`; for every other `n` the difference is `≥ 0`. With `lam ≥ 0`:
   `Φ(1) Σ_{|log n−Z|≤½} lam(n)/n ≤ ∫_{Z−2}^{Z+2} Σ_n lam(n) φ(log n − L)/n dL ≤ 4(C + ‖φ‖_∞ M_Λ)`.
   Here `M_Λ = (2 log 4 + 18)e^{½}` bounds the local mass of `Λ` (square-root Chebyshev). Small `Z` involve finitely many `n`. Then `|d| ≤ lam + Λ` gives bounded local mass of `d`.
2. **Local mass gives the notch bounds** (`notchBounded_of_localMassBounded`). Cover by the windows `|log n − j| ≤ ½`, `j ≥ 1` (harmonic and square-root sums, `σ > 1` sums), and by `|log n − (log N + k + ½)| ≤ ½` (the `n^{−3/2}` tail). Geometric sums give the four `NotchSmall` bounds at the level `5M + 1`.
3. **MUST-611 under local mass.** Fixed-level fibre law plus bounded `Σ d/n` (block identity plus local mass) plus the twist `|1 + ε p^{it}|²` give that `G_p` does not diverge. Monotonicity gives summability when `lam ≥ 0` on `pℕ ∩ (p, ∞)`.

## Lean
- `WeilDeviationLocalMass`: `LocalMassBounded`, `sum_mul_le_windows`, `notchBounded_of_localMassBounded`, `localMassBounded_of_abs_le`, `profilePrimitive_mono`, `exists_localMassBounded_of_nonneg`.
- `WeilConeMultiplesOfPrimeLaw`, refactored to the local-mass form:
  - `not_tendsto_atTop/atBot_multiplesSum_of_localMass`, `summable_multiples_of_localMass`, `not_summable_multiples_of_semiprime_floor`;
  - nonnegative cone: `not_tendsto_multiplesSum_of_nonneg`, `summable_multiples_of_weilPositiveFull_of_nonneg`, `not_weilPositiveFull_of_nonneg_semiprime_floor`;
  - the MUST-611 pointwise theorems are kept as wrappers.
- Audit:
  - both modules compile cleanly with `lake env lean` (oleans written with `-o`);
  - `#print axioms` gives `[propext, Classical.choice, Quot.sound]`;
  - wired into `RHTower.lean` after `WeilFibreBochnerLaw`;
  - collision scan clean (`window_nonneg` was renamed `localWindow_nonneg`);
  - `lake build` deferred: the upstream chain was invalidated by other agents.

## Open
- **Signed cone.** For signed `lam`, Weil positivity alone does not yet bound the local mass of `|lam − Λ|`. The dyadic mean-square law (MUST-591) gives `O(log)` per window, not `O(1)`.
- **Growing `z`.** Mass on integers whose smallest prime factor tends to infinity (rough semiprimes) is untouched. Reaching it needs twists over growing prime sets, which the product-type `coordBound` blocks.

## Log
- 2026-10-01: created and formalized (cycle 181).
