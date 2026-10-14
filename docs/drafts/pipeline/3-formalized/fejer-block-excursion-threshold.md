# Fejér-block excursions: the Paley–Wiener threshold is sharp

## Statement

Setting:

- lag function `Φ(t) = Σ_b (a_b(t)/2)(F_b(t) − 1)`;
- level `a_b(t) = c_b e^{δ_b t}`;
- Fejér kernel `F_b(t) = K_b^{−1}|Σ_{k<K_b} e^{ikω_b t}|²`.

**Admissible** means:

- `c_b > 0`;
- `0 ≤ δ_b ≤ Θ`;
- `ω_b ≥ ω₀ > 0`;
- `K_b ≥ 1`;
- `Σ c_b K_b < ∞`;
- `Σ 1/K_b ≤ e^{−ΘL}/8`, with `ω₀ L ≥ 12π`.

**Theorem** (`FejerData.Admissible.summable_of_excursion_le`). Let `f ≥ 0` be decreasing. If
`|{Φ > 0} ∩ [k, k+1)| ≤ e^{−f(k)k}` for all large `k`, then `Σ_b f(2^b) < ∞`.

Together with the blind side (`exists_configuration_excursion_le`: Fejér blocks achieve exactly this
bound whenever `Σ_b f(2^b) < ∞`), the excursion threshold for Fejér blocks is the Paley–Wiener
condition `∫ f(t) dt/t < ∞`.

## The level budget (abstract core)

`LevelBudget.sum_div_two_pow_le` applies to a countable family with levels `c_i > 0`, sharpness
`K_i ≥ 1`, rates `δ_i ∈ [0, Θ]` and finite mass `m = Σ c_i K_i`. Write `A(t) = Σ c_i e^{δ_i t}`.

**Hypothesis.** At `T = 2^k` the blocks with `K ≥ e^{F_k}` carry at least the fraction `η` of `A(T)`.

**Conclusion.**

`Σ_k F_k/2^k ≤ 2Θ + 4|log A(0)| + 2|log m − 2 log η|`.

Proof:

- **Markov:** `A_κ(0) ≤ m/κ`.
- **Cauchy–Schwarz in time:** `A_κ(T)² ≤ A_κ(0) A_κ(2T)`, proved by pointwise AM–GM.
- **Combination:** `F_k ≤ log A(2T) − 2 log A(T) + log(m/η²)`.
- **Telescoping:** `2 log A(2^k)/2^k` telescopes, and `log A(t) ≤ log A(0) + Θt`.

## The Fejér input

- **Spike lower bound** (`re_dirSum_ge`, `fej_ge_of_near`): `Re S_K(θ) ≥ K/2` within `1/K` of `2πℤ`,
  so `F_K ≥ K/4`.
- **One block against the rest** (`lag_ge`): `Φ ≥ a_b F_b/2 − A/2`.
- **Visibility** (`volume_core_ge`): if `a_b(T) K_b > 4e^{ΘL} A(T)`, the spike windows of width
  `2/(K_b ω_b)` inside `[T, T+L)` are excursions, of total measure `≥ L/(2πK_b)`.
- **Suppression** (`amp_mul_K_le`, `half_le_levelAbove`): thinness `L e^{−E}` on the window forces
  `a_b K_b ≤ 4e^{ΘL} A` for every blunt block `K_b < e^E/(2π)`. With `Σ 1/K_b ≤ e^{−ΘL}/8`, the
  sharp blocks carry half of the level.

## Reading

Sharpness costs mass at a fixed level, since mass equals level times `K`. The level must stay on
blocks sharp enough for the current thinness. Finite mass and bounded rates pay for this at exactly
the Paley–Wiener rate.

This settles the rigid side for the corpus' own model class. The open general problem is listed in
`1-in-progress/pw-rigid-side-excursion-threshold.md`: arbitrary positive configurations need a
covering principle that groups terms into effective blocks satisfying the share hypothesis.

## Lean

Module `RHTower/WeilLagFejerBlockExcursionRigidity` (738 lines), standard axioms, wired after
`JointAncestrySparseChainExclusion`.
