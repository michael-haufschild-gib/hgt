# Lattice excursions obey the level budget

## Statement

Setting:

- lattice configuration `Φ(t) = Σ_i c_i e^{δ_i t} cos(m_i t)`;
- weights `c_i > 0`, integer frequencies `m_i ≥ 1`, rates `δ_i ∈ [0, Θ]`;
- finite frequency moment `μ_α = Σ c_i m_i^α`, `α > 0`;
- excursion measure `v(T) = |{Φ > 0} ∩ (T, T+2π]|`.

**Theorem** (`LatticeExcursion.Admissible.sum_log_inv_excursion_le`).

`Σ_{k<n} log(1/v(2π2^k))/2^k ≤ (4πΘ + 4|log Σc| + 2|log μ_α − 2 log ¾|)/α + 2|log(π/(8e^{2πΘ}))|`.

**Corollary** (`Admissible.summable_of_excursion_le`). If `v(2π2^k) ≤ e^{−f(2π2^k)·2π2^k}` eventually
and `f ≥ 0`, then `Σ_k f(2π2^k) < ∞`. This is the rigid side of the Paley–Wiener threshold, with no
block structure.

## Proof

1. **Period positivity.** For `T ∈ 2πℤ`, `δ ≥ 0` and integer `a`,
   `∫_T^{T+2π} e^{δt} cos(at) dt = e^{δT} δ(e^{2πδ} − 1)/(δ² + a²) ≥ 0`. The case `a = 0` gives at
   least `2πe^{δT}`. Expanding by product-to-sum, every term of `Φ(t)(1 + cos kt)` has a nonnegative
   period integral, and the terms with `m_i = k` contribute at least `π c_i e^{δ_i T}`.
2. **Frequency amplitudes.** Since `Φ ≤ 0` off `E = {Φ > 0}` and `Φ ≤ A(T) e^{2πΘ}` on the period,
   `π A_k(T) ≤ 2 A(T) e^{2πΘ} v(T)`.
3. **Share.** The frequencies `≤ N = ⌊π/(8e^{2πΘ} v)⌋` carry at most `A/4`.
4. **Level budget** (`LevelBudget.sum_div_two_pow_le`). Use sharpness `K_i = m_i^α`, mass `μ_α` and
   rates `2πδ`. Markov and Cauchy–Schwarz in time `A_κ(T)² ≤ A_κ(0) A_κ(2T)` give
   `Σ α log(N_k + 1)/2^k ≤ 4πΘ + C`.

## Reading

- Frequency mass is the currency: sharp structures need high frequencies, and the moment pays for
  them.
- Cycle 207b found that linear Bochner bounds admit sparse handovers. That holds only when the
  frequency moment is infinite.
- The Fejér-block theorem (MUST-1401, `fejer-block-excursion-threshold.md`) handles infinite moments
  inside its class. The corpus blind construction has an infinite moment for every `α > 0`.
- For ζ, the lag configuration has `Σ |w_ρ||γ_ρ|^α < ∞` for every `α < 1`, but its ordinates are not
  a lattice. A non-lattice version, with almost-periods replacing exact periods, would give "RH ⟺ JAS
  positivity off PW-thin log-scales" with no side condition.

## Lean

Module `RHTower/WeilLagLatticeExcursionBudget` (601 lines), standard axioms, wired after
`WeilLagFejerBlockExcursionRigidity`.
