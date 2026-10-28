# The gap of the prime form below its pole is 2 log 2

- **ID:** rapt-sharp-gap-of-prime-form-is-two-log-two
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** RP29 (non-sharp gap); `0-backlog/rapt-top-spectrum-of-prime-form-is-log-integers.md`.
- **Statement:** For every `ε > 0`, eventually in `N`: `P_N ≤ (log N − γ − 2 log 2 + ε)|x|²` on
  `x ⊥ n^{−1/2}`, and some `x ⊥ n^{−1/2}`, `x ≠ 0`, has `P_N(x) ≥ (log N − γ − 2 log 2 − ε)|x|²`.
  So `λ₂(P_N) = log N − γ − 2 log 2 + o(1)`, and the first excited state is the 2-adic step.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven
- [x] 2 → 3  formalized: `eventually_atomicWeilForm_below_pole_two_log_two`, axioms
  `[propext, Classical.choice, Quot.sound]`

## Proof

Pole gauge `y = √n x`, harmonic measure `1/n` on `[1, N]`, `D = Σ Λ(t)/(mt)(y_{mt} − y_m)²`. The
upper bound is `D ≥ (2 log 2 − ε) Var(y)` eventually; the ground-state identity with its top control
(`eventually_atomicWeilForm_add_poleDefect_le`) then gives
`eventually_atomicWeilForm_le_two_log_two`.

1. **Finite prime chain** (`TheValuationChainOfFinitelyManyPrimesHasGapTwoLogTwo`). On the box
   `Π_{p<Q}{0..J}` with weights `1/a`, Efron–Stein (`boxVar_le_boxGlauber`) and the sharp ladder
   `log p Σ_{j≤J} p^{−j} ≥ 2 log 2 (1 − 2^{−J−1})` (`boxGap_le_ladder`). On `Q`-smooth `a ≤ X`, zero
   extension costs only edges leaving `[1, X]` (`smoothBoundary_le`), and the halo
   `Σ (1/a) log a · u² ≤ 2E + 2M_Q Σ (1/a) u²` (`sum_log_mul_sq_le_smoothEnergy`) pays it:
   `eventually_smoothVar_le_smoothEnergy`.
2. **Two scales** (`TheSpectralGapOfThePrimeFormIsTwoLogTwo`). `n = a b`, `a` the `Q`-smooth part
   (`sum_Icc_eq_smooth_rough`). Total variance: `Var ≤ Σ_a V_a/a + Σ_a (F(N/a)/a)(h_a − c)²`, with
   `h_a` the fibre means and `F` the rough harmonic mass.
   - Fibres: rough tensorization (`exists_harmonicVar_le_glauberForm_rough`) and base edges give
     `Σ_a V_a/a ≤ (K/log Q) D_L` (`sum_fibreVar_le`).
   - `a ≤ X`: Module A. The chain of fibre means is paid edge by edge
     (`roughHarmonic_mul_sq_fibreMean_sub_le`). Jensen on the common fibre, plus the nested-mean
     error `(F(N/a) − F(N/at))V_a/F(N/a)` with the shell bound `F(Y) − F(Y/t) ≤ 1 + log t`
     (`roughHarmonic_sub_div_le`). Summing (`roughHarmonic_mul_smoothEnergy_le`), with
     `Σ_k (log p/p^k)(1 + log p^k) ≤ 8 log p`, gives
     `F(N) E_X(h) ≤ (F(N)/F(N/X))((1+η) D_S + (1+1/η)(8L_Q/F(N/X)) U)`.
   - `a > X`: the halo applied in each rough fibre over `b` (`sum_log_mul_fibre_le`).
   - Assembly: `two_scale_le`, then the parameter order `ε → Q → X → N`
     (`exists_cutoff_div_log_le`, `exists_horizon`, `eventually_le_roughHarmonic_div`,
     `ratio_bounds`, `gap_of_two_scale`) gives `eventually_mul_harmonicVar_le_poleDefect`.
3. **Sharpness** (`TheFirstExcitedStateOfThePrimeFormIsTheTwoAdicStep`). Take
   `x = (1_{2∣n} − E_N/H_N)/√n`. In the gauge only the edges `m → m 2^k` with `m` odd move the
   parity. Using the small-edge identity (`sum_smallEdge_eq`) and the 2-adic ladders,
   `D_N(x) = log 2 · E_N` (`poleDefect_twoAdicStep`). With `|x|² = E_N − E_N²/H_N` and
   `E_N = H_{⌊N/2⌋}/2 ≤ H_N/2`, this gives `D_N ≤ 2 log 2 |x|²` for every `N`
   (`poleDefect_twoAdicStep_le`). Mertens on the rows from below (`exists_row_ge`,
   `sum_row_mul_sq_ge`) and `|x|² ≥ log(N/2 + 1)/4` give
   `eventually_exists_atomicWeilForm_ge`.

## Insight

The Poincaré constant of the multiplicative walk under harmonic measure on `[1, N]` converges to
`2 log 2 = (p log p/(p − 1))|_{p=2}`, the infinite 2-ladder's gap. The extremal state is
1-dimensional, along the 2-adic valuation. This matches the finite-prime model's level
`γ + log 2 + d(2)` with `d(2) = log 2`: the first excited level of the backlog conjecture on the top
spectrum.

## Log
- 2026-10-28 — created; plan. Module A (steps 1–3) formalized.
- 2026-10-28 — Module B and sharpness formalized; RP37.
