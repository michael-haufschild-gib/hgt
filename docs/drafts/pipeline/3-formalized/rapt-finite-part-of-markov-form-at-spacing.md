# The finite part of the Markov form at the spacing scale

- **ID:** rapt-finite-part-of-markov-form-at-spacing
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rapt-deficit-of-prime-form-is-dirichlet-energy` (pole defect pays the top atoms),
  `ssha-robin-constant-of-an-atom` (exact self-energy), AE/SSHA stability laws (crude constants).
- **Statement:** Let `φ` be a `K`-Lipschitz `C²` profile on `[0, 1]` with `∫φ² > 0`, `g = φ(·/w)`,
  `f = Σ_{n ≤ N} x_n g(· − log n)`, `M(f)` the Markov form (Weil's form without the pole term).
  For `0 < ε ≤ 1/2`, eventually in `N`, for every `w ≤ δ_N/2` with `wN ≤ 1/(64e²)` and every `x`:
  `M(f) ≥ (2θ′(0) + log(1/(wN)) + κ_L(φ) + γ − ε − (e^{1/2}/2) w − A·wN) ‖f‖²`,
  `A = 2(16e² + 3 + 16e²(log 4 + 4))`. For `φ ≥ 0` and the pole `x_n = n^{−1/2}`, eventually
  `M(f) ≤ (2θ′(0) + log(1/(wN)) + κ_L(φ) + γ + ε + (e^{1/2}/2) w) ‖f‖²`.
  So the ground energy of the Markov form at `w = c/N` is `2θ′(0) + log(1/c) + κ_L(φ) + γ + O(c) + o(1)`.

## Proof

1. Exact diagonal: `∫(f − f(·+y))² = Σ x_m² ∫(g − g(·+y))² − 2 Σ_{m≠n} x_m x_n G(y − log(n/m))`
   (`G` the autocorrelation, `‖g‖²`-bounded, supported in `[−w, w]`). Integrated against `ω` on
   `(0, ∞)`: `levyEnergy f ≥ Σ x_m² levyEnergy g − 2‖g‖² Σ_{m≠n} |x_m||x_n| W_{mn}`, `W_{mn}` the
   `ω`-mass of the window `|y − log(n/m)| ≤ w`; for nonnegative atoms and `x ≥ 0` the cross terms
   have a sign and `levyEnergy f ≤ Σ x_m² levyEnergy g`.
2. Windows: `|log(n/m)| ≥ δ_N ≥ 2w`; `ω` antitone, `ω(y) ≤ 1/(2y) + 1`, so
   `W_{mn} ≤ 2w(1/|log(n/m)| + 1)`.
3. Rows: `1/|log(n/m)| ≤ e²m/|n − m| + 1/2`; harmonic row sum; so the Schur rows are
   `≤ wN(4e²(m/N)(1 + log(N + 1)) + 3)`, and `(m/N)(1 + log(N+1)) ≤ 4 + 2(m/N) log m`.
4. Mean-square payment: `Σ (m/N) log m · x_m² ≤ 2D_N + 2(log 4 + 4)|x|²` (pole defect), and
   `P_N + (1 − ε)D_N ≤ (log N − γ + ε)|x|²`; the defect keeps weight `1 − ε − 32e²wN ≥ 0`.
5. Self-energy: `|levyEnergy g − (log(1/w) + κ_L(φ))‖g‖²| ≤ (e^{1/2}/2) w ‖g‖²`. Upper bound:
   `P_N(pole) ≥ (log N − γ − ε)|pole|²`.

## Significance

- The finite part of Weil's form without the pole, at the spacing scale, is identified exactly:
  Robin constant of the atom (archimedean place) + Euler constant (prime place, pole vector).
  The previous stability laws had constants `C₀ = 2(log 4 + 4) + 1` and `c₀ = c₁e^{−(C₀+2|θ′(0)|)}`.
- Mechanism: the archimedean cross kernel has rows `≍ c (m/N) log N`, unbounded on the top atoms;
  the tilt of the pole paid them row by row at a cost exponential in the constants. Here they are
  paid in mean square by the Dirichlet energy of the pole relations, the same energy that is the
  deficit of the prime form.
- Positivity window: `M ≥ 0` whenever `2θ′(0) + log(1/c) + κ_L(φ) + γ > A c + o(1)`; the threshold
  is governed by `e^{2θ′(0) + κ_L(φ) + γ}` up to `O(c)`.

## Status

Lean: `formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheFinitePartOfTheMarkovFormAtTheSpacing.lean`
(`archLevyDensity_le_inv_add_one`, `window_integrable_and_le`, `integral_sub_shift_sq_atomicTest_eq`,
`levyEnergy_atomicTest_ge_diag`, `levyEnergy_atomicTest_le_diag`, `sum_inv_abs_logGap_add_one_le`,
`sum_abs_mul_sym_le`, `div_mul_log_le`, `cross_penalty_le`, `eventually_markovEnergy_atomicTest_ge`,
`eventually_markovEnergy_truncPole_le`). Clean exact-file check; axioms
`propext, Classical.choice, Quot.sound`; wired in the RAPT umbrella.

Open: the `O(c)` constant (A ≈ 1.5·10³ is crude); signed profiles for the upper bound; the pole
term `2C² − 2S²` on top of the finite part (Weil's form itself, B3.26 at `K < 1`).
