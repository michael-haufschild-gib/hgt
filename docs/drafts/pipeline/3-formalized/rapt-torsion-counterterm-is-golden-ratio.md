# The torsion counterterm is the golden ratio

- **ID:** rapt-torsion-counterterm-is-golden-ratio
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** RAPT §9 topic 4 ("the exact torsion constant", window `[3/2, 2]`, continuum prediction
  `e/(e − 1)`); `rapt-deficit-of-prime-form-is-dirichlet-energy` (ground-state identity).
- **Statement:** For every `N ≥ 1`, with `φ = (1 + √5)/2`, `C_e` the Hecke excess constant and `K` the
  tame constant:
  `κ = φ(log N + log 4 + 4) + 2C_e` renormalizes the torsion pairing on the orders `≤ N`, and every
  renormalizing `κ` satisfies `κ ≥ φ(log N − log 2 − log 4 − 4) − 4φ²K`. Equivalently the top of
  `T_N = diag(log n) + P_N` is `φ log N + O(1)`.

## Proof

Upper bound. `log n = Σ_{t∣n} Λ(t)` gives `Σ log n · x_n² = Σ_{mt ≤ N} Λ(t) x_{mt}²`. On each edge
`x_{mt}² ≤ φ²(x_{mt} − x_m/√t)² + φ x_m²/t` (defect `φ(a − φb)²`), so
`Σ log n x² ≤ φ² D_N + φ Σ A(⌊N/m⌋) x_m²`. With `P_N = Σ(A + log n)x² − D_N`,
`T_N ≤ (2 − φ^{−2}) Σ log n x² + (1 + φ^{−1}) Σ A x² = φ Σ (A + log n) x²` (`φ² = φ + 1`), and
`A(⌊N/n⌋) + log n ≤ log N + log 4 + 4`.

Lower bound. `x_n = φ^{ω(n)}/√n`, weight `g = φ^{2ω}`. Edge mass `a(m,t) = Λ(t) g(m)/(mt)`; coprime
edges `U`, the rest `W`. Exactly: `J = Σ log n x² = φ² U + W`, `P_N = 2(φ U + W)`, so
`T_N = (φ² + 2φ) U + 3W`. Mertens (`A(y) ≥ log y − log 4 − 4`, `⌊N/m⌋ ≥ N/(2m)`):
`U + W = Σ (g(m)/m) A(⌊N/m⌋) ≥ (log N − K′) S − J`, hence `(1 + φ²) U + 2W ≥ (log N − K′) S`.
Since `φ(1 + φ²) = φ² + 2φ`: `T_N ≥ φ(log N − K′) S − (2φ − 3) W`. Non-coprime edges: `W ≤ Σ (g(m)/m) d(m)`
(`d` the tame different; prime-power edges through `p` carry `≤ log p/(p − 1)`), and the multiples of `p`
carry `≤ φ²/(p − 1)` of the golden mass (`p`-ladders), so `W ≤ 2φ²K S`. Torsion: diagonal
`c(n) = log n − d(n)`, off-diagonal `≥ P` (`φ(mt) ≤ tφ(m)`), charges `y_n = φ^{ω(n)}(nφ(n))^{−1/2}`.

## Significance

- Answers RAPT topic 4. The continuum model `𝟙⊗𝟙 + log n` predicts `e/(e − 1) ≈ 1.582`; the true
  constant is `φ ≈ 1.618`. Numerics (Lanczos, `N ≤ 10⁵`): slopes `d λ_max/d log N` = 1.599, 1.603,
  1.606, 1.608 (approaching `φ`, past `e/(e − 1)`).
- Mechanism: the extremal charges are multiplicative, `φ^{ω(n)}`; on every coprime Hecke edge the
  charge rises by `φ`, the equality case `a = φ b` of the golden split. The prime place and the
  self-intersection balance at the fixed point of `z ↦ 1 + 1/z`. Arithmetic structure
  (`ω(n)`, not `log n`) decides the counterterm: the first counterterm in the programme where
  pointwise (edge-local) bounds are sharp and the radial continuum model is not.
- The anomaly cost (torsion minus covariant counterterm) is exactly `(φ − 1) log N = log N/φ + O(1)`,
  inside the old `[½, 1]` window.

## Status

Lean: `formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheTorsionCountertermIsTheGoldenRatio.lean`
(`gold_amgm`, `sum_log_mul_sq_le_golden`, `diag_add_atomicWeilForm_le_golden`,
`diag_add_atomicWeilForm_le_golden_log`, `goldenTest`, `goldenTest_edge`, `sum_vonMangoldt_div_dvd_le`,
`sum_noncoprime_vonMangoldt_le`, `sum_goldenWeight_dvd_le`, `sum_goldenWeight_tame_le`,
`diag_add_atomicWeilForm_goldenTest_ge`, `torsionCounterterm_golden`). Clean exact-file check; axioms
`propext, Classical.choice, Quot.sound`; wired in the RAPT umbrella.

Open: the `O(1)` term; whether the extremal vector of `T_N` converges (in the pole gauge) to
`φ^{ω(n)}`; twisted torsion pairings.
