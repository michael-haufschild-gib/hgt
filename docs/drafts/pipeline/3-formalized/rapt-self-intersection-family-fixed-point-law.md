# The self-intersection family obeys a fixed-point law

- **ID:** rapt-self-intersection-family-fixed-point-law
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** generalizes `rapt-torsion-counterterm-is-golden-ratio` (α = 1, top) and the ground-state
  identity of `rapt-deficit-of-prime-form-is-dirichlet-energy` (α = 0).
- **Statement:** For `κ ≠ 0`, `α = κ − 1/κ`, and every `N`, `x`:
  `α Σ log n x_n² + P_N(x) + D_κ(x)/κ = κ Σ_n (A(⌊N/n⌋) + log n) x_n²`,
  `D_κ(x) = Σ_{mt ≤ N} Λ(t)(x_{mt} − κ x_m/√t)²`. Consequently, with `κ₊ > 0 > κ₋` the roots of
  `κ² = ακ + 1`: `κ₋(log N + log 4 + 4) ≤ α diag(log n) + P_N ≤ κ₊(log N + log 4 + 4)` and the vectors
  `κ±^{ω(n)}/√n` attain `κ± log N + O(1)` (errors `≤ 2K|κ|(1 − κ)² + |κ|(log 2 + log 4 + 4)`).

## Proof

Expand `D_κ` on the edges: `D_κ = Σ log n x² − κ P_N + κ² Σ A x²` (Chebyshev identity for the first,
`P_N = 2 Σ Λ(t)t^{−1/2} x_m x_{mt}` for the second, `Σ_t Λ(t)/t = A` for the third); then
`α + 1/κ = κ`. `D_κ ≥ 0` gives the ends (sign of `κ`) with the row bound `A + log n ≤ log N + log 4 + 4`.
For `x = κ^{ω}/√n`: coprime edges satisfy `x_{mt} = κ x_m/√t` exactly; non-coprime edges give
`(1 − κ)² x_m²/t`, which sums to `≤ (1 − κ)² Σ_m x_m² d(m) ≤ 2Kκ²(1 − κ)²|x|²` (`d` the tame different,
multiples of `p` carry `≤ κ²/(p − 1)` of the `κ^{2ω}`-mass). The rows are `≥ log N − log 2 − log 4 − 4`.

## Significance

- The whole spectral range of the self-intersection family is computed: two multiplicative extremals
  per `α`, the fixed points of `z ↦ α + 1/z`. `α = 0`: `[−log N, log N]` (pole and alternating
  charges `(−1)^{ω(n)}`). `α = 1` (torsion): `[−log N/φ, φ log N]`; numerics for the bottom: slopes
  −0.601, −0.606, −0.608, −0.611 (N = 10³…10⁵) → `−1/φ`.
- The deficit of every end is a twisted Dirichlet energy: `D_κ` measures the failure of the
  `κ`-twisted pole relations `x_{mt} = κ x_m/√t`; `κ = 1` is the pole, `κ = −1` the Liouville-type
  alternation, `κ = φ` the torsion extremal.
- Semicircle law (`abs_atomicWeilForm_le_semicircle`): `|P_N(x)| ≤ 2√(H(L′S − H))`, `H = Σ log n x²`,
  `S = |x|²`. The family's ends are the support function of the disk `v² ≤ 4u(1 − u)` in the
  (height, prime form)/`log N` plane: the prime form is the off-diagonal component of a large spin
  whose diagonal is the height. Sharp at the pole (`u = ½`, `v = 1`) and along `κ^{ω(n)}/√n`.
- AIT: the renormalized torsion form `−P_N − diag(c)` reaches `log N/φ − O(1)` on
  `(−1/φ)^{ω(n)}/√n` (its largest positive square).

## Status

Lean: `formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheSelfIntersectionFamilyObeysAFixedPointLaw.lean`
(`twistedPoleDefect`, `twistedPoleDefect_eq`, `fixedPoint_identity`, `sum_row_mul_sq_le`,
`sum_row_mul_sq_ge`, `fixedPoint_top_le`, `fixedPoint_bottom_ge`, `omegaWeight`, `fixedPointTest`,
`sum_omegaWeight_dvd_le`, `sum_omegaWeight_tame_le`, `twistedPoleDefect_fixedPointTest_le`,
`fixedPoint_top`, `fixedPoint_bottom`). Clean exact-file check; axioms
`propext, Classical.choice, Quot.sound`; wired in the RAPT umbrella.

Open: the second eigenvalue of `α diag(log n) + P_N` (gap below `κ₊ log N`); twisted versions
(characters) of the law.
