# No compact shift-measure port from the cosine producer to Ξ

- **ID:** ptr-compact-shift-measure-port
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** PTR loop rows 282–284; extends CANNOT-509 / MUST-1303
- **Statement:** For `h ≠ 0`, finite complex measures `μ_k` supported in a compact interval, and polynomials
  `Q_k`, `Σ_k Q_k(t) ∫ A_h(t + is) dμ_k(s) ≠ Ξ(t)` for some real `t` (first without `t`-derivatives of `A_h`).

## Goal
CANNOT-509 excludes finitely many imaginary shifts. This is the compactly supported continuous analogue, the
last shift-type class before infinite-order, frequency-splitting ports. Note that the canonical port
`sec(hD) = Σ_k (−1)^k e^{−(2k+1)h|D|}` is a series of Poisson semigroup operators (kernel multiplier
`e^{−y|u|}`), not of shifts. It splits frequencies like an analytic signal or Hilbert transform.

## Approach
- **Kernel side:** `∫ A_h(·+is) dμ(s)` has kernel `Φ cosh(hu) m_μ(u)`, with `m_μ(u) = ∫ e^{−su}dμ(s)`.
  `d/du` maps `m_μ` to `m_{−sμ}`, so the class of `c · m_ν(u) e^{βu} Φ^{(j)}(u)` is closed (no `u^a` factors
  without `t`-derivatives).
- **Mode separation:** as in `CosineProducerShiftPortObstruction`.
- **Head uniqueness:** each head is a compact Fourier–Borel transform. Use corpus carrier separation
  `compactFourierBorel_eq_zero_of_ray_decay` in place of the exponential-polynomial leading-term lemma.
- **Grading:** exact grading turns into identities of measures in the exponent variable. The extreme point of the
  combined support is supplied by a single shifted copy, which forces the top part to vanish. Induct.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven
- [x] 2 → 3  formalized: `RHTower/CosineProducerMeasurePortObstruction.lean`,
  `not_exists_measure_port_cosineProducer`. Standard axioms, olean built, wired, lint clean for the module.

## Result
CANNOT-510. Derivatives of `A_h` were not needed: `t`-polynomials become `(i d/du)^m`, and the binomial
structure plus the triangular cusp system closes the argument. Uniqueness for Fourier–Borel sums used the
corpus two-ray Paley–Wiener vanishing rather than carrier separation.

**Remaining PTR port class:** infinite-order operators with unbounded shift support and frequency splitting,
like `sec(hD) = Σ(−1)^k e^{−(2k+1)h|D|}`. That is the canonical-system realization of row 263.

## Log
- 2026-10-12 — created in 0-backlog (PTR loop row 284).
- 2026-10-12 — formalized (PTR loop row 285, CANNOT-510).
