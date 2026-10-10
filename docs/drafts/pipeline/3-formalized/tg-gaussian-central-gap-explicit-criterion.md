# TG — explicit uniform central Gaussian criterion

- **ID:** TG-EXPL-1
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean, unconditional)
- **Source:** TG-BIAS-1 (critical germ bound, A(½) ≤ −7/24), undamped archimedean defect (TG cycle 5)
- **Statement:** RH ⟺ ∀ y ∈ (0,1]: Σ Λ(n)n^{-1/2}e^{-yn²} − ∫₁^∞u^{-1/2}e^{-yu²}du ≤ −1/10 + 32√y.

## Proof
Gap = Re A_y(½) − Re Z_y with Z_y the germ field. ‖A(½) − A_y(½)‖ ≤ (y(‖c_A‖ + 3/2) + 4(2y +
2Γ(3/2)√y))·π²/6 ≤ 18√y·1.654 ≤ 31√y (‖c_A‖ = |½ − ½log π − γ/2| ≤ 1, Γ(3/2) < 0.8875, π < 3.15).
Under RH |Z_y| ≤ 2(1+y)(2+γ−log 4π) < 0.1848(1+y) for every y > 0. So gap ≤ −7/24 + 31√y + 0.1848 +
0.1848√y ≤ −1/10 + 32√y. Converse: the bound is ≤ 32 on (0,1], central budget law.

## Lean
`RHTower/GaussianCentralGapExplicitCriterion.lean` (157 lines), wired after GaussianPrimeChebyshevBias.
`riemannHypothesis_iff_gaussianCentralGap_le_explicit`, `gaussianCentralGap_le_explicit_of_riemannHypothesis`,
`norm_gaussianArchimedeanCurrent_half_sub_MB_le`. Build exit 0; axioms [propext, Classical.choice, Quot.sound].

## Reading
A Robin-type Π⁰₁ form of the TG central budget: all constants explicit, a single violating y refutes
RH, and for y < (1/320)² it forces the prime sum below the continuum (sign gate).
