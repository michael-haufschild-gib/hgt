# Stage-3 ledger: 11-rh-zero-divisor-geometry

Goal (2026-10-05): every card here formalized unconditionally in Lean, then moved to `3-formalized`.

| Card | Lean status | Next brick |
|-|-|-|
| weil-cone-explicit-real-producer | DONE, moved to stage 3 (`RHTower/LebesgueAtomWeilPositivity`) | — |
| weil-cone-common-ratio-unions-bohr-nonvanishing | Thm B DONE (`RHTower/WeilFullConeCommonRatioRigidity`); Thm A open | discrete mollified 2nd moment on vertical APs (BCHB constant) |
| weil-cone-rational-mass-atomic-producers | open | (a) datum-k exponentiation; (b) level-1 Maass converse at λ=¼ |
| weil-cone-finite-type-uniqueness | algebraic core only (`FiniteTypeDiscreteMomentAlgebra`) | boundary residue law; Gonek lemma; Jutila + Ingham density |
| verified-height-one-zero-turing-extension | consumer theorems only | needs a kernel-checked Turing/Riemann–Siegel certificate at height 3·10¹² (≈1.2·10¹³ zeros) |

## Reusable corpus facts found this goal
- Theorem B needs no Theorem A: `WeilAbscissa.eq_vonMangoldt_of_weilPositiveFull_of_sparse_rpow`.
- Step 3 of finite type ≈ `WeilRegular.eq_zero_of_weilPositive_add` (linear growth only; card allows polynomial).
- Explicit formula for ζ is proved: `WeilEF.EF_lit_zetaZeroConfig`.
- Corpus Ingham–Huxley has a `T^ε` loss (`exists_zeroHeightBox_ncard_le_ingham_huxley`); corpus Selberg
  near-line density decays only like `1/a` (`exists_selberg_nearLine_zeroDensity`). Neither suffices for Lemma C′.

## Rational-mass card: brick plan
(b) k = 2, G = ζ² (level-one Maass converse at λ = ¼):
- R1 K₀ = `modifiedBesselKOrder · 0`: Mellin `∫K₀(r)r^{s−1}dr = 2^{s−2}Γ(s/2)²`, ODE, holomorphic extension in the argument, decay.
- R2 `u_g(x+iy) = 4√y Σ g_n K₀(2πny)cos 2πnx + √y(b + a log y)`: C^∞, `Δu = u/4`, even, 1-periodic.
- R3 theta relation `u(i/y) = u(iy)` from `Λ(s) = Γ_ℝ(s)²G(s)` even with double poles (a, b = Laurent data at 1).
- R4 PDE uniqueness: `v = u − u∘S` with `v = ∂ₓv = 0` on iℝ₊ ⇒ `v ≡ 0` (x-analyticity + derivative recursion).
- R5 Wronskian: Green (`SelbergModularCurrentGreen`) ⇒ constant terms of `u_G`, `u_{ζ²}` proportional.
- R6 Roelcke: level-one cusp eigenfunction with `λ < 3π²/2` vanishes (`SelbergModularPotentialGreen`, `SelbergModularStripComparison`, Wirtinger).
- R7 assemble: `G = ζ²` ⇒ `F = ζ` ⇒ `lam = Λ`, RH.
(a) R8 datum-k exponentiation (generalize `IntegerMassRigidity` to masses in (1/k)ℕ, atoms t_j ≥ 0);
    R9 converse: explicit formula for degree-k `G` (Hadamard + contour) ⇒ producer.
