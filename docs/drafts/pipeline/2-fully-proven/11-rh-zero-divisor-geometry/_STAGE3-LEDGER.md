# Stage-3 ledger: 11-rh-zero-divisor-geometry

Goal (2026-10-05): every card here formalized unconditionally in Lean, then moved to `3-formalized`.

| Card | Lean status | Next brick |
|-|-|-|
| weil-cone-explicit-real-producer | DONE, moved to stage 3 (`RHTower/LebesgueAtomWeilPositivity`) | — |
| weil-cone-common-ratio-unions-bohr-nonvanishing | Thm B DONE (`RHTower/WeilFullConeCommonRatioRigidity`); Thm A open | discrete mollified 2nd moment on vertical APs (BCHB constant) |
| weil-cone-rational-mass-atomic-producers | (b) DONE, all atoms, both signs (`RHTower/WeilHalfIntegerMassRigidity`, `WeilRationalMassAtomicProduct`) | (a): A1–A8 below |
| weil-cone-finite-type-uniqueness | algebraic core only (`FiniteTypeDiscreteMomentAlgebra`) | boundary residue law; Gonek lemma; Jutila + Ingham density |
| verified-height-one-zero-turing-extension | consumer theorems only | BLOCKED by rules: headline is a certified numerical fact at height 3·10¹²; needs kernel Riemann–Siegel/Turing evaluation of ≈1.2·10¹³ zeros ("no computations", no `ofReduceBool`). User decision required |

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
Done (2026-10-05, axiom-clean, unwired leaf modules in `RHTower/`):
- R1 `BesselKZeroMoments` (K_j moments, Bessel ODE, `hasMellin_kZero`).
- R2 `MaassBesselSeries`, `MaassBesselFunction` (smooth λ=¼ eigenfunction, even, periodic).
- R4 `MaassAxisUniqueContinuation`, `MaassBesselHolomorphicLines`, `MaassConverseAutomorphy`.
- R3 `MaassThetaMellin`, `MaassGammaCorrections`, `MaassThetaRelation` (`kTheta_relation`).
- `MaassConverseLevelOne.maassFun_invS`: FE ⇒ `u(−1/z) = u(z)`.
- R5 `ModularInversionGreen` (S/T-invariant Green, radial anti-invariance, gradient-density invariance),
  `MaassConstantTermWronskian.constTerm_wronskian_eq_zero`.
- R6 `MaassLevelOneCuspVanishing.coeff_eq_zero_of_invS` (no even level-one cusp form at λ = ¼; Roelcke via
  corpus strip comparison + Wirtinger + explicit Bessel decay; corpus `SelbergMaassStripGap` only covers λ < ¼).
- R7 `MaassZetaSquaredConverse.coeff_eq_divisorCount_of_functional_equation` (converse theorem for ζ²),
  `WeilHalfIntegerMassRigidity.vonMangoldt_and_riemannHypothesis_of_half_integer_counting` (+ atomic form
  `half_integer_mass_rigidity`). All wired into `RHTower.lean`; standard axioms only.
- R10 (open): the card allows atoms anywhere. Small atoms (|t|<1, finitely many) give a polynomial factor `P`
  (|P| still increases in σ ≥ ½). An atom at `t = 0` of odd multiplicity flips the FE sign; then `u∘S = −u`,
  `u∘T = u` and `(ST)³ = 1` force `u = 0`. Needs a sign-ε version of `MaassThetaRelation` + automorphy.
(a) R8 datum-k exponentiation (generalize `IntegerMassRigidity` to masses in (1/k)ℕ, atoms t_j ≥ 0);
    R9 converse: explicit formula for degree-k `G` (Hadamard + contour) ⇒ producer.

## Rational-mass card (a): plan (2026-10-05)
R10 done: `WeilRationalMassAtomicProduct.bigG_pow_eq_of_fractional_counting` (any k, atoms anywhere): `G^k = K·P·Q`,
`P(1−s) = (−1)^{Σn}P(s)`. Odd sign for k = 2 killed by `(ST)³ = 1` (`coeff_eq_zero_of_odd_functional_equation`).
(a) forward: Ĝ := K·P·Q entire, zeros on the line, sign `(−1)^{kμ{0}}`, finite order (corpus
`weierstrassE1_norm_le_exp_two_norm_sq` ⇒ order ≤ 2), `Ĝ(1) ≠ 0` (pole of exact order k), `−G'/G = k·Σ lam n^{−s}`.
(a) converse (G with ζ^k FE, finite order, zeros on the line ⇒ (1/k)Λ_G Weil-positive):
- A1 generic prime-side line integral (Zeta23 `prime_side_line` is Λ-specific; generalize).
- A2 two-line residue lemma: `(1/2π)∫(H(c+it)+H(1−c−it))·g_{z₀}(c+it)dt = H(z₀)+H(1−z₀)`, `g_{z₀} = 1/(s−z₀)+1/(s−1+z₀)`,
  `1−c < Re z₀ < c`. Covers the pole terms (z₀ = 0) and every atom (z₀ = ½+it).
- A3 `W_lam(k) = (1/2π)∫(H+H̃)Φ_lam` on `Re s = c` (A1 + Zeta23 `gamma_line_shift` + A2 at z₀ = 0).
- A4 atomic explicit formula: Φ_lam atomic with c_j ≥ 0 ⇒ `W_lam(f⋆f̃) = Σ c_j(|f̂(t_j)|²+|f̂(−t_j)|²) ≥ 0`.
- A6 Hadamard: corpus `OrderOneHadamard.eq_const_mul_hadamardProduct_of_even` on `Ĝ(½+z)/z^{m₀}` ⇒ Φ_lam atomic.
- A7 finite order ⇒ order-one envelope (Phragmén–Lindelöf in the strip + Stirling on the edges).
