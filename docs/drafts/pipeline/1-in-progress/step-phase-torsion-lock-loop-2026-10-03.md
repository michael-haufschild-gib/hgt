# Step phases and ℤ/3 torsion locks: conjecture loop (2026-10-03)

- **ID:** step-phase-torsion-lock-loop
- **Stage:** 1-in-progress
- **Type:** LOOP CARD (targets T1, T2, set by the user)
- **Source:** spark loop S28 (`spark-conjecture-loop-2026-10-03.md`); lock theory `3-formalized/11-rh-zero-divisor-geometry/weil-cone-lock-phase-rigidity.md`; twins C329/C394; ledger L223/L224, L278-CORR, L318.
- **T1.** A radial or contour argument that handles step lock phases (a monotone lift with jumps, total variation ≥ linear).
- **T2.** A structural obstruction to ℤ/3 torsion locks: `lam ∈ W` with `μ_lam ∈ (1/3)ℤ` atoms, i.e. real-rooted `F ∈ V₃ ∖ {ζ³}` (MUST-670).

## Frontier (corpus, verified this session)
- Lock rigidity [L]: non-integer mass `O(T^α)`, `α < 1`; monotone bounded twists (MUST-677); C¹ / a.p. / settled locks; carried-by-Z (MUST-718).
- Engine: Hamburger reflected radial limits `ε J(ε+im) → β/π`. The defect needs signed radial limits → 0 (`HamburgerTwistedRadialDefect`).
- L224 Lemma C [P mod Gonek]: `∫ e^{2πiN_ν}|F|² w = 2πΣ (b⋆b)(n) w(2πn) + O(T^{1−δ})`.
- MUST-603 [L] (Hamburger stability): `∫|F||sin πN_ν| = o(T)` ⇒ `lam = Λ`.
- L278-CORR: the class-field "non-uniqueness" is false, so there is no ℚ-specific (Minkowski) barrier.

## Reductions (this loop)
- **R1 (T1 ≡ T2 for twins) [P].**
  - For a producer with lock `P`, the engine identity gives `M_m[(P−1)F] ∝ 2κβ − a_m`. Here `M_m` is the Abel–Bohr mean at frequency `2 log m` and `a_m` are the coefficients of `F_lam`.
  - For a twin, `a_m` are the coefficients of `F^{1/3}`, which are not constant. So the radial defect means are nonzero, and no step-phase radial argument can be general.
  - Any T1 argument for twins must use that the steps sit at the zeros of `F` itself.
- **R2 (conductor awareness) [P].**
  - Full-pole ℤ/2 locks exist for the datum `(Γ_ℝ, conductor √N, pole 1)` for every integer `N ≥ 2` (under RH): `lam = Λ + Λ_{B_N}/2`, `F = ζ²B_N`, `B_N = 1 + N^{½−s}`.
  - Their step phase `(−1)^{N_B}` is periodic (Poisson lattice), i.e. almost periodic. At conductor 1, a.p. step phases are already excluded (MUST-690).
  - So T1 at conductor 1 concerns only non-a.p. step phases.
- **R3 (step-phase contour identities `I_k`, every k ≥ 1) [P mod Gonek].**
  - For every producer and every `k`: `∫|F_lam|^k e^{iπkN_ν} w = Σ_n b^{(k)}_n A_k(n) w(2πn^{2/k}) + error`, with `b^{(k)}` the coefficients of `F_lam^k`.
  - The stationary phase is `−kπn^{2/k} − kπ/8`. It is non-oscillating for every `n` only at `k = 2` (Lemma C). Otherwise coherent terms come only from resonant `n` (`k = 1`: none, alternating; `k = 3`: `n = 8u³`; `k = 6`: cubes).
  - For twins, `|F_lam| = |Z_F|^{1/3}` and `e^{iπN_ν} = e^{iπN_F/3}`.
- **R4 (sector law for ℤ/3 twins) [P from R3 + MUST-603].**
  - Let `S_j = {t : N_F(t) ≡ j mod 3}` and `A_j = ∫_{S_j}|Z_F|^{2/3} w`.
  - `I_2` gives `A_1 = A_2` and `A_0 − A_1 = R²∫w log t + C₁∫w + o(T)`.
  - MUST-603 forces `∫_{S₁∪S₂}|Z_F|^{1/3} w ≥ c₀∫w`, so `A_1 + A_2 ≥ c₀²∫w`.
  - **Hence `∫|Z_F|^{2/3}w ≥ R²∫w log t + (C₁ + 3c₀²/2)∫w`.** A twin's `F^{1/3}` exceeds its Dirichlet mean square by a positive amount per unit length.
  - A sharp mean-value theorem for producers, `∫|F_lam|²w = R²∫w log t + C₁∫w + o(T)`, would exclude every ℤ/3 twin. This is L224's missing input, now needed with the second-order constant.
