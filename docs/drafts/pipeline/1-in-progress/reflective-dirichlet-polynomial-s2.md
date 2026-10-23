# Self-Dual Reflective Dirichlet-Polynomial Closure in the Guth–Maynard / Chen–Gupta–Li $S_2$ Tower

- **ID:** reflective-dirichlet-polynomial-s2
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** docs/reports/review-2110/argon.md · §1.6 Mechanism 5
- **Statement:** Unconditional formalization of the Four-Part Self-Dual Reflective Dirichlet-Polynomial Closure in the Guth–Maynard / Chen–Gupta–Li $S_2$ Tower (`reflective_dirichlet_polynomial_s2_master_theorem`) in `GaloisForLFunctions.ReflectiveDirichletPolynomialS2`:
  1. **Signed Principal Reflection Factorization & Self-Dual Scale Law (`SelfDualPrincipalReflectionIdentity.lean`):**
     - Proves `sum_fourier_pos_eq_mellin_headPoly_integral` and `sum_fourier_neg_eq_conj_mellin_headPoly_integral`: for any $N > 0$ and $M \in \mathbb{N}$, the positive- and negative-frequency Poisson sums $\sum_{m=1}^M \hat{h}_t(\pm mN)$ factorize exactly inside the Mellin-line integral into the unweighted Dirichlet head polynomial $D_M(\pm t - y) = \sum_{m=1}^M m^{-i(\pm t - y)}$ (`cglGMHeadPoly`) times the stationary-phase integral $K(\pm t - y; \log N, \log(2MN))$.
     - Proves `selfDual_reflection_scale_product` and `selfDual_ceiling_length_bounds`: for $N > 0$ and $M = \lceil |t|^{1+\epsilon} / N \rceil$, the primal-reflected product obeys $|t|^{1+\epsilon} \le N \cdot M < |t|^{1+\epsilon} + N$, and at the self-dual scale $N = |t|^{(1+\epsilon)/2}$, the reflected length satisfies $N \le M < N + 1$.
     - Packages the conjugation symmetry `gmNonzero w N (-τ) = conj (gmNonzero w N τ)` and explicit Lemma 6.2 bound in `gmNonzero_conj_symm_and_lemma62_bound`.
  2. **Exact $q=1$ Cubic Trace $S_2$ Plane-Diagonal Decomposition & Single-Block Reduction (`CubicTraceS2ReflectionReduction.lean`):**
     - Proves `cglTraceS2_modulusOne_eq_diag_add_offDiag`: for any packet of $R$ rows at modulus $q = 1$ with distinct times forming $W$, the $S_2$ component of the Chen–Gupta–Li cubic trace decomposes exactly into the positive diagonal quadratic form $3N^3 \hat{h}_0(0) \sum_{x,y \in W} \|A(x-y)\|^2$ plus the off-diagonal triple sum $3N^3 \sum_{x,y \in W} \sum_{z \in W \setminus \{x\}} A(x-y)A(y-z)\hat{h}_{z-x}(0)$.
     - Proves `cglTraceS2_modulusOne_le_single_dyadic_block`: for any $\epsilon \in (0, 1]$, the $q = 1$ Chen–Gupta–Li cubic trace $S_2$ is bounded by a single dyadic block $2^j \le M \le (2T)^{1+\epsilon}/N + 1$ of the unweighted Heath–Brown pair sum `hbPairSum W (dyadicSegmentBlock M j) 1`.
  3. **Widened $17/30$ Smooth-Tapered Cross-Scale Dispersion & Balanced-Regime Quasi-RH Equivalence (`ShortWindowDispersionAtSeventeenThirtieths.lean`):**
     - Proves `exists_abs_crossScaleFunctional_smooth_add_centredPrimeRow_le_seventeenThirtieths` and `exists_abs_crossScaleFunctional_smooth_add_centredPrimeRow_le_of_range`: couples the Guth–Maynard $30/13$ zero-density / $17/30$ short-interval prime theorem (`tendsto_psi_short_window_div_seventeenThirtieths`, `exists_abs_rowBilinear_centredPrimeRow_le_of_range`) with smooth-tapered higher-order Bernoulli elimination (`abs_crossScaleFunctional_add_le_of_isSmoothTaperedAtScale`), extending unconditional smooth-plus-centred-prime cross-scale dispersion from Huxley's $Q \le P^{12/7-\delta}$ to the full Guth–Maynard range $P^{1+\delta} \le Q \le P^{30/17-\delta}$.
     - Proves `moebius_and_prime_powerWindowSaving_iff_quasiRH`: in the balanced self-dual regime, short-window power saving for the Möbius row (`MoebiusPowerWindowSaving`), short-window power saving for the prime row (`PrimePowerWindowSaving`), and the quasi-Riemann hypothesis (`zetaZeroAbscissa < 1`) are unconditionally three-way equivalent.
  4. **Master Reflective Dirichlet-Polynomial $S_2$ Theorem (`MasterReflectiveDirichletPolynomialS2Theorem.lean`):**
     - Synthesizes all four legs into `reflective_dirichlet_polynomial_s2_master_theorem`.

## Goal
To research, derive, and formalize §1.6 Mechanism 5 of Project Argon (`docs/reports/review-2110/argon.md`), bridging the Guth–Maynard / Chen–Gupta–Li $S_2$ cubic trace and signed principal reflection tower with the widened $17/30$ smooth-tapered cross-scale dispersion and balanced-regime quasi-RH equivalence in its own subfolder `formal/GaloisForLFunctions/ReflectiveDirichletPolynomialS2/`.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem `GaloisForLFunctions.ReflectiveDirichletPolynomialS2.reflective_dirichlet_polynomial_s2_master_theorem`, `lake --old env lean` green, zero axioms/sorrys
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Log
- 2026-10-23 — Created in `1-in-progress`.
