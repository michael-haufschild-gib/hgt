# Short-Interval Crossovers, Hecke-Dilated Welch Bounds, Witt–Euler Curve Twins, Weil-Comb Shift Stability, and Four-Factor Dichotomies

- **ID:** elt-ch-sac-sc-single-quartet-harvest
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/review-2011/obstacles-summary.md` §2.4
- **Statement:** Unconditional analytic, spectral, algebraic, and arithmetic theorems across `ExceptionalLayerTheory`, `CountingHolography`, `SignedArithmeticCorrespondences`, and `SelbergClass` governing `HasSingleOffLineQuartet ρ₀`, `BacklundConverse.FiniteOffLine`, Hecke-dilated integer probes, universal Witt–Euler coordinates and prime-base genus-2 curve twins, additive shift stability of the Weil comb, four-factor log-positivity dichotomies, Bernoulli–Möbius `L²` convergence on `Re s > 1/2`, and composite-supported Dirichlet log-dipoles.

## Goal
Formalize unconditionally in Lean 4 the exact equivalences, cancellations, short-interval crossover laws, Welch lower bounds, universal Witt–Euler coordinate theorems, genus-2 complex-quartet curve twins, Weil-comb shift-stability estimates, and four-factor/Bernoulli–Möbius/dipole results established during the single-quartet investigation (§2.4).

## Gates
- [x] 0 → 1  in-progress: well-posed, unconditional mathematical statements
- [x] 1 → 2  fully-proven: complete paper proofs (`[PROVED HERE]`), zero open dependencies
- [x] 2 → 3  formalized: Lean 4 modules audited via `lake --old env lean` with zero errors/warnings and wired into domain umbrellas

## Formalized Lean Modules & Declarations

1. **`GaloisForLFunctions.ExceptionalLayerTheory.SingleQuartetShortIntervalsAndAnnihilationOperators`**
   (`formal/GaloisForLFunctions/ExceptionalLayerTheory/SingleQuartetShortIntervalsAndAnnihilationOperators.lean`)
   - `OutsideQuartetOnLine`, `outsideQuartetOnLine_of_riemannHypothesis`, `hasSingleOffLineQuartet_iff_outsideQuartetOnLine`, `outsideQuartetOnLine_dichotomy`, `riemannHypothesis_iff_outsideQuartetOnLine_and_mult_zero`, `outsideQuartetOnLine_chebyshevPsi_and_theta_wave`
   - `quartetHalfPeriodScale`, `halfPeriodAnnihilator`, `quartetHalfPeriodScale_lt_two_of_singleQuartet`, `quartetHalfPeriodScale_cpow`, `halfPeriodAnnihilator_re_cpow_eq_zero`, `iterate_halfPeriodAnnihilator_re_cpow_log_pow_eq_zero`, `outsideQuartetOnLine_halfPeriod_chebyshev_cancellation`
   - `norm_cpow_increment_le`, `norm_cpow_increment_sub_linear_le`, `finiteOffLine_short_interval_psi_and_theta`, `finiteOffLine_exists_prime_in_cramer_interval`, `singleQuartet_exists_prime_in_cramer_interval`, `infinite_offLine_of_cramer_prime_gap_failure`
   - `singleQuartetMainWave`, `singleQuartet_short_interval_subcritical_rh_bound`, `singleQuartet_short_interval_supercritical_both_signs`, `singleQuartet_wave_short_interval_L2_crossover`
   - `xi_add_shift_ne_zero_of_singleQuartet`, `riemannZeta_re_eq_zero_iff_abs_im_eq_of_singleQuartet`

2. **`GaloisForLFunctions.CountingHolography.Sections.HeckeDilatedProbeWelchBounds`**
   (`formal/GaloisForLFunctions/CountingHolography/Sections/HeckeDilatedProbeWelchBounds.lean`)
   - `heckeDilateIndex`, `heckeDilateAt`, `integerProbe_heckeDilateAt`, `probePairing_heckeDilateAt_self`, `heckeDilateAt_comp`, `probePairing_heckeDilateAt_mul_left`
   - `disjoint_activeConductors_heckeDilateAt_of_sep`, `disjoint_activeConductors_heckeDilateAt_of_primes`
   - `finite_right_support_heckeDilate_energy`, `exists_heckeDilate_pair_correlation`
   - `singleQuartet_heckeDilate_welch_bound`, `singleQuartet_three_heckeDilates_pair_ge_half`, `four_le_rightZeros_of_three_heckeDilates`

3. **`GaloisForLFunctions.CountingHolography.ThePrimeFiveQuartetEulerTwin`**
   (`formal/GaloisForLFunctions/CountingHolography/ThePrimeFiveQuartetEulerTwin.lean`)
   - `exists_int_necklace_of_integral_hasGhost`
   - `fiveQuartetAlpha0`, `fiveQuartetAlpha2`, `fiveQuartetAlpha_add_and_mul`, `fiveQuartetAlpha_norms`
   - `primeFiveQuartetDatum`, `primeFiveQuartetDatum_alpha`, `primeFiveQuartetDatum_im_ne_zero`, `primeFiveQuartetDatum_not_unitary`, `primeFiveQuartetDatum_hOnePoly`
   - `fiveQuartetTrace`, `primeFiveQuartetDatum_powerSum_eq_trace`, `fiveQuartetPointCount`, `primeFiveQuartetDatum_pointCount_eq`, `primeFiveQuartetDatum_zetaSeries_integral`, `primeFiveQuartet_complete_twin`

4. **`GaloisForLFunctions.SignedArithmeticCorrespondences.AdditiveShiftStabilityOfTheWeilComb`**
   (`formal/GaloisForLFunctions/SignedArithmeticCorrespondences/AdditiveShiftStabilityOfTheWeilComb.lean`)
   - `jetKernel_add_sub_jetKernel`
   - `addShiftSet`, `addShiftProfile`, `nonContactCombForm`, `combForm_eq_nonContactCombForm_sub_contacts`, `degTwo_addShift`
   - `diagRealBudget_addShift_sub_le`, `poleProduct_addShift_sub_le`, `nonContactCombForm_addShift_sub_le`
   - `eq_of_add_eq_mul_add`, `not_dvd_add_one_of_dvd_of_le`, `contact_add_one_eq_zero_of_le`, `contact_prime_not_dvd_dvd`

5. **`GaloisForLFunctions.SelbergClass.FourFactorPositivityAndBernoulliMoebiusConvergence`**
   (`formal/GaloisForLFunctions/SelbergClass/FourFactorPositivityAndBernoulliMoebiusConvergence.lean`)
   - `fourFactorLogWeight`, `fourFactorLogWeight_ofReal_eq_four_cos_sq`, `fourFactorLogWeight_ofReal_nonneg`, `twoSidedEdit_fourFactor_vanishes_on_real_axis`, `positiveFiniteEuler_fourFactor_neg_at_prime_sq`, `positiveRootEuler_fourFactor_neg_at_prime`
   - `bernoulliMoebiusMode`, `bernoulliMoebiusMode_prime`, `norm_bernoulliMoebiusMode_le`, `summable_sq_norm_bernoulliMoebiusMode`
   - `dipoleLogCoeff`, `dipoleLogCoeff_uniform_bound`, `exists_exp_dipoleLogCoeff_continuation`

## Paper Proofs (`[PROVED HERE]`)

### 1. Unified Multiplicity Bifurcation, Half-Period Annihilation, Short-Interval Crossovers, and Shifted `ξ`-Sums
Let $\rho_0 \in \mathbb{C}$ satisfy $\frac12 < \operatorname{Re}\rho_0 < 1$, and define `OutsideQuartetOnLine ρ₀` by requiring $\operatorname{Re}\rho = \frac12$ for every strip zero $\rho$ of $\zeta$ outside $Q(\rho_0) = \{\rho_0, \bar\rho_0, 1-\rho_0, 1-\bar\rho_0\}$.
- **Multiplicity bifurcation:** Let $m = \operatorname{ord}_{\rho_0}\xi \in \mathbb{N}$. Then `OutsideQuartetOnLine ρ₀` splits into `(RiemannHypothesis ∧ m = 0) ∨ (HasSingleOffLineQuartet ρ₀ ∧ 1 ≤ m)`, `RiemannHypothesis ↔ OutsideQuartetOnLine ρ₀ ∧ m = 0`, and uniformly across $m \ge 0$,
  $$\psi(x) - x = -2m\operatorname{Re}\!\left(\frac{x^{\rho_0}}{\rho_0}\right) + O(\sqrt{x}\log^2 x), \qquad \theta(x) - x = -2m\operatorname{Re}\!\left(\frac{x^{\rho_0}}{\rho_0}\right) + O(\sqrt{x}\log^2 x) \quad (x \ge 16).$$
- **Two-point half-period annihilation:** For $\operatorname{Im}\rho_0 \neq 0$, $\lambda_0 = \exp(\pi/|\operatorname{Im}\rho_0|)$ satisfies $\lambda_0^{\rho_0} = -\lambda_0^{\operatorname{Re}\rho_0}$ (and $1 < \lambda_0 < 2$ under `HasSingleOffLineQuartet ρ₀` since $|\operatorname{Im}\rho_0| > 67$). The operator $(\mathcal{D}_{\rho_0}F)(x) = F(\lambda_0 x) + \lambda_0^{\operatorname{Re}\rho_0}F(x)$ annihilates $x \mapsto \operatorname{Re}(c x^{\rho_0})$, its $m$-fold iterate $\mathcal{D}_{\rho_0}^{[m]}$ annihilates $x \mapsto \operatorname{Re}(c x^{\rho_0}(\log x)^k)$ for all $k < m$, and under `OutsideQuartetOnLine ρ₀` both $\mathcal{D}_{\rho_0}(\psi(y)-y)(x)$ and $\mathcal{D}_{\rho_0}(\theta(y)-y)(x)$ are $O(\sqrt{x}\log^2 x)$.
- **Cramér-scale prime gaps under `FiniteOffLine`:** For $\rho \neq 0$ with $\operatorname{Re}\rho \le 1$, $x > 0$, $h \ge 0$, the convex mean-value theorem gives $\left\|\frac{(x+h)^\rho - x^\rho}{\rho}\right\| \le h x^{\operatorname{Re}\rho - 1}$, and for $\operatorname{Re}\rho \le 2$, $\left\|\frac{(x+h)^\rho - x^\rho}{\rho} - h x^{\rho - 1}\right\| \le \|\rho - 1\| h^2 x^{\operatorname{Re}\rho - 2}$. Under `BacklundConverse.FiniteOffLine`, let $\beta_* = \max(\frac12, \max_{\rho\text{ off-line}}\operatorname{Re}\rho) < 1$; then $|\theta(x+h) - \theta(x) - h| \le K\sqrt{x}\log^2 x + K h x^{\beta_* - 1}$ for $x \ge 16$, $0 \le h \le x$. Taking $h = 2(K+1)\sqrt{x}\log^2 x$ yields $\theta(x+h) - \theta(x) \ge \sqrt{x}\log^2 x > 0$ for large $x$, hence a prime in $(x, x + C\sqrt{x}\log^2 x]$. Contrapositively, failure of Cramér-scale prime gaps forces infinitely many off-line zeros.
- **Pointwise ($\frac32 - \operatorname{Re}\rho_0$) and $L^2$ ($2 - 2\operatorname{Re}\rho_0$) crossovers:** Under `HasSingleOffLineQuartet ρ₀`, for $0 < \alpha \le \frac32 - \operatorname{Re}\rho_0$, $x^{\alpha + \operatorname{Re}\rho_0 - 1} \le \sqrt{x}$, so $\psi(x+x^\alpha) - \psi(x) - x^\alpha$ and $\theta(x+x^\alpha) - \theta(x) - x^\alpha$ remain $O(\sqrt{x}\log^2 x)$. For $\frac32 - \operatorname{Re}\rho_0 < \alpha < 1$, $|\operatorname{Im}\rho_0|\log(3/2) > 67/3 > 2\pi$ produces points $x_\pm \in [X, \frac32 X]$ where $\cos(\operatorname{Im}\rho_0 \log x_\pm) = \mp 1$, forcing both increments to exceed $+m X^{\alpha + \operatorname{Re}\rho_0 - 1}$ at $x_+$ and fall below $-m X^{\alpha + \operatorname{Re}\rho_0 - 1}$ at $x_-$. Meanwhile, $\int_X^{2X} (W_{\rho_0}(x+h) - W_{\rho_0}(x))^2\,dx \asymp h^2 X^{2\operatorname{Re}\rho_0 - 1}$ for $0 \le h \le \eta_0 X$, crossing $X h \log^2 X$ at $\alpha = 2 - 2\operatorname{Re}\rho_0 < \frac32 - \operatorname{Re}\rho_0 < 1$.
- **Shifted $\xi$-sums and vertical-line uniqueness:** Under `HasSingleOffLineQuartet ρ₀`, $\xi(s) + \xi(s - 2h) = 2\operatorname{cosProducer}_h((s - (\frac12 + h))(-i)) \neq 0$ whenever $h \ge \operatorname{Re}\rho_0 - \frac12$ and $\operatorname{Re} s \neq \frac12 + h$; and $\zeta(\operatorname{Re}\rho_0 + it) = 0 \iff |t| = |\operatorname{Im}\rho_0|$.

### 2. Hecke-Dilated Integer-Probe Isometry and Welch Correlation Floors
For a probe $a_0 : \operatorname{Fin} N_0 \to \mathbb{Z}$, `heckeDilateAt hd hM a₀` embeds atom $i+1$ to $d(i+1)$ inside $\operatorname{Fin} M$.
- **Exact self-pairing isometry and joint scale invariance:** Because `atomGram` depends only on atom ratios $(i+1)/(j+1)$, $\langle T_d a_0, T_d a_0\rangle = \operatorname{integerProbe}_{N_0}(a_0)$ and $\langle T_{kd_1} a, T_{kd_2} b\rangle_{kM} = \langle T_{d_1} a, T_{d_2} b\rangle_M$. Active conductors are disjoint whenever $d_1 N_0 < d_2$ or whenever $d_1 \neq d_2$ are primes exceeding $N_0$.
- **Welch floor and converse exclusion:** When $\#\operatorname{rightZeros} \le r$ and $Q(a_0) < 0$, the Hermitian Gram matrix $H$ of $m$ Hecke dilates has $\operatorname{hermNegIndex} H \le r$, $\operatorname{tr} H = m Q(a_0) \le 0$, and $\operatorname{tr}(H^2) = m Q(a_0)^2 + \sum_{i \neq j} \langle T_{d_i} a_0, T_{d_j} a_0\rangle^2$, giving $m(m-r)Q(a_0)^2 \le r \sum_{i \neq j} \langle T_{d_i} a_0, T_{d_j} a_0\rangle^2$. Under `HasSingleOffLineQuartet ρ₀` ($r = 2$) at $m = 3$, some pair satisfies $|\langle T_{d_i} a_0, T_{d_j} a_0\rangle| \ge \frac12 |Q(a_0)|$; contrapositively, $2\sum_{i \neq j} \langle T_{d_i} a_0, T_{d_j} a_0\rangle^2 < 3 Q(a_0)^2$ forces $(4 : \mathbb{N}_\infty) \le \#\operatorname{rightZeros}$ and excludes `HasSingleOffLineQuartet` globally.

### 3. Universal Witt–Euler Coordinates and the Prime-Base $q = 5$ Quartet Curve Twin
- **Universal Witt–Euler peeling:** Every formal power series $Z \in 1 + X\mathbb{Z}\llbracket X\rrbracket$ has logarithmic ghost sequence in `ghostRing` ($N_k = \sum_{d \mid k} d\pi_d$ with $\pi_d \in \mathbb{Z}$ and $k\pi_k = \sum_{d \mid k}\mu(k/d)N_d$). Inductively peeling $(1 - X^d)^{\pi_d}$ with $\pi_d = \operatorname{coeff}_d(R_{d-1}) \in \mathbb{Z}$ kills coefficients in degrees $1 \le m \le d$ and matches ghost components degree by degree.
- **Prime-base $q = 5$ genus-2 non-real quartet curve twin:** $P_4(X) = 1 - 2X + 12X^2 - 10X^3 + 25X^4 = (1 - (1+i)X + 5X^2)(1 - (1-i)X + 5X^2)$ defines a genus-2 `CurveDatum (Fin 4)` over prime base $q = 5$ with integral zeta series, lone non-real off-circle quartet ($\sqrt{5} < \|\alpha_0\| < 3 < 5$), strictly positive closed-orbit counts $\pi_d \ge 1$ for all $d \ge 1$ ($\pi_1 = 4, \pi_2 = 21, \pi_3 = 52$), genus-2 Weil count laws at $n = 1, 2, 3$ (with exact boundary equality $a_2^2 = 400 = 16 \cdot 5^2$), and failure on the full tower.

### 4. Additive Shift Stability of the Weil Comb vs Prime-Contact Destruction
For a finite support $S \subseteq [N, \infty)$ ($N \ge 1$) and additive translation $n \mapsto n + h$:
- **Singular-jet cancellation and $O((h/N + |S|h/N^2)\sum c_n^2)$ stability:** For $m + n > 0$, $\operatorname{jetKernel}(m+h, n+h) - \operatorname{jetKernel}(m, n) = -\frac{h}{(m+n)(m+n+2h)}$; `degTwo` is strictly shift-invariant, $|\operatorname{diagRealBudget}(c_{+h}) - \operatorname{diagRealBudget}(c)| \le (\frac{h}{N} + \frac{|S|h}{4N^2})\sum_{n \in S} c_n^2$, and $|\operatorname{nonContactCombForm}(c_{+h}) - \operatorname{nonContactCombForm}(c)| \le (\frac{h}{N} + \frac{9|S|h}{4N^2})\sum_{n \in S} c_n^2$.
- **Prime-contact destruction and ray rigidity:** Each pair $(m, n)$ meets any ratio $r \ge 2$ at at most one shift $h \in \mathbb{N}$; for $Q \le m < n \le Qm$, $\operatorname{contact}(m, n) \neq 0 \implies \operatorname{contact}(m+1, n+1) = 0$; and for any prime $p$, $p \nmid m$, $p \mid i$ ($i > 0$), $\operatorname{contact}(m, i) = \log p$ if $m = \operatorname{ordCompl}_p(i)$ and $0$ otherwise.

### 5. Four-Factor Log-Positivity Dichotomy, Bernoulli–Möbius `L²` Convergence, and Composite Dipoles
- **Four-factor dichotomy:** For $b : \mathbb{N} \to \mathbb{R}$ and $n \ge 1$, $\operatorname{Re}(2b(n) + b(n)(n^{-i\gamma} + n^{i\gamma})) = 4\cos^2(\frac{\gamma\log n}{2})b(n)$. On two-sided prime edits $B = \operatorname{editSystem}(\operatorname{edit}\rho_0)$ ($\frac12 < \operatorname{Re}\rho_0 < \frac{14}{15}$), every prime-power log-multiplicity $1 + \operatorname{edit}\rho_0(n) \in \{0, 1, 2\}$ is nonnegative, yet the holomorphic continuation of $((s-1)\zeta_B(s))^2((s+i\gamma_0-1)\zeta_B(s+i\gamma_0))((s-i\gamma_0-1)\zeta_B(s-i\gamma_0))$ ($\gamma_0 = \operatorname{Im}\rho_0$) to $\{\operatorname{Re} s > \frac12\}$ vanishes on the real axis at $s = \operatorname{Re}\rho_0$. Conversely, on single-prime quadratic Euler modifications, `PositiveFiniteEuler` with roots $-r, -p/r$ ($r > 0$) at $\gamma_0 = \pi/\log p$ has $p^2$ weight $2(1 - r^2 - (p/r)^2) \le 2(1 - 2p) \le -6$, and positive-root factors with roots $p^\sigma, p^{1-\sigma}$ at $\gamma_0 = 2\pi/\log p$ have $p^1$ weight $4(1 - p^\sigma - p^{1-\sigma}) \le 4(1 - 2\sqrt{p}) < 0$.
- **Bernoulli–Möbius `L²` convergence on $\operatorname{Re} s > \frac12$:** For $c_m(s) = m^{-s}\sum_{d \mid m}\mu(d)d^{s-2}$ ($m \ge 1$), $\|c_m(s)\| \le d(m) m^{-\min(\operatorname{Re} s, 2)}$, giving $\sum_{m=0}^\infty \|c_m(s)\|^2 < \infty$ across $\{\operatorname{Re} s > \frac12\}$ via $d(m) \le C m^\varepsilon$.
- **Composite-supported Dirichlet log-dipole:** For $\operatorname{Re}\rho_1 < \frac12 < \operatorname{Re}\rho_0 < 1$, $L_{\rho_0,\rho_1}(s) = \sum_{k=2}^\infty \frac{k^{\rho_1-1} - k^{\rho_0-1} + k^{\bar\rho_1-1} - k^{\bar\rho_0-1}}{\log k} k^{-s}$ is uniformly bounded on $\operatorname{Re} s \ge \operatorname{Re}\rho_0 + \varepsilon$, while $\exp(L_{\rho_0,\rho_1}(s))$ continues holomorphically to $\{\operatorname{Re} s > \operatorname{Re}\rho_1\}$ with exact zero set $\{\rho_0, \bar\rho_0\}$.

## Log
- 2026-11-20 — paper proofs written in `2-fully-proven`; all five Lean 4 modules audited via `lake --old env lean` (exit code 0, zero warnings) and wired into `ExceptionalLayerTheory.lean`, `CountingHolography.lean`, `SignedArithmeticCorrespondences.lean`, and `SelbergClass.lean`; promoted to `3-formalized`.
