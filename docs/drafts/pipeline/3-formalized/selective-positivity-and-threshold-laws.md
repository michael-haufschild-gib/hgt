# Selective Positivity and Square-Root Threshold Laws

- **ID:** selective-positivity-and-threshold-laws
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** docs/reports/review-2610/questions.md (Questions 1–6)
- **Statement:** Complete, unconditional paper and Lean 4 resolution (including positive survivors and corollaries) of the six frontier questions on coalescent prime-pair dispersion, gauge-selective full-sector window positivity past `½ log 2`, the Möbius escaped-pairing boundary law, real-valued Serre-dual scaling cohomology, subquadratic Jacobi–Hurwitz biarithmetic heights, two-prime Catalan selectivity on `[-23/40, 23/40]`, and lattice-to-continuum prime-tower transfer.

## Goal

Resolve all six frontier questions unconditionally with complete positive/negative classifications, constructive separating witnesses, exact structural equivalences to `zetaZeroAbscissa`, `zetaZeroWidth`, and `RiemannHypothesis`, and mandatory positive salvage theorems for every obstructed mechanism.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorems in `GaloisForLFunctions.SelectivePositivityAndThresholdLaws` (6 modules + umbrella wired into `MainTheorems.lean`), `lake --old env lean` green on all 6 modules, standard axioms `[propext, Classical.choice, Quot.sound]` PASS

## Formalized Modules & Exact Lean Declarations

All declarations live in namespace `GaloisForLFunctions.SelectivePositivityAndThresholdLaws`:

1. **`LiouvilleOddWindowRefutationAndSelectiveFullPositivity.lean` (Questions 2a & 2b):**
   - `exists_odd_smooth_threeHundredSixtyTwoThousandths_zeta_pos_liouville_neg`
   - `exists_odd_smooth_threeHundredSixtyTwoThousandths_flippedTwo_neg`
   - `not_forall_odd_threeHundredSixtyTwoThousandths_re_weilFullFunctional_liouvilleTwist_nonneg`
   - `fullZeroForm_ge_of_even_support_le_threeHundredSixtyTwoThousandths`
   - `fullZeroForm_ge_of_support_le_threeHundredSixtyTwoThousandths`
   - `zetaZeroConfig_re_W_ge_of_aperture_le_threeHundredSixtyTwoThousandths`
   - `re_windowedW_zetaZeroConfig_nonneg_of_threeHundredSixtyTwoThousandths`
   - `one_div_5000_le_ccmRestrictedWeilGroundEnergy_threeHundredSixtyTwoThousandths`
   - `lt_of_ccmRestrictedWeilGroundEnergy_nonpos_threeHundredSixtyTwoThousandths`
   - `re_weilFullFunctional_ge_of_full_window_of_atom_two_eq`
   - `exists_even_smooth_threeHundredSixtyTwoThousandths_zeta_pos_shiftedPair_neg`
   - `threeHundredSixtyTwoThousandths_selectivity_battery`
2. **`MoebiusEscapedPairingBoundaryLaw.lean` (Question 2c):**
   - `escapedPairing_moebius_succ_sub_self`
   - `half_le_max_abs_escapedPairing_moebius`
   - `not_uniform_all_multipliers_escapedPairing_rpow`
   - `growingEndpointEscapedMoebiusLaw_tfae`
   - `riemannHypothesis_iff_growingEndpointEscapedMoebiusLaw_half`
   - `riemannHypothesis_iff_forall_lt_half_growingEndpointEscapedMoebiusLaw`
   - `not_dyadic_escapedPairing_rpow_of_half_lt`
3. **`SerreDualScalingCohomologyAndLargeSieveSections.lean` (Question 3):**
   - `thetaBox_riemannRoch_and_serreDuality`
   - `thetaBox_strict_selectivity_shiftedPair`
   - `surfaceBox_serreDuality`
   - `curve_frobMass_cohomology_calibration`
   - `goldenDatum_frobMass_cohomology_refutes_riemannRoch`
   - `sections_beyond_largeSieve_iff_zetaZeroWidth_le`
   - `serreDual_section_growth_iff_riemannHypothesis`
4. **`JacobiHurwitzTorsionInflationAndShortCycleHeights.lean` (Question 4):**
   - `abs_jacobiHurwitzHeight_sub_quad_le`
   - `hodgeIndex_of_asymptoticRiemannInequality`
   - `jacobiHurwitzHeight_dichotomy`
   - `jacobiHurwitz_largeSieve_inflation_ge_half_abs`
   - `jacobiHurwitzQuad_ge_quarter_of_abundant`
   - `goldenDatum_no_asymptotic_subquadratic_height`
   - `shortCycle_subquadratic_height_exists_primeTwo`
   - `riemannHypothesis_iff_exists_asymptotic_subquadratic_height`
5. **`ParityLobeObstructionAndEscapeLaplaceSplit.lean` (Questions 1 & 5A):**
   - `ramanujanStabilizerPacket_eq_sum_dvd_indicator`
   - `tendsto_ramanujanStabilizerPacket`
   - `multiModulus_ramanujan_primeCoalSum_split`
   - `selbergParity_pair_gap_on_primes`
   - `parityBlind_dispersion_diverges_above_threshold`
   - `parityBlind_refutes_quadratic_and_fourThirds_budgets`
   - `oddEvenShift_singleProfile_certifies_proportion`
   - `coalescent_surplus_battery_laws`
   - `escapeLaplaceSymbol_eq_invZeta_form`
   - `escapeLaplaceSymbol_pole_and_visibility_laws`
6. **`TwoPrimeCatalanSeparationAndContinuumTowerObstruction.lean` (Questions 5B & 6):**
   - `catalan_finite_gauge_separation`
   - `bddBelow_liouvilleWindowRayleighSet`
   - `exists_smooth_odd_twentyThreeFortieths_zeta_pos_liouville_neg`
   - `liouvilleWindowGroundEigenvalue_twentyThreeFortieths_lt_neg_threeTenths`
   - `towerOddPrimeSide_eq_zero_of_lt`
   - `eventually_sum_continuumPrimeTower_edgeTowerBump_le`
   - `not_continuumPrimeTower_subexponential_dyadicH1`
   - `continuum_poleNeutralized_width_equivalence`

## Complete Dependency-Closed Proofs

### 1. Square-Root Boundary Law for `escapedPairing` (Question 2c) — `[PROVED HERE]`

For the signed Möbius source $x_j = \mu(j)/\sqrt{j}$ and flat test $y_j = 1/\sqrt{j}$ on $[1, N]$ (`b ≤ N`),
$$
\operatorname{escapedPairing}(N, a, b, \mu/\sqrt{\cdot}, 1/\sqrt{\cdot})
  = \sum_{j \in (\lfloor(N-b)/a\rfloor, N]} \frac{\mu(j)}{j}.
$$

1. **Unconditional Refutation of Unrestricted-Multiplier Uniformity (`not_uniform_all_multipliers_escapedPairing_rpow`):**
   At `b = 0` and `N ≥ 1`, taking adjacent multipliers `a = N` and `a = N + 1` isolates the unit cell $\mu(1)/1 = 1$, forcing $\operatorname{escapedPairing}(N, N+1, 0) - \operatorname{escapedPairing}(N, N, 0) = 1$ and $\max(|\operatorname{escapedPairing}(N, N, 0)|, |\operatorname{escapedPairing}(N, N+1, 0)|) \ge \tfrac{1}{2}$ for all $N \ge 1$. No uniform $C N^{-\theta}$ bound ($\theta > 0$) holds across unrestricted multipliers $a$.
2. **Exact Quasi-RH Equivalence on the Growing-Endpoint Regime $M = \lfloor(N-b)/a\rfloor \ge 1$ (`growingEndpointEscapedMoebiusLaw_tfae`):**
   For any $\theta \in (0, 1/2]$, uniform saving $O_\varepsilon(((N-b)/a)^{-\theta+\varepsilon})$ across all $(a, b)$ with $1 \le (N-b)/a$, dyadic saving at $(a, b) = (2, 0)$, and `zetaZeroAbscissa ≤ 1 - θ` are unconditionally equivalent via discrete Abel summation and Mellin inversion. At $\theta = 1/2$ (and across $\forall \theta \in (0, 1/2)$), this is unconditionally equivalent to `RiemannHypothesis` (`riemannHypothesis_iff_growingEndpointEscapedMoebiusLaw_half`, `riemannHypothesis_iff_forall_lt_half_growingEndpointEscapedMoebiusLaw`).
3. **Unconditional Impossibility Beyond $\theta = 1/2$ (`not_dyadic_escapedPairing_rpow_of_half_lt`):**
   Even at $(a, b) = (2, 0)$, any $O(N^{-\theta})$ bound with $\theta > 1/2$ forces $M(x) = O(x^{1-\theta'})$ ($\theta' = \min(\theta, 3/4) > 1/2$), contradicting `1/2 ≤ zetaZeroAbscissa`.

### 2. Two-Sided Selective Weil Positivity Past `½ log 2` on `[-181/500, 181/500]` (Questions 2a & 2b) — `[PROVED HERE]`

Crossing $\tfrac{1}{2}\log 2 \approx 0.34657$ into $[-181/500, 181/500]$ ($2 \cdot 181/500 = 0.724 \in (\log 2, \log 3)$) exposes only the single prime atom $n = 2$:

1. **Refutation of the Liouville-Twisted Odd Window (`w(2) = -log 2`):**
   Convolving a balanced nine-knot odd clamp spline supported in $[-18099/50000, 18099/50000]$ with a symmetric $C^\infty$ mollifier produces an explicit odd $F \in C^2_c([-181/500, 181/500])$ with $\int F^2 > 0$ satisfying $\tfrac{1}{1000}\int F^2 \le \operatorname{Re} W_\zeta(F \star \tilde{F})$ while $\operatorname{Re} W_{\lambda\Lambda}(F \star \tilde{F}) = \operatorname{Re} W_{\mathrm{flippedTwo}}(F \star \tilde{F}) < -\tfrac{1}{1000}\int F^2 < 0$ (`exists_odd_smooth_threeHundredSixtyTwoThousandths_zeta_pos_liouville_neg`).
2. **Coercive Full-Sector Positivity (`w(2) = +log 2`):**
   On the even sector, combining the Lorentz pole square $2\pi(\int F \cosh(x/2)\,dx)^2$ with a certified 32-piece degree-8 rational upper envelope of $\tfrac{577}{800} - (\gamma(r) - \sqrt{2}\log 2\cos(r\log 2))$ on $[0, 69/2]$, tail monotonicity for $r \ge 69/2$, and a $23 \times 23$ even Legendre $LDL^\top$ + Gershgorin factorization proves `fullZeroForm F ≥ (1/5000) ∫ F²` (`fullZeroForm_ge_of_even_support_le_threeHundredSixtyTwoThousandths`). Combining with the Schur-lending odd certificate (`≥ (1/1000) ∫ F²`) establishes $\operatorname{Re} W_w(f \star \tilde{f}) \ge \tfrac{1}{5000}\int \|f\|^2$ for all complex $f \in C^2_c([-181/500, 181/500])$ whenever $w(2) = \log 2$ (`re_weilFullFunctional_ge_of_full_window_of_atom_two_eq`) and `1/5000 ≤ ccmRestrictedWeilGroundEnergy A` for $A \le 181/500$.
3. **Non-Tempered Even Selectivity (`w(2) = (2^a + 2^{-a}) log 2`):**
   An even two-bump smooth witness localized near $\pm \tfrac{1}{2}\log 2$ inside $[-181/500, 181/500]$ has positive autocorrelation at $\log 2$ and therefore drives $\operatorname{Re} W_{\Lambda_a}(F \star \tilde{F}) < -\tfrac{1}{5000}\int F^2 < 0$ for non-zero shift $a \ne 0$ (`exists_even_smooth_threeHundredSixtyTwoThousandths_zeta_pos_shiftedPair_neg`, `threeHundredSixtyTwoThousandths_selectivity_battery`).

### 3. Serre-Dual Real-Valued Scaling Cohomology & Large-Sieve Sections (Question 3) — `[PROVED HERE]`

1. **Selective Theta Log-Volumes (`thetaBox_riemannRoch_and_serreDuality`, `thetaBox_strict_selectivity_shiftedPair`):**
   Defining `thetaBoxH0 w s` and `thetaBoxH1 w s` via Jacobi theta log-volumes at weighted prime-node displacements gives strictly positive real invariants defined independently of the sign of the Weil form, satisfying Poisson Serre duality $d \mapsto -d$, exact Riemann–Roch `thetaBoxH0 w s - thetaBoxH1 w s = (e^s + s - 1) - ∑_{k ≤ e^s} w(k)`, and strict selectivity separating $\Lambda$ from `shiftedPairVonMangoldt a` ($a \ne 0$) for every $s \ge \log 2$.
2. **Polar-Surface Cohomology Calibration (`surfaceBox_serreDuality`, `curve_frobMass_cohomology_calibration`, `goldenDatum_frobMass_cohomology_refutes_riemannRoch`):**
   `surfaceBoxH0` and `surfaceBoxH1` satisfy `h¹(D) = h⁰(K - D)`, reproduce Weil curve Riemann–Roch with quadratic nef growth, and refute Riemann–Roch on the positive self-intersection cone of `goldenDatum`.
3. **Sub-Large-Sieve Section Growth (`sections_beyond_largeSieve_iff_zetaZeroWidth_le`, `serreDual_section_growth_iff_riemannHypothesis`):**
   Paying the odd Chebyshev defect by a sub-large-sieve Sobolev budget $C e^{2\beta r}(\|f\|_2^2 + \|f'\|_2^2)$ ($\forall \beta > \sigma$) is unconditionally equivalent to `zetaZeroWidth ≤ σ`; globally on `scalingSurface`, Serre-dual asymptotic Riemann–Roch with subquadratic degree-zero growth is equivalent to `RiemannHypothesis`.

### 4. Torsion-Weighted Jacobi–Hurwitz Inflation vs. Short-Cycle Heights (Question 4) — `[PROVED HERE]`

1. **Tate-Limit Quadratic Decomposition & Dichotomy (`abs_jacobiHurwitzHeight_sub_quad_le`, `jacobiHurwitzHeight_dichotomy`):**
   Every torsion-weighted Jacobi–Hurwitz packet $h_P(x)$ lies within a uniform constant $B_P$ of its homogeneous quadratic form $q_P(x) = \sum_i w_i \pi J_i(x)^2 / t_i \ge 0$, so $P$ either vanishes identically on $\ker(\cdot A)$ (forcing $|h_P(z)| \le B_P$ and reducing any asymptotic Riemann inequality to `S.HodgeIndex`) or inflates as $q_P(z) n^2 - B_P$.
2. **Converse Large-Sieve Inflation (`jacobiHurwitz_largeSieve_inflation_ge_half_abs`, `jacobiHurwitzQuad_ge_quarter_of_abundant`, `goldenDatum_no_asymptotic_subquadratic_height`):**
   Any packet satisfying the unsigned Cauchy–Schwarz / additive-large-sieve majorant $\tfrac{1}{2}|x \cdot (x - \kappa)| - o(n^2)$ inflates on every degree-zero cycle with exact coefficient $q_P(z) \ge \tfrac{1}{2}|z \cdot z|$; on abundant classes even the signed asymptotic Riemann inequality forces $q_P(z) \ge \tfrac{1}{4}|z \cdot z| > 0$.
3. **Short-Cycle Existence & Global Equivalence (`shortCycle_subquadratic_height_exists_primeTwo`, `riemannHypothesis_iff_exists_asymptotic_subquadratic_height`):**
   On `scalingSubsurface (primitiveSmoothRealTestsAt r)` for $r \le \tfrac{1}{2}(\log 2 + 1/50)$ (including $r = 3/10$), `optimalEffectivity` gives an unconditional nonnegative height with exact `RiemannInequality` and identical vanishing on degree-zero rays; globally on `scalingSurface`, existence of a bounded-below asymptotic subquadratic height is unconditionally equivalent to `RiemannHypothesis` and to two-window Weil positivity on $[-3/10, 3/10]$.

### 5. Parity–Lobe Dispersion Obstruction & Escape Laplace Split (Questions 1 & 5A) — `[PROVED HERE]`

1. **Multi-Modulus Ramanujan–Stabilizer Split (`multiModulus_ramanujan_primeCoalSum_split`, `tendsto_ramanujanStabilizerPacket`):**
   Weighting normalized level-$d$ Dirichlet-character averages of `twistedPrimeCoalSum` by `stabilizerDivisorWeight Q d` across $1 \le d \le Q$ ($2Q\theta_0 < 1$) reconstructs the `ramanujanStabilizerPacket Q |n - m|`-weighted prime-pair sum (converging to `hardyLittlewoodSingularSeries |n - m|` as $Q \to \infty$) plus a residue discrepancy of zero character mean at every modulus $q \le Q$.
2. **Parity–Lobe Divergence (`selbergParity_pair_gap_on_primes`, `parityBlind_dispersion_diverges_above_threshold`, `parityBlind_refutes_quadratic_and_fourThirds_budgets`):**
   Selberg's nonnegative weights $\Lambda \pm \lambda\Lambda$ average to $\Lambda$ with pure-prime pair correlations $0$ vs. $4\log p \log p'$. Any parity-blind dispersion bracket $|C(r) - C_0(r)| \le \kappa S(r)$ ($\kappa > 0, S(r) \ge s_{\min} > 0$) accumulates at least $(\kappa s_{\min} K_1/2)\widehat{\Omega}_c(0)$ on the positive inner cosine lobe, diverging as $T^{1+\delta}/\log^2 T \gg N(T, 2T)$ for every $\lambda = 1 + \delta > 1$ and refuting both $B\delta^2/(1+\delta)^2$ and the $\lambda = 4/3$ budget $5/36$. Conversely, bounding `oddEvenShiftPrimeCoalescentSurplus` or `PrimeCoalescentSurplusAtMost β` ($\beta < 5/36$, $\beta \le 1/18$) unconditionally certifies critical-line proportions $> 2/3$ and $\ge 3/4$ (`oddEvenShift_singleProfile_certifies_proportion`, `coalescent_surplus_battery_laws`).
3. **Escape Laplace Split (`escapeLaplaceSymbol_eq_invZeta_form`, `escapeLaplaceSymbol_pole_and_visibility_laws`):**
   On the damping strip, the receiver symbol equals $G_\varepsilon(s) = \zeta(s)(\zeta(s+\varepsilon)^{-1} - \operatorname{Re}\zeta(1+\varepsilon)^{-1})/s$, splits at every simple zero $\rho$ into the translated simple pole $(\zeta(\rho-\varepsilon)/(\zeta'(\rho)(\rho-\varepsilon)))/(s - (\rho-\varepsilon))$ plus a bounded remainder, and positive visible gauge mass on every escape state across $0 < \varepsilon < 1/2$ is unconditionally equivalent to `RiemannHypothesis`.

### 6. Two-Prime Catalan Separation on `[-23/40, 23/40]` & Continuum Prime-Tower Obstruction (Questions 5B & 6) — `[PROVED HERE]`

1. **Archimedean-Free Catalan `{2, 3, 4}` Separation & Ground Eigenvalue (`catalan_finite_gauge_separation`, `bddBelow_liouvilleWindowRayleighSet`, `liouvilleWindowGroundEigenvalue_twentyThreeFortieths_lt_neg_threeTenths`):**
   Because $3 + 1 = 4 = 2^2$ has even $\Omega(4) = 2$ while $\Omega(2) = 1$ is odd, `catalanSuccessorSquareForm w = w 2 * w (3 + 1)` equals $+8^\sigma(\log 2)^2 > 0$ on every scale twist $n^\sigma\Lambda(n)$ ($\sigma \in \mathbb{R}$) and $-(\log 2)^2 < 0$ on $\lambda\Lambda$, while `catalanKroneckerTwistDefect` vanishes on ordinate twists $\cos(\gamma_0\log n)\Lambda(n)$ at $\gamma = \gamma_0$ and obeys $\ge \tfrac{1}{5000}e^{-2|\gamma|}$ on $\lambda\Lambda$ for all $\gamma \in \mathbb{R}$. On $[-23/40, 23/40]$, `liouvilleWindowRayleighSet (23/40)` is bounded below and mollifying $u^3((27/50)^2 - u^2)\mathbf{1}_{[-27/50,27/50]}(u)$ produces a smooth odd witness with $\operatorname{Re} W_\zeta > \tfrac{1}{25}\int F^2 > 0$ and $\operatorname{Re} W_{\lambda\Lambda} < -\tfrac{3}{10}\int F^2 < 0$, proving `liouvilleWindowGroundEigenvalue (23/40) < -(3/10)`.
2. **Lattice-to-Continuum Prime-Tower Obstruction & Pole-Neutralized Width Law (`towerOddPrimeSide_eq_zero_of_lt`, `not_continuumPrimeTower_subexponential_dyadicH1`, `continuum_poleNeutralized_width_equivalence`):**
   On the integer lattice $[1, X]$, every prime $p > X$ has `towerOddPrimeSide q X p K = 0` identically. On the continuum $[0, A]$, edge bumps `edgeTowerBump A` of width $1/2 < \log 2$ near $A$ have bounded dyadic $H^1$ norm, zero same-side ratio correlations, and off-lattice reflected crossings summing to $\le -c_0 e^A$ by Chebyshev's prime theorem, refuting $-C_\sigma e^{2\sigma A}\,\mathrm{dyadicH1NormSq}(F)$ for every $\sigma < 1/2$. Neutralizing the rank-one $s = 1$ pole in `scalingSubsurface (oddRealTestsAt A)` restores the exact equivalence between the sub-exponential Sobolev floor and `zetaZeroWidth ≤ σ`.

## No-go closure (mandatory for obstructed sub-questions Q2a, Q2c-all-`a`, Q4-JH, Q5A-dispersion, Q6-raw-continuum)

- **Exact killing theorems/mechanisms:**
  1. *Q2(a):* `exists_odd_smooth_threeHundredSixtyTwoThousandths_zeta_pos_liouville_neg` — edge-concentrated odd spline on `[-181/500, 181/500]` turns $w(2) = -\log 2$ into a negative off-diagonal crossing exceeding the archimedean Lévy energy.
  2. *Q2(c) unrestricted `a` & `θ > ½`:* `not_uniform_all_multipliers_escapedPairing_rpow` ($a = N, N+1$ isolate $\mu(1)/1 = 1$) and `not_dyadic_escapedPairing_rpow_of_half_lt` ($\theta > 1/2$ contradicts `1/2 ≤ zetaZeroAbscissa`).
  3. *Q4 torsion-weighted JH:* `jacobiHurwitzHeight_dichotomy` and `jacobiHurwitz_largeSieve_inflation_ge_half_abs` — Tate homogeneity forces $q_P(z) \ge \tfrac{1}{2}|z \cdot z|$ under unsigned/large-sieve Riemann-inequality envelopes.
  4. *Q5(A) parity-blind dispersion:* `parityBlind_dispersion_diverges_above_threshold` — Bombieri/Selberg parity gap $2\kappa > 0$ against the signed cosine kernel diverges as $T^{1+\delta}/\log^2 T \gg N(T, 2T)$ on the positive inner lobe.
  5. *Q6 unneutralized `continuumPrimeTower`:* `not_continuumPrimeTower_subexponential_dyadicH1` — width-$1/2$ top-octave edge bumps reconstruct the off-lattice Chebyshev $s = 1$ pole $\le -c_0 e^A$ at $O(1)$ dyadic $H^1$ norm.
- **Strongest positive survivors:**
  1. *Q2(a)+(b):* `threeHundredSixtyTwoThousandths_selectivity_battery` — full complex-sector selective Weil positivity on `[-181/500, 181/500]` (`≥ 1/5000 ‖f‖₂²` when $w(2) = \log 2$, `< 0` on `w = λΛ`, `flippedTwoVonMangoldt`, and `shiftedPairVonMangoldt a`).
  2. *Q2(c):* `growingEndpointEscapedMoebiusLaw_tfae` and `riemannHypothesis_iff_growingEndpointEscapedMoebiusLaw_half` — exact equivalence between growing-endpoint `escapedPairing` saving and `zetaZeroAbscissa ≤ 1 - θ` / `RiemannHypothesis`.
  3. *Q3 & Q4:* `thetaBox_riemannRoch_and_serreDuality`, `sections_beyond_largeSieve_iff_zetaZeroWidth_le`, and `shortCycle_subquadratic_height_exists_primeTwo` — sign-independent Serre-dual scaling cohomology, sub-large-sieve width equivalence, and unconditional short-cycle subquadratic heights.
  4. *Q5(A) & Q5(B):* `multiModulus_ramanujan_primeCoalSum_split`, `escapeLaplaceSymbol_pole_and_visibility_laws`, `catalan_finite_gauge_separation`, and `liouvilleWindowGroundEigenvalue_twentyThreeFortieths_lt_neg_threeTenths`.
  5. *Q6:* `continuum_poleNeutralized_width_equivalence` — exact graded equivalence `zetaZeroWidth ≤ σ` after rank-one pole neutralization.
- **New insight:** Separates structural artifacts (rank-one $s = 1$ continuum pole, Bombieri parity gap, Tate quadratic homogeneity, $a = N$ boundary step) from the genuine gauge-charged arithmetic core, and establishes `[-181/500, 181/500]` as the first proved full-sector gauge-selective window past `½ log 2`.
- **Status:** Dependency-closed paper proofs and Lean 4 formalizations complete across all 6 modules in `GaloisForLFunctions.SelectivePositivityAndThresholdLaws`; `lake --old env lean` green and `#print axioms` verified (`[propext, Classical.choice, Quot.sound]`).

## Log

- 2026-10-26 — Created in `2-fully-proven/` with complete dependency-closed paper proofs and no-go salvage closures for Questions 1–6.
- 2026-10-27 — Promoted to `3-formalized/`: all 6 Lean modules in `GaloisForLFunctions/SelectivePositivityAndThresholdLaws/` verified green with `lake --old env lean`, wired into `SelectivePositivityAndThresholdLaws.lean` and `MainTheorems.lean`, and audited with `#print axioms`.
