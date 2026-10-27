# Selective Positivity and Threshold Laws

**One question.** What separates prime-blind positivity below the square-root and Nyquist horizons
from selective arithmetic positivity beyond them, and what exact obstructions govern parity-blind
dispersion, unsigned torsion averaging, and raw continuum prime towers?

Below the Nyquist threshold $\tfrac12\log 2 \approx 0.34657$, the autocorrelation $f \star \tilde f$
of a test supported in $[-A,A]$ vanishes at $\pm\log n$ for every $n \ge 2$, so Weil positivity
holds blindly for every arithmetic weight $w : \mathbb{N} \to \mathbb{R}$. Across the global
square-root threshold $X = T$ (the diagonal horizon of the additive large sieve and Dirichlet mean
value theorem), unsigned energy estimates, parity-blind dispersion brackets, and unneutralized
continuum prime towers hit sharp structural obstructions.

`SelectivePositivityAndThresholdLaws` establishes the exact boundary laws, obstructions, and
unconditional positive theorems across all six faces of this threshold:

1. **Two-sided selective Weil positivity past $\tfrac12\log 2$** on $[-181/500, 181/500]$
   ($181/500 = 0.362 > \tfrac12\log 2$): coercive full-sector positivity $\Re W_w(f \star \tilde f)
   \ge \tfrac1{5000}\|f\|_2^2$ whenever $w(2) = \log 2$, paired with smooth odd refutation when
   $w(2) = -\log 2$ ($\lambda\Lambda$ and `flippedTwoVonMangoldt`) and smooth even refutation when
   $w(2) = (2^a + 2^{-a})\log 2$ (`shiftedPairVonMangoldt a`, $a \ne 0$).
2. **Two-prime ground-eigenvalue negativity on $[-23/40, 23/40]$ and archimedean-free Catalan
   $\{2,3,4\}$ separation** between $\Lambda$, real scale twists $n^\sigma\Lambda(n)$, ordinate
   twists $\cos(\gamma\log n)\Lambda(n)$, and $\lambda\Lambda$.
3. **Growing-endpoint escaped Möbius boundary law** across $0 < \theta \le \tfrac12$ (equivalent to
   $\Theta_\zeta \le 1 - \theta$, and at $\theta = \tfrac12$ to `RiemannHypothesis`) together with
   unconditional impossibility for $\theta > \tfrac12$.
4. **Serre-dual real-valued cohomology on polar and scaling surfaces**, selective theta log-volume
   separation against `shiftedPairVonMangoldt`, refutation on `goldenDatum`, and the graded
   sub-large-sieve section-growth equivalence to $\mathrm{width}(\zeta) \le \sigma$.
5. **Torsion-weighted Jacobi–Hurwitz height dichotomy and converse large-sieve quadratic inflation**
   $q_P(z) \ge \tfrac12 |z \cdot z|$ on degree-zero cycles, contrasted with exact subquadratic
   effectivity on proved short-cycle subsurfaces ($r \le \tfrac12(\log 2 + 1/50)$).
6. **Parity–lobe divergence for parity-blind dispersion at $\lambda = 1 + \delta > 1$**, exact
   multi-modulus Ramanujan–stabilizer decomposition, escape Laplace pole-residue splitting of
   $G_\varepsilon(s) = \zeta(s)(\zeta(s+\varepsilon)^{-1} - \Re\zeta(1+\varepsilon)^{-1})/s$, and
   exponential $-c_0 e^A$ divergence of raw continuum prime towers versus pole-neutralized Sobolev
   width equivalence.

Namespace `GaloisForLFunctions.SelectivePositivityAndThresholdLaws`; umbrella
`SelectivePositivityAndThresholdLaws.lean`.

---

## 1. Modules and Main Declarations

### 1.1 `LiouvilleOddWindowRefutationAndSelectiveFullPositivity.lean`

Crossing $\tfrac12\log 2$ into $[-181/500, 181/500]$ ($2 \cdot 181/500 = 0.724 \in (\log 2, \log 3)$)
exposes the single prime atom $n = 2$ while keeping all $n \ge 3$ outside autocorrelation support:

- **Refutation of the Liouville-twisted odd window (`w(2) = -log 2`).** Smoothing a balanced
  nine-knot odd clamp spline produces an explicit odd $F \in C^2_c([-181/500, 181/500])$ with
  $\int F^2 > 0$ satisfying $\tfrac1{1000}\int F^2 \le \Re W_\zeta(F \star \tilde F)$ while
  $\Re W_{\lambda\Lambda}(F \star \tilde F) = \Re W_{\mathrm{flippedTwo}}(F \star \tilde F) <
  -\tfrac1{1000}\int F^2 < 0$
  (`exists_odd_smooth_threeHundredSixtyTwoThousandths_zeta_pos_liouville_neg`,
  `exists_odd_smooth_threeHundredSixtyTwoThousandths_flippedTwo_neg`,
  `not_forall_odd_threeHundredSixtyTwoThousandths_re_weilFullFunctional_liouvilleTwist_nonneg`).
- **Coercive even-sector and full-sector positivity (`w(2) = +log 2`).** On the even sector, the
  Lorentz pole square $2\pi(\int F \cosh(x/2)\,dx)^2$ combines with a certified 32-piece degree-8
  rational upper envelope of $\tfrac{577}{800} - (\gamma(r) - \sqrt{2}\log 2\cos(r\log 2))$ on
  $[0, 69/2]$ and a $23 \times 23$ even Legendre $LDL^\top$ + Gershgorin factorization to prove
  `fullZeroForm F ≥ (1 / 5000) ∫ F²`
  (`fullZeroForm_ge_of_even_support_le_threeHundredSixtyTwoThousandths`). Combining with the
  Schur-lending odd certificate yields unconditional full-sector positivity past $\tfrac12\log 2$:
  - `fullZeroForm_ge_of_support_le_threeHundredSixtyTwoThousandths`
  - `zetaZeroConfig_re_W_ge_of_aperture_le_threeHundredSixtyTwoThousandths`
  - `re_windowedW_zetaZeroConfig_nonneg_of_threeHundredSixtyTwoThousandths`
  - `one_div_5000_le_ccmRestrictedWeilGroundEnergy_threeHundredSixtyTwoThousandths`
  - `lt_of_ccmRestrictedWeilGroundEnergy_nonpos_threeHundredSixtyTwoThousandths`
  - `re_weilFullFunctional_ge_of_full_window_of_atom_two_eq`
- **Non-tempered selectivity (`w(2) = (2^a + 2^{-a}) log 2`).** An even two-bump test localized near
  $\pm\tfrac12\log 2$ inside $[-181/500, 181/500]$ satisfies $\Re W_{\Lambda_a}(F \star \tilde F) <
  -\tfrac1{5000}\int F^2 < 0$ for non-zero shift $a \ne 0$
  (`exists_even_smooth_threeHundredSixtyTwoThousandths_zeta_pos_shiftedPair_neg`,
  `threeHundredSixtyTwoThousandths_selectivity_battery`).

### 1.2 `MoebiusEscapedPairingBoundaryLaw.lean`

For the signed Möbius source $x_j = \mu(j)/\sqrt{j}$ and flat test $y_j = 1/\sqrt{j}$ on $[1,N]$,
the escaped pairing across a congruence/dilation step $(a,b)$ collapses to the pure harmonic tail
$\sum_{(N-b)/a < j \le N} \mu(j)/j$ (`escapedPairing_moebiusSource`), independent of $(a,b)$ up to
the lower endpoint $M = \lfloor(N-b)/a\rfloor$:

- **Unrestricted multiplier obstruction at the escape origin.** Across arbitrary multipliers
  $a \in \mathbb{N}_+$, adjacent multipliers $a = N$ and $a = N + 1$ at $b = 0$ isolate the unit
  cell $\mu(1)/1 = 1$, forcing $\max(|\mathrm{escapedPairing}(N,N,0)|,
  |\mathrm{escapedPairing}(N,N+1,0)|) \ge \tfrac12$ for every $N \ge 1$ and refuting any uniform
  $C N^{-\theta}$ bound ($\theta > 0$) without controlling $(N-b)/a$
  (`escapedPairing_moebius_succ_sub_self`, `half_le_max_abs_escapedPairing_moebius`,
  `not_uniform_all_multipliers_escapedPairing_rpow`).
- **Exact quasi-Riemann equivalence across $0 < \theta \le \tfrac12$.** Uniform power saving
  $O_\varepsilon(((N-b)/a)^{-\theta+\varepsilon})$ across all $(a,b)$ with $1 \le (N-b)/a$
  (`GrowingEndpointEscapedMoebiusLaw θ`), single-multiplier dyadic saving at $a = 2, b = 0$
  (`DyadicEscapedMoebiusLaw θ`), and the zero-free strip bound `zetaZeroAbscissa ≤ 1 - θ` are
  unconditionally equivalent (`growingEndpointEscapedMoebiusLaw_tfae`). At $\theta = \tfrac12$,
  this is unconditionally equivalent to `RiemannHypothesis`
  (`riemannHypothesis_iff_growingEndpointEscapedMoebiusLaw_half`,
  `riemannHypothesis_iff_forall_lt_half_growingEndpointEscapedMoebiusLaw`).
- **Unconditional impossibility beyond $\theta = \tfrac12$.** Even for $a = 2, b = 0$, no bound
  $C N^{-\theta}$ holds for any $\theta > \tfrac12$ (`not_dyadic_escapedPairing_rpow_of_half_lt`).

### 1.3 `SerreDualScalingCohomologyAndLargeSieveSections.lean`

Rank-based Dirichlet section counts read only support cardinalities and cannot distinguish $\Lambda$
from non-tempered weights. Replacing integer dimensions by real log-volumes restores arithmetic
selectivity and Serre duality:

- **Selective theta log-volumes.** `thetaBoxH0 w s` and `thetaBoxH1 w s` are strictly positive,
  satisfy Poisson functional-equation Serre duality $d \mapsto -d$, capture the exact box-minus-node
  defect $E_w(s) = (e^s + s - 1) - \sum_{k \le e^s} w(k)$ (`= e^s + s - 1 - \psi(e^s)` at $w = \Lambda$)
  via `thetaBoxH0 w s - thetaBoxH1 w s = E_w(s)` (`thetaBox_riemannRoch_and_serreDuality`), and
  strictly separate $\Lambda$ from `shiftedPairVonMangoldt a` ($a \ne 0$) for every $s \ge \log 2$
  (`thetaBox_strict_selectivity_shiftedPair`).
- **Sign-free polar-box cohomology on polar surfaces.** `surfaceBoxH0` and `surfaceBoxH1` are
  nonnegative, satisfy exact Serre duality $h^1(D) = h^0(K - D)$ (`surfaceBox_serreDuality`),
  satisfy the Riemann inequality and quadratic nef growth on unitary Weil curves over $\mathbb{F}_q$
  (`curve_frobMass_cohomology_calibration`), and refute Riemann–Roch on the positive self-intersection
  cone of `goldenDatum` (`goldenDatum_frobMass_cohomology_refutes_riemannRoch`).
- **Sub-large-sieve section growth and width equivalence.** Paying the odd-sector Chebyshev defect
  by a sub-large-sieve Sobolev budget $C e^{2\beta r}(\|f\|_2^2 + \|f'\|_2^2)$ ($\forall \beta > \sigma$)
  is unconditionally equivalent to `zetaZeroWidth ≤ σ` and `oddDefectFloorRate ≤ σ`
  (`sections_beyond_largeSieve_iff_zetaZeroWidth_le`); globally on `scalingSurface`, Serre-dual
  asymptotic Riemann–Roch with subquadratic degree-zero growth is equivalent to `RiemannHypothesis`
  (`serreDual_section_growth_iff_riemannHypothesis`).

### 1.4 `JacobiHurwitzTorsionInflationAndShortCycleHeights.lean`

Every torsion-weighted Jacobi–Hurwitz packet $h_P(x) = \sum_i w_i \log\theta_{\mathrm{JH}}(t_i, J_i(x))$
lies within an explicit uniform constant $B_P$ of its nonnegative quadratic form
$q_P(x) = \sum_i w_i \pi J_i(x)^2 / t_i$ (`abs_jacobiHurwitzHeight_sub_quad_le`):

- **Sharp dichotomy and converse large-sieve inflation.** Every packet $P$ either vanishes
  identically on $\ker(\cdot A)$ (forcing boundedness $|h_P(z)| \le B_P$ and reducing any
  asymptotic Riemann inequality to `S.HodgeIndex`) or inflates quadratically $h_P(nz) \ge q_P(z)n^2 - B_P$
  (`jacobiHurwitzHeight_dichotomy`). Any packet satisfying the unsigned Cauchy–Schwarz /
  large-sieve majorant $\tfrac12|x \cdot (x - \kappa)| - o(n^2)$ inflates on every degree-zero
  class with exact coefficient $q_P(z) \ge \tfrac12|z \cdot z|$
  (`jacobiHurwitz_largeSieve_inflation_ge_half_abs`), and on abundant classes even the signed
  asymptotic Riemann inequality forces $q_P(z) \ge \tfrac14|z \cdot z| > 0$
  (`jacobiHurwitzQuad_ge_quarter_of_abundant`, `goldenDatum_no_asymptotic_subquadratic_height`).
- **Short-cycle existence and global equivalence.** On `scalingSubsurface (primitiveSmoothRealTestsAt r)`
  for $r \le \tfrac12(\log 2 + 1/50)$ (including $r = 3/10$), `optimalEffectivity` gives an
  unconditional nonnegative height with exact `RiemannInequality` and identical vanishing on
  degree-zero rays (`shortCycle_subquadratic_height_exists_primeTwo`). Globally on `scalingSurface`,
  existence of a bounded-below asymptotic subquadratic height is unconditionally equivalent to
  `RiemannHypothesis` and to two-window Weil positivity on $[-3/10, 3/10]$
  (`riemannHypothesis_iff_exists_asymptotic_subquadratic_height`).

### 1.5 `ParityLobeObstructionAndEscapeLaplaceSplit.lean`

- **Multi-modulus Ramanujan–stabilizer split.** Weighting normalized level-$d$ Dirichlet-character
  averages of `twistedPrimeCoalSum` by `stabilizerDivisorWeight Q d` across $1 \le d \le Q$
  ($2Q\theta_0 < 1$) reconstructs the `ramanujanStabilizerPacket Q |n - m|`-weighted prime-pair
  sum (converging as $Q \to \infty$ to `hardyLittlewoodSingularSeries |n - m|`, which vanishes on
  odd lags and is positive on even lags), while the non-congruent residue discrepancy has zero
  character mean at every modulus $q \le Q$ (`multiModulus_ramanujan_primeCoalSum_split`,
  `tendsto_ramanujanStabilizerPacket`).
- **Selberg parity involution and trans-threshold parity–lobe divergence.** The nonnegative weights
  `selbergEvenVonMangoldt = Λ + λΛ` and `selbergOddVonMangoldt = Λ - λΛ` average to $\Lambda$ with
  pure-prime pair correlations $0$ vs. $4\log p\log p'$ (`selbergParity_pair_gap_on_primes`). Any
  parity-blind dispersion bracket $|C(r) - C_0(r)| \le \kappa S(r)$ ($\kappa > 0, S(r) \ge s_{\min} > 0$)
  accumulates at least $(\kappa s_{\min} K_1 / 2)\widehat\Omega_c(0)$ on the positive inner cosine
  lobe, diverging as $T^{1+\delta}/\log^2 T \gg N(T,2T)$ for every $\lambda = 1 + \delta > 1$ and
  refuting both $B\delta^2/(1+\delta)^2$ and the $\lambda = 4/3$ budget $5/36$
  (`parityBlind_dispersion_diverges_above_threshold`,
  `parityBlind_refutes_quadratic_and_fourThirds_budgets`). Conversely, bounding
  `oddEvenShiftPrimeCoalescentSurplus` or `PrimeCoalescentSurplusAtMost β` ($\beta < 5/36$,
  $\beta \le 1/18$) unconditionally certifies critical-line proportions $> 2/3$ and $\ge 3/4$
  (`oddEvenShift_singleProfile_certifies_proportion`, `coalescent_surplus_battery_laws`).
- **Escape Laplace split and visibility equivalence.** On the damping strip, the receiver line
  symbol equals $G_\varepsilon(s) = \zeta(s)(\zeta(s+\varepsilon)^{-1} - \Re\zeta(1+\varepsilon)^{-1})/s$
  (`escapeLaplaceSymbol_eq_invZeta_form`), splits at every simple zero $\rho$ into the simple pole
  $(\zeta(\rho-\varepsilon)/(\zeta'(\rho)(\rho-\varepsilon)))/(s - (\rho-\varepsilon))$ plus a
  bounded remainder, and positive visible gauge mass on every escape state across $0 < \varepsilon < \tfrac12$
  is unconditionally equivalent to `RiemannHypothesis` (`escapeLaplaceSymbol_pole_and_visibility_laws`).

### 1.6 `TwoPrimeCatalanSeparationAndContinuumTowerObstruction.lean`

- **Archimedean-free Catalan $\{2,3,4\}$ separation.** Because $3 + 1 = 4 = 2^2$ has even
  $\Omega(4) = 2$ while $\Omega(2) = 1$ is odd, `catalanSuccessorSquareForm w = w 2 * w (3 + 1)`
  equals $+8^\sigma(\log 2)^2 > 0$ on every scale twist $n^\sigma\Lambda(n)$ ($\sigma \in \mathbb{R}$)
  and $-(\log 2)^2 < 0$ on $\lambda\Lambda$, while `catalanKroneckerTwistDefect` vanishes on
  ordinate twists $\cos(\gamma_0\log n)\Lambda(n)$ at $\gamma = \gamma_0$ and obeys the Kronecker
  repulsion bound $\ge \tfrac1{5000}e^{-2|\gamma|}$ on $\lambda\Lambda$ for all $\gamma \in \mathbb{R}$
  (`catalan_finite_gauge_separation`).
- **Variational ground eigenvalue on $[-23/40, 23/40]$.** `liouvilleWindowRayleighSet r` is
  unconditionally bounded below for every $r > 0$ (`bddBelow_liouvilleWindowRayleighSet`), and
  mollifying $u^3((27/50)^2 - u^2)\mathbf{1}_{[-27/50,27/50]}(u)$ produces a smooth odd test in
  $[-23/40, 23/40]$ with $\Re W_\zeta > \tfrac1{25}\int F^2 > 0$ and
  $\Re W_{\lambda\Lambda} < -\tfrac3{10}\int F^2 < 0$, proving
  `liouvilleWindowGroundEigenvalue (23 / 40) < -(3 / 10)`
  (`exists_smooth_odd_twentyThreeFortieths_zeta_pos_liouville_neg`,
  `liouvilleWindowGroundEigenvalue_twentyThreeFortieths_lt_neg_threeTenths`).
- **Lattice-to-continuum prime-tower obstruction and pole-neutralized width law.** On the integer
  lattice $[1,X]$, every prime $p > X$ has `towerOddPrimeSide q X p K = 0` identically
  (`towerOddPrimeSide_eq_zero_of_lt`). On the continuum $[0,A]$, edge bumps `edgeTowerBump A` of
  width $\tfrac12 < \log 2$ near $A$ have bounded dyadic $H^1$ norm, zero same-side ratio
  correlations, and off-lattice reflected crossings summing to $\le -c_0 e^A$ by Chebyshev's prime
  theorem (`eventually_sum_continuumPrimeTower_edgeTowerBump_le`), refuting
  $-C_\sigma e^{2\sigma A}\,\mathrm{dyadicH1NormSq}(F)$ for every $\sigma < \tfrac12$
  (`not_continuumPrimeTower_subexponential_dyadicH1`). Neutralizing the $s = 1$ pole in
  `scalingSubsurface (oddRealTestsAt A)` restores the exact equivalence between the sub-exponential
  Sobolev floor and `zetaZeroWidth ≤ σ` (`continuum_poleNeutralized_width_equivalence`).
