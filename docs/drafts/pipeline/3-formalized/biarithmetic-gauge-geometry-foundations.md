# Foundational Theorems of Biarithmetic Gauge Geometry: Gauge Vacua, Quantitative Catalan Repulsion, Chiral Coupled Deformations, Euclidean Cell Subdivisions, and Torsion Escape

- **ID:** biarithmetic-gauge-geometry-foundations
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** docs/reports/review-2610/argon.md §4 (`Biarithmetic Gauge Geometry`)
- **Statement:** Five foundational theorems establishing the objects, obstructions, and positive survivors of Biarithmetic Gauge Geometry, unified in `GaloisForLFunctions.BiarithmeticGaugeGeometry.biarithmetic_gauge_geometry_master_theorem`: (I) Unitary prime-gauge equivalence of multiplicative lattice operators (`nonneg_realSign_latticeForm_iff`) vs. Catalan–Bézout successor holonomy reconstruction on `{2, 3, 4}` (`catalan_holonomy_two`, `catalan_holonomy_three`, `succConn_liouville_three`); (II) Baker-free all-height Diophantine twist repulsion `(1 + cos(γ log 2)) + (1 + cos(γ log 3)) ≥ (1/50) exp(-|γ|)` (`liouville_kronecker_repulsion_ge`); (III) Unconditional disproof of two-sided `CoupledRigid γ` at unboundedly many Hardy critical-line zeros (`exists_gt_not_coupledRigid`, `not_forall_coupledRigid`), chiral asymmetry of critical-line deformations (`isEvenPosDef_criticalSplitMultiplier`, `not_isEvenPosDef_inwardCollapseMultiplier`), `O(2^{-σ})` vs. `Θ(σ^{-3})` Hadamard–Dirichlet lattice separation (`criticalSplit_escapes_dirichletLattice`, `coupledQuartet_escapes_dirichletLattice`), and sufficiency of the surviving one-sided `CentralVanishingCeiling γ` for `RiemannHypothesis` (`riemannHypothesis_of_forall_centralVanishingCeiling`); (IV) Polar-neutral rank-one cancellation of the lattice reflected-diagonal surplus (`reflectedDiag_add_offDiagPolar_eq_neg_levy`) paired with exact logarithmic cell subdivision (`sum_logCellWidth_mul_add_eq`, `continuumCellShiftCorr_eq_spine_add_remainder`) and `m`-uniform disjoint-block biarithmetic Sobolev remainder control (`abs_euclideanCellRemainder_le_of_supported`); (V) Rank-2 monomial theta marginal collapse (`monomial_theta_sum_factors`) vs. fixed-point-free dyadic rational-torsion rotation (`dyadic_torsion_rotation_fixed_point_free`) and pole-cancelled bi-torsion Ramanujan contrast (`biTorsionContrast_zero`, `biTorsionContrast_primes_values`).

## Goal
Supply the rigorous mathematical foundations, core tools, sharp no-go theorems, and dependency-closed positive survivors of the research programme `GaloisForLFunctions.BiarithmeticGaugeGeometry`, bridging `BiarithmeticGeometry`, `ArithmeticPolarization`, `ArithmeticEffectivityTheory`, `ArithmeticOrientationTheory`, `StripBochnerWeilForcing`, and `ArithmeticCorrespondencePositivity`.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorem `GaloisForLFunctions.BiarithmeticGaugeGeometry.biarithmetic_gauge_geometry_master_theorem` (and 6 modules under `formal/GaloisForLFunctions/BiarithmeticGaugeGeometry/`), `lake --old env lean` green, `#print axioms` verified (`[propext, Classical.choice, Quot.sound]`)

## Lean Modules and Key Declarations
1. `formal/GaloisForLFunctions/BiarithmeticGaugeGeometry/PrimeGaugeTorusAndVacuumIntertwiners.lean`
   - `PrimeGauge`, `PrimeGauge.eulerGauge`, `PrimeGauge.liouvilleGauge`, `PrimeGauge.kroneckerGauge`, `PrimeGauge.gaugeChar`
   - `gaugeTwist`, `diagForm_gaugeTwist_eq`, `ratioShift_gaugeTwist_eq`, `realSign_latticeForm_eq`, `nonneg_realSign_latticeForm_iff`
   - `succConn`, `succConn_flat_iff_primes_eq_one`, `catalan_holonomy_two`, `catalan_holonomy_three`, `succConn_liouville_three`
2. `formal/GaloisForLFunctions/BiarithmeticGaugeGeometry/QuantitativeCatalanDiophantineRepulsion.lean`
   - `abs_log_nat_sub_ge`, `two_pow_ne_three_pow`, `abs_odd_mul_log_two_sub_odd_mul_log_three_ge`
   - `exists_odd_int_one_add_cos_ge`, `liouville_kronecker_repulsion_ge`, `abs_height_ge_of_liouville_approx`
3. `formal/GaloisForLFunctions/BiarithmeticGaugeGeometry/ChiralDeformationAndNonRigidityOfHeightCoupledSystems.lean`
   - `CoupledRigid`, `CentralVanishingCeiling`, `criticalSplitMultiplier`, `inwardCollapseMultiplier`, `HasDirichletLatticeDecay`
   - `isEvenPosDef_criticalSplitMultiplier`, `exists_criticalSplit_deformation_of_xi_zero`, `not_coupledRigid_of_xi_critical_zero`, `exists_gt_not_coupledRigid`, `not_forall_coupledRigid`
   - `not_isEvenPosDef_inwardCollapseMultiplier`
   - `tendsto_cube_mul_zero_of_dirichletLatticeDecay`, `tendsto_cube_mul_neg_logDeriv_criticalSplit`, `tendsto_cube_mul_neg_logDeriv_coupledQuartetSymSquare`, `criticalSplit_escapes_dirichletLattice`, `coupledQuartet_escapes_dirichletLattice`
   - `criticalSplit_strictly_below_centralCeiling`, `coupledRigid_implies_centralVanishingCeiling`, `xi_ne_zero_of_centralVanishingCeiling`, `riemannHypothesis_of_forall_centralVanishingCeiling`
4. `formal/GaloisForLFunctions/BiarithmeticGaugeGeometry/EuclideanCellRemainderAndPolarNeutralCollapse.lean`
   - `polarCrossingAmplitude`, `archLevyProductWeight`, `fullArchCrossingForm`, `offDiagPolarForm`
   - `neg_archPairKernel_eq_polar_sub_levy`, `archReflectedDiagWeight_eq_polar_sub_levy`, `fullArchCrossingForm_eq_polar_sq_sub_levy`, `fullArchCrossingForm_polarNeutral_eq`, `reflectedDiag_add_offDiagPolar_eq_neg_levy`, `exists_nonzero_polarNeutral_profile`
   - `logCellWidth`, `sum_logCellWidth_mul_add_eq`, `continuumCellShiftCorr`, `divisibleCellSpine`, `euclideanCellRemainder`, `continuumCellShiftCorr_eq_spine_add_remainder`
   - `cellL2NormSq`, `biarithmeticSobolevEnergy`, `euclideanCellRemainder_sq_le`, `abs_euclideanCellRemainder_le_of_supported`
5. `formal/GaloisForLFunctions/BiarithmeticGaugeGeometry/RamanujanTorsionStabilizersAndMonomialCollapse.lean`
   - `monomial_theta_sum_factors`, `monomial_torsion_fixes_origin`, `monomial_torsion_preserves_axes`
   - `torsionMulEquiv`, `torsionMulEquiv_no_fixed_points_of_sub_one_isUnit`, `dyadic_torsion_rotation_fixed_point_free`
   - `ramanujanTorsionSum`, `ramanujanTorsionSum_coprime_mul`, `sum_ramanujanTorsionSum_eq_zero`, `sum_normSq_ramanujanTorsionSum`, `ramanujanTorsionSum_prime`
   - `biTorsionContrast`, `biTorsionContrast_zero`, `biTorsionContrast_coprime_mul`, `biTorsionContrast_primes_values`
6. `formal/GaloisForLFunctions/BiarithmeticGaugeGeometry/MasterBiarithmeticGaugeGeometryTheorem.lean`
   - `biarithmetic_gauge_geometry_master_theorem`

## Complete Dependency-Closed Paper Proofs (`[PROVED HERE]`)

### Theorem I (Unitary Prime-Gauge Blindness vs. Catalan–Bézout Successor Rigidity) `[PROVED HERE]`
1. **Prime Gauge Torus and Multiplicative Lift:** Let $\Omega_{\mathcal{P}}$ be the group of prime phase assignments $\omega : \mathbb{N} \to \mathbb{C}$ satisfying $\|\omega(p)\| = 1$ for every prime $p$ and $\omega(n) = 1$ for non-primes, with completely multiplicative extension $\chi_\omega(n) = \prod_{p \in n.\text{primeFactors}} \omega(p)^{v_p(n)}$ for $n \ge 1$ ($\chi_\omega(0) = 0$). For $m, n \ge 1$, unique factorization gives $\chi_\omega(m n) = \chi_\omega(m)\chi_\omega(n)$ and $\|\chi_\omega(n)\| = 1$. At $\omega_{\mathbf{1}}(p) = 1$, $\chi_{\mathbf{1}}(n) = 1$; at $\omega_{\boldsymbol{-1}}(p) = -1$, $\chi_{\boldsymbol{-1}}(n) = (-1)^{\Omega(n)}$ is Liouville's function $\lambda(n)$; at $\omega_\gamma(p) = p^{i\gamma}$, $\chi_{\omega_\gamma}(n) = n^{i\gamma}$ for $n \ge 1$.
2. **Unitary Multiplicative Blindness:** For any $\psi : \mathbb{N} \to \mathbb{C}$, define $(U_\omega \psi)(n) = \chi_\omega(n)\psi(n)$. Since $\|\chi_\omega(n)\| = 1$ for $n \ge 1$, $\|U_\omega \psi(n)\| = \|\psi(n)\|$, so every diagonal potential $\sum_{n=1}^X d(n) \|\psi(n)\|^2$ is strictly $U_\omega$-invariant, while for every multiplicative ratio shift $m \ge 1$ and $a \ge 1$, $\overline{(U_\omega \psi)(a)}\, (U_\omega \psi)(a m) = \chi_\omega(m)\,\overline{\psi(a)}\,\psi(a m)$. For real sign gauges $\sigma : \mathbb{N} \to \{\pm 1\}$, $\chi_\sigma(a)\chi_\sigma(b) = \chi_\sigma(ab)$ makes **both** ratio correlations $\chi_\sigma(m)\psi(a)\psi(am)$ and product correlations $\chi_\sigma(ab)\psi(a)\psi(b)$ unitarily equivalent to the Euler vacuum ($\sigma \equiv +1$) via $\phi(n) = \chi_\sigma(n)\psi(n)$.
3. **Successor Connection and Catalan Reconstruction:** Define $A_\omega(n) := \overline{\chi_\omega(n)}\chi_\omega(n+1)$ ($n \ge 1$). Flatness $A_\omega(n) = 1$ on $1 \le n \le N$ holds iff $\omega(p) = 1$ for every prime $p \le N + 1$. On $\{2, 3, 4\}$, $A_\omega(2) = \overline{\omega(2)}\omega(3)$ and $A_\omega(3) = \overline{\omega(3)}\omega(2)^2$, so $A_\omega(2)A_\omega(3) = \omega(2)$ and $A_\omega(2)^2 A_\omega(3) = \omega(3)$.

### Theorem II (Quantitative Baker-Free Diophantine Repulsion of the Liouville Vacuum off the Kronecker Line) `[PROVED HERE]`
1. **Parity-Separated Integer Power Gap:** Distinct integers $A, B \ge 1$ satisfy $|\log A - \log B| \ge \frac{1}{A + B}$. Since $2^a$ is even for $a \ge 1$ and $3^b$ is odd, every pair of odd integers $u, v \in \mathbb{Z}$ satisfies $|u \log 2 - v \log 3| \ge \frac{1}{2^{|u|} + 3^{|v|}}$.
2. **Cosine Distance and Determinant Elimination:** Choosing odd $u_2, u_3 \in \mathbb{Z}$ with $|u_p| \le \frac{|\gamma|\log p}{\pi} + 1$ and $1 + \cos(\gamma\log p) \ge \frac{2}{\pi^2}(\gamma\log p - u_p\pi)^2$, the cross-combination $(\log 3)\delta_2 - (\log 2)\delta_3 = \pi(u_3 \log 2 - u_2 \log 3)$ eliminates $\gamma$ identically. Since $\frac{\log 2 \cdot \log 3}{\pi} < \frac{1}{2}$, $2^{|u_3|} + 3^{|u_2|} \le 5 e^{|\gamma|/2}$, giving $(1 + \cos(\gamma\log 2)) + (1 + \cos(\gamma\log 3)) \ge \frac{1}{50} e^{-|\gamma|}$ for all $\gamma \in \mathbb{R}$.

### Theorem III (Disproof of `CoupledRigid`, Chirality Law, Lattice-Decay Separation, and `CentralVanishingCeiling`) `[PROVED HERE]`
1. **Outward Splitting & Failure of `CoupledRigid`:** $W_\beta(s) = \frac{(s - 1/2)^2 + \beta^2}{(s - 1/2)^2}$ has Bochner cosine weight $2 e^{-(\sigma - 1/2)t}(1 - \cos(\beta t)) \ge 0$. At every Hardy critical zero $\xi(\tfrac{1}{2} + i\gamma) = 0$, $\Lambda_\gamma$ vanishes at $s = \tfrac{1}{2}$ to order $\ge 2$; cancelling $(s - \tfrac{1}{2})^2$ via iterated `dslope` constructs $(F_\beta, \Lambda_\beta) \in \text{HeightCoupledSystem } 2\ 1\ 1\ \gamma$ ($\beta \ne 0$) not scalar-proportional to $\zeta_\gamma$.
2. **Chirality & Lattice Separation:** Inward collapse $W_\beta^{-1}$ is a $3$-point `polarSum` with real-anchor weight $-2 < +1$, violating `real_anchor_of_posDef_polarSum` and failing `IsEvenPosDef`. On $\sigma \to +\infty$, $\sigma^3$ annihilates any $O(2^{-\sigma})$ Dirichlet log-lattice derivative while converging to $2\beta^2 > 0$ on $W_\beta$ and $4b^2 + 4a^2 > 0$ on `coupledQuartetSymSquare`.
3. **Chiral Survivor:** `CentralVanishingCeiling γ` ($\operatorname{ord}_{1/2}(\Lambda) \le \operatorname{ord}_{1/2}(\Lambda_\gamma)$) holds strictly on all $W_\beta$ splittings ($\Delta\operatorname{ord}_{1/2} = -2$) while excluding off-critical quartets ($\Delta\operatorname{ord}_{1/2} = +4$) and implying `RiemannHypothesis`.

### Theorem IV (Polar-Neutral Rank-One Collapse & Exact Euclidean Cell-Remainder Subdivision) `[PROVED HERE]`
1. **Polar-Neutral Collapse:** Across $(a, b) \in [2, X]^2$, $-k_{\mathrm{arch}}(-\log a, \log b) = \frac{(a-1)(b-1)}{2\sqrt{ab}} - \frac{(ab)^{3/2}}{(ab)^2 - 1}$ collapses the linear reflected-diagonal part into $\frac{1}{2}(\sum_{n=2}^X \frac{n-1}{\sqrt{n}} q_n)^2$, which vanishes identically on $\sum_{n=2}^X \frac{n-1}{\sqrt{n}} q_n = 0$.
2. **Cell Subdivision & Sobolev Bound:** Logarithmic cells $w_n = \log(n+1) - \log n$ satisfy $\sum_{r=0}^{m-1} w_{am+r} = w_a$, factoring shift correlations cleanly into `divisibleCellSpine` + `euclideanCellRemainder`. Disjointness of Euclidean blocks $\{am + j : 0 \le j < m\}$ across $a \ge 1$ bounds $|R_m(c)| \le \sqrt{\sum_{a=1}^X w_a c_a^2} \cdot \sqrt{\sum_{k=1}^X k(c_{k+1} - c_k)^2}$ for profiles supported on $[1, X]$, uniformly in $m \ge 1$.

### Theorem V (Monomial Theta Diagonal Collapse vs. Dyadic Rational-Torsion Rotation and Bi-Torsion Contrast) `[PROVED HERE]`
1. **Marginal Collapse vs. Stabilizer Escape:** Separable monomial $\mathbb{Z}^2$ dilations factor into 1D marginals fixing $(0,0)$, whereas on $(\mathbb{Z}/q\mathbb{Z})^\times$ ($q \ge 3$ odd), dyadic multiplication $u \mapsto 2u$ has zero fixed points since $2 - 1 = 1$ is a unit.
2. **Pole-Cancelled Bi-Torsion Contrast:** $\Delta_{q_1, q_2}(n) = \varphi(q_2)c_{q_1}(n) - \varphi(q_1)c_{q_2}(n)$ satisfies $\Delta_{q_1, q_2}(0) = 0$, $\Delta_{q_1, q_2}(pn) = \Delta_{q_1, q_2}(n)$ for $\gcd(p, q_1 q_2) = 1$, and for distinct primes $q_1 \ne q_2$ evaluates to $q_1 - q_2 \ne 0$ at $1$, $+q_2(q_1 - 1) > 0$ at $q_1$, and $-q_1(q_2 - 1) < 0$ at $q_2$.

## No-go closure (for `CoupledRigid γ`)
- **Exact killing theorem/mechanism:** `not_coupledRigid_of_xi_critical_zero`, `exists_gt_not_coupledRigid`, `not_forall_coupledRigid` in `ChiralDeformationAndNonRigidityOfHeightCoupledSystems.lean`.
- **Strongest positive survivor:** `CentralVanishingCeiling γ` (`criticalSplit_strictly_below_centralCeiling`, `riemannHypothesis_of_forall_centralVanishingCeiling`), paired with `not_isEvenPosDef_inwardCollapseMultiplier` and `coupledQuartet_escapes_dirichletLattice`.
- **New insight:** Higher-degree Bochner positivity on the critical line is chiral (outward-only, $\Delta\operatorname{ord}_{1/2} < 0$), whereas off-critical quartet contraction moves zeros inward ($\Delta\operatorname{ord}_{1/2} = +4$); moreover, finite rational Hadamard surgeries exit the $O(2^{-\sigma})$ discrete Dirichlet log-lattice via $\Theta(\sigma^{-3})$ decay.
- **Status:** Fully formalized in Lean 4; `lake --old env lean` green; transitive axioms verified: `[propext, Classical.choice, Quot.sound]`.

## Log
- 2026-10-26 — Dependency-closed paper proofs completed and formalized across 6 Lean 4 modules in `formal/GaloisForLFunctions/BiarithmeticGaugeGeometry/`; wired into `BiarithmeticGaugeGeometry.lean` and `MainTheorems.lean`.
