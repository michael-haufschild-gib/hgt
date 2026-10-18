# Bézout–Valuation Incidence Wall 1 Programme Status (Modules 66–74)

Here is the exact, honest enumerated breakdown of the Wall 1 programme in [`BezoutValuationIncidence`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence.lean) through **Modules 66–74** toward [Wall 1](file:///Users/michael/Documents/code/hgt/docs/reports/wall1.md).

---

## I. Baseline Completed in Modules 66–70 (Programme Steps 1–5)

1. **Step 1 — Compensated Harmonic Predecessor-Peak Drift & Single-Divisor $O(1)$ Harmonic Defect ([`CompensatedHarmonicPredecessorPeakDriftAndDiagonalBudget.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/CompensatedHarmonicPredecessorPeakDriftAndDiagonalBudget.lean)):**
   - Isolated the exact predecessor-peak drift $\kappa(\varepsilon)$ (`pmPredecessorPeakLogDrift`), proved the exact budget identity $v(\varepsilon) + 2\kappa(\varepsilon) = 2\,\operatorname{pmInteriorLogCounterterm}(\varepsilon)$, proved $D_T^{\text{act}}(\varepsilon) - v(\varepsilon)H_T^{\text{comp}} = o(\log T)$ and $P_T^{\text{pred}}(\varepsilon) - \kappa(\varepsilon)H_T^{\text{comp}} = o(\log T)$, and proved the uniform $O(1)$ single-divisor harmonic remainder bound `abs_divisorHarmonic_sub_coeffDensity_mul_compensated_le`.
2. **Step 2 — Exact Self-Cancellation of the Pronic Potential & Non-Circular Interior Gradient Conservation ([`PronicPotentialSelfCancellationAndInteriorGradientConservation.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/PronicPotentialSelfCancellationAndInteriorGradientConservation.lean)):**
   - Substituting the summation-by-parts identity for $2 M_T^{\text{int}}(\varepsilon)$ into $E_T(\varepsilon) = D_T^{\text{act}}(\varepsilon) + 2 P_T^{\text{pred}}(\varepsilon) + 2 M_T^{\text{int}}(\varepsilon)$ **cancels $E_T(\varepsilon)$ identically from both sides**, leaving the non-circular conservation law (`pmBezoutInteriorGradient_add_two_mul_localImpulse_eq_activeDeleted_add_predecessorPeak`)
     $$\operatorname{Grad}_T(\varepsilon) + 2\,\operatorname{Local}_T(\varepsilon) = D_T^{\text{act}}(\varepsilon) + 2 P_T^{\text{pred}}(\varepsilon) - E_T^{\text{act}}(\varepsilon) - \Phi_\varepsilon(1)\Bigl(1 - \frac{1}{T+1}\Bigr),$$
     and proving that $E_T(\varepsilon) \le B_\varepsilon$ is two-sided equivalent (`pmPowerDampedDivisorDiscreteEnergy_le_two_mul_interiorPronic_add_half`, `pmBezoutInteriorPronicEnergy_le_two_mul_discreteEnergy_add_half`, `riemannHypothesis_of_pmBezoutInteriorPronicEnergy_bounded`) to bounding the **pure Bézout interior pronic energy**
     $$E_T^{\text{int}}(\varepsilon) := \sum_{n=1}^T \frac{I_\varepsilon(n)^2}{n(n+1)} \le B_\varepsilon \qquad (\forall T \ge 1).$$
3. **Step 3 — Arbitrary-Depth $m$-Step Bézout Shells & Route PM Second-Layer Profile ([`ArbitraryDepthBezoutShellsAndRoutePMSecondLayerProfile.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/ArbitraryDepthBezoutShellsAndRoutePMSecondLayerProfile.lean)):**
   - Constructed the arbitrary-depth Bézout shell decomposition for any lag horizon $L$ (`sieveActiveShellPrefix`, `sieveDeepInteriorPrefix`), proved exact support annihilation on $1 \le d \le L + 1$, and specialized to the Route PM second-layer profile (`pmSecondLayerInteriorPrefix`).
4. **Step 4 — Second-Order $O\bigl(1/((H+1)(H+2))\bigr)$ Pronic Tail via Abel Summation by Parts ([`OscillatoryPronicTailSummationByPartsAndSecondOrderVonMangoldtError.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/OscillatoryPronicTailSummationByPartsAndSecondOrderVonMangoldtError.lean)):**
   - Extracted the deterministic totient drift $\frac{\varphi(q)}{2(H+1)}$ to reach $O\bigl(1/((H+1)(H+2))\bigr)$ tail decay (`abs_pmRamanujanPrimitive_pronic_tail_sub_totient_drift_le`, `abs_finite_horizon_vonMangoldt_compensated_error_le`).
5. **Step 5 — Rank-1 Von Mangoldt + PSD Energy-Centered Pronic Gram Split ([`EnergyCenteredPronicGramPositivityAndVonMangoldtLowerBound.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/EnergyCenteredPronicGramPositivityAndVonMangoldtLowerBound.lean)):**
   - Proved $\mathcal{Q}_N^{\text{pronic}}(c) = \bigl(\sum_{e=2}^N \Lambda(e) Y_{N,c}(e)\bigr)^2 + \mathcal{Q}_N^{\text{ec}}(c)$ with $\mathcal{Q}_N^{\text{ec}}(c) \ge 0$ (`sieveEnergyCenteredPronicGramForm_nonneg`), $\mathcal{Q}_N^{\text{mc}}(c) \ge 0$ (`sieveMeanCenteredPronicGramForm_nonneg`), and the 3-term energy-centered prime-dilation recurrence `pmRamanujanEnergyCenteredGram_prime_pair`.

---

## II. Post–Module 70 Programme Formalized in Modules 71–74

### 1. Arithmetic-Progression Harmonic Remainder & Shifted-Divisor Starting-Point Bounds ([`ArithmeticProgressionHarmonicRemainderAndShiftedDivisorBounds.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/ArithmeticProgressionHarmonicRemainderAndShiftedDivisorBounds.lean) — Module 71)
- **What is formalized unconditionally:**
  - Defined the arithmetic-progression harmonic sum `progressionHarmonicSum q r K = ∑ k ∈ range K, 1 / (k * q + r)` and proved the exact two-sided sandwich (`progressionHarmonicSum_succ_bounds`):
    $$0 \le \frac{1}{r} - \frac{1}{q} \le \operatorname{progressionHarmonicSum}(q, r, K + 1) - \frac{(\operatorname{harmonic}\,K : \mathbb{R})}{q} \le \frac{1}{r},$$
    together with explicit remainder bounds (`abs_progressionHarmonicSum_succ_sub_harmonic_div_le`, `abs_progressionHarmonicSum_succ_sub_inv_add_harmonic_div_le`, `abs_progressionHarmonicSum_succ_sub_log_div_le`).
  - Proved that any shifted divisor hit $d_2 \mid n$ and $d_1 \mid (n + 1)$ ($n \ge 1$) automatically forces:
    1. $\operatorname{Coprime} d_1 d_2$ (`coprime_of_dvd_and_dvd_succ`),
    2. $\max(d_1, d_2 + 1) \le n + 1$ (`max_le_succ_of_dvd_and_dvd_succ`) and $d_1 d_2 \le (n + 1)^2$ (`mul_le_succ_sq_of_dvd_and_dvd_succ`),
    3. the reciprocal starting-point bounds $\frac{1}{n + 1} \le \min\bigl(\frac{1}{d_1}, \frac{1}{d_2 + 1}\bigr) \le \frac{1}{\sqrt{d_1 d_2}}$ (`inv_succ_le_min_of_dvd_and_dvd_succ`, `inv_succ_le_one_div_sqrt_mul`), and
    4. the progression-harmonic defect bound `shifted_divisor_progressionHarmonicSum_defect_bounds`.

### 2. Mean-Centered Pronic Gram Recurrence & Centering-Discrepancy Rank-One Bridge ([`MeanCenteredPronicGramRecurrenceAndCenteringDiscrepancyBridge.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/MeanCenteredPronicGramRecurrenceAndCenteringDiscrepancyBridge.lean) — Module 72)
- **What is formalized unconditionally:**
  - Defined `sieveCenteringDiscrepancy q = (q.totient : ℝ) / 2 - vonMangoldt q` and proved the exact entrywise rank-1 identity (`pmRamanujanMeanCenteredGram_eq_energyCentered_add_rankOne`) and quadratic form identity (`sieveMeanCenteredPronicGramForm_eq_energyCentered_add_sq`):
    $$\mathcal{G}^{\text{mc}}(p, q) = \mathcal{G}^{\text{ec}}(p, q) + \Delta(p)\,\Delta(q), \qquad
      \mathcal{Q}_N^{\text{mc}}(c) = \mathcal{Q}_N^{\text{ec}}(c) + \left(\sum_{e=2}^N \Delta(e)\,Y_{N,c}(e)\right)^2,$$
    giving the unconditional upper bound $\mathcal{Q}_N^{\text{ec}}(c) \le \mathcal{Q}_N^{\text{mc}}(c)$ (`sieveEnergyCenteredPronicGramForm_le_meanCentered`).
  - Proved the **pure-totient 3-term prime-dilation recurrence** for `pmRamanujanMeanCenteredGram` (`pmRamanujanMeanCenteredGram_prime_pair`), in which all von Mangoldt prime-power terms cancel identically:
    $$\mathcal{G}^{\text{mc}}(p q, p r) + \mathcal{G}^{\text{mc}}(p q, r) + \mathcal{G}^{\text{mc}}(q, p r) = (p - 1)\,\mathcal{G}^{\text{mc}}(q, r) + \frac{p(p - 1)}{4}\,\varphi(q)\,\varphi(r),$$
    along with its diagonal specialization `pmRamanujanMeanCenteredGram_prime_mul_diag`.
  - Proved the asymptotic annihilation of shifted energy-centered covariance on composite non-prime-power moduli (`tendsto_pmRamanujanEnergyCenteredGram_prime_mul_add_of_not_isPrimePow`): for $q, r > 1$ with $\neg\operatorname{IsPrimePow} q$,
    $$\lim_{p \to \infty,\,p\text{ prime}} \bigl(\mathcal{G}^{\text{ec}}(p q, r) + \mathcal{G}^{\text{ec}}(q, r)\bigr) = 0.$$

### 3. Two-Prime Dilation Profile Identity & Prime-Star Shear Cancellation ([`TwoPrimeDilationProfileIdentityAndPrimeStarShearCancellation.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/TwoPrimeDilationProfileIdentityAndPrimeStarShearCancellation.lean) — Module 73)
- **What is formalized unconditionally:**
  - Proved the **exact single-prime dilation profile identity** (`pmRamanujanPrimitiveGram_prime_mul_add_diag_eq_dilationProfile`): for any prime $p$ and $r > 1$ with $\neg p \mid r$,
    $$\mathcal{G}(pr, r) + \mathcal{G}(r, r) = \sqrt{p}\,\operatorname{pmRamanujanDilationProfile}(r, hr, p),$$
    and the **exact four-term two-prime dilation profile identity** (`pmRamanujanPrimitiveGram_two_prime_mul_eq_dilationProfile`, `pmRamanujanEnergyCenteredGram_two_prime_mul_eq_dilationProfile`): for primes $p, q$ and $r > 1$ with $\neg p \mid r$ and $\neg q \mid r$,
    $$\mathcal{G}(pr, qr) + \mathcal{G}(pr, r) + \mathcal{G}(qr, r) + \mathcal{G}(r, r) = \sqrt{p}\sqrt{q}\,\operatorname{pmRamanujanDilationProfile}\Bigl(r, hr, \frac{p}{q}\Bigr).$$
  - Upgraded the $O(1)$ bound on $\Phi_r(p)$ to the exact prime-limit asymptotic law (`tendsto_sqrt_mul_pmRamanujanDilationProfile_prime`, `tendsto_sqrt_mul_pmRamanujanDilationProfile_prime_of_not_isPrimePow`):
    $$\lim_{p \to \infty,\,p\text{ prime}} \sqrt{p}\,\operatorname{pmRamanujanDilationProfile}(r, hr, p) = \frac{\varphi(r)\,\Lambda(r)}{2},$$
    which vanishes for every composite non-prime-power $r$.
  - Proved the shifted two-mode shear-cancellation identities (`pmRamanujanPrimitiveGram_shifted_two_mode_eq`, `pmRamanujanEnergyCenteredGram_shifted_two_mode_eq`, `pmRamanujanMeanCenteredGram_shifted_two_mode_eq`) and the general prime-star dilation-profile decomposition (`prime_star_dilationProfile_decomposition`, `prime_star_shear_balanced_eq_dilationProfile_form`).

### 4. Route PM Cofactor Sieve Bridge & Unified Physical–Spectral Energy Equivalence ([`RoutePMCofactorSieveBridgeAndUnifiedEnergyEquivalence.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/RoutePMCofactorSieveBridgeAndUnifiedEnergyEquivalence.lean) — Module 74)
- **What is formalized unconditionally:**
  - Defined `pmCofactorDivisorWeight ε Q d = (pmPowerDampedRamanujanCofactor ε (Q + 1) d).re` and proved (`pmCofactorDivisorWeight_eq_pmRamanujanResidueCoeff`, `selbergMultiplesCoord_pmCofactorDivisorWeight`) that it is the exact finite Ramanujan multiples inverse of `q ↦ (pmPowerDampedRamanujanWeight ε q).re` at cutoff $Q + 1$.
  - Proved the exact identities linking the BVI pronic discrepancy functionals at `c = pmCofactorDivisorWeight ε Q` to the Route PM spectral functionals:
    - `sievePrefixDiscrepancy_pmCofactorDivisorWeight_eq`: $\operatorname{sievePrefixDiscrepancy}(Q+1, M, c_{\varepsilon, Q}) = \operatorname{Re}\bigl(\operatorname{pmPowerDampedRamanujanCumulativePrefix}(\varepsilon, Q, M)\bigr)$,
    - `sievePronicDiscrepancyGramForm_pmCofactorDivisorWeight_eq`: $\mathcal{Q}_{Q+1}^{\text{pronic}}(c_{\varepsilon, Q}) = \operatorname{pmPowerDampedRamanujanGramQuadratic}(\varepsilon, Q)$,
    - `sieveEnergyCenteredPronicGramForm_pmCofactorDivisorWeight_eq`: $\mathcal{Q}_{Q+1}^{\text{ec}}(c_{\varepsilon, Q}) = \operatorname{pmPowerDampedRamanujanEnergyVariance}(\varepsilon, Q)$,
    - `sieveMeanCenteredPronicGramForm_pmCofactorDivisorWeight_eq`: $\mathcal{Q}_{Q+1}^{\text{mc}}(c_{\varepsilon, Q}) = \operatorname{pmPowerDampedRamanujanMeanCenteredQuadratic}(\varepsilon, Q)$.
  - Proved the BVI spectral budget criteria for $L^2(0, \infty)$ admission and Mellin right-half-plane analyticity (`pmPowerDampedFermiSource_memLp_and_analytic_of_sieveEnergyCenteredPronicGramForm_budget`, `pmPowerDampedFermiSource_memLp_and_analytic_of_sieveMeanCenteredPronicGramForm_budget`, `pmPowerDampedFermiSource_memLp_and_analytic_of_sievePronicDiscrepancyGramForm_budget`) and the master synthesis theorem `routePM_physical_and_spectral_budget_synthesis`.

---

## III. Honest Status & Single Remaining Analytic Frontier

Per `docs/reports/STATUS.md` and `docs/reports/wall1.md`:
- Every reduction, conservation law, dilation identity, and physical–spectral equivalence in Modules 66–74 is **100% unconditional, axiom-clean (`[propext, Classical.choice, Quot.sound]`), and sorry-free**.
- Neither the uniform-in-$T$ bound $\operatorname{pmBezoutInteriorPronicEnergy}(\varepsilon, T) \le B_\varepsilon$ nor the equivalent uniform-in-$Q$ bound $\mathcal{Q}_{Q+1}^{\text{ec}}(\operatorname{pmCofactorDivisorWeight}(\varepsilon, Q)) = \operatorname{pmPowerDampedRamanujanEnergyVariance}(\varepsilon, Q) \le B_\varepsilon$ for $0 < \varepsilon < 1/2$ is claimed to be proved unconditionally; establishing either bound for all $\varepsilon > 0$ is equivalent to closing Wall 1 (and hence `RiemannHypothesis` via `riemannHypothesis_of_pmBezoutInteriorPronicEnergy_bounded` or `pmPowerDampedFermiSource_memLp_and_analytic_of_sieveEnergyCenteredPronicGramForm_budget`).