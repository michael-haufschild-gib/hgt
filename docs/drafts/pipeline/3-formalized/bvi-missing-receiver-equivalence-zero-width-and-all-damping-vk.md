# The Missing Receiver of Bézout–Valuation Incidence: Exact Equivalence, Zero-Width Admission, All-Column Chain Law, and All-Damping Vinogradov–Korobov Bounds

- **ID:** bvi-missing-receiver-equivalence-zero-width-and-all-damping-vk
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `formal/GaloisForLFunctions/BezoutValuationIncidence/README.md` §7.1 ("### 7.1 The receiver")
- **Statement:** For every damping $\varepsilon > 0$, the receiver formulations of `BezoutValuationIncidence` §7.1 (bounded actual receiver energy $\sup_T E_T(\varepsilon) < \infty$, bounded pure-interior pronic energy $\sup_T E_T^{\mathrm{int}}(\varepsilon) < \infty$, strict interior contraction of the Bézout interior martingale $M_T^{\mathrm{int}}(\varepsilon)$ against either $E_T(\varepsilon)$ or $E_T^{\mathrm{int}}(\varepsilon)$, boundedness of the compensated interior bracket $2 M_T^{\mathrm{int}}(\varepsilon) + 2 c^{\mathrm{int}}(\varepsilon) H_T^{\mathrm{comp}}$, $\ell^2$-membership of the first column $C_\varepsilon(\cdot, 0)$, $\ell^2$-membership of every column $C_\varepsilon(\cdot, k)$, and $\ell^2$-membership of $C_\varepsilon b$ for all finitely supported $b \in c_0(\mathbb{N}, \mathbb{R})$) are unconditionally equivalent, satisfy the sharp horizon-by-horizon comparison $|\sqrt{E_T^{\mathrm{int}}(\varepsilon)} - \sqrt{E_T(\varepsilon)}| \le 1/2$, hold on the exact half-line $\varepsilon > \Theta - 1/2$ with common derived-set infimum $\Theta - 1/2$, translate zeros with multiplicity up to the boundary $\operatorname{Re} \rho \ge 1/2 + k\varepsilon$, and hold unconditionally across the entire sub-half-damping range $0 < \varepsilon \le 1/2$ on the Vinogradov–Korobov band (removing the $\varepsilon \ge 1/4$ barrier).

## Goal
Resolve §7.1 ("The receiver") in `formal/GaloisForLFunctions/BezoutValuationIncidence/README.md` completely and unconditionally, formalize every consequence and corollary of this resolution, and apply it across `BezoutValuationIncidence` and `SignedArithmeticEnergyIncidence`.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean modules compiled and audited with `lake --old env lean`, `#print axioms` clean
- [x] 3 → 4  publication-ready: standalone paper / README integration

## Formalized Modules & Declarations

1. **Module 1 (`formal/GaloisForLFunctions/BezoutValuationIncidence/TheReceiverEquivalenceAndZeroWidthLaw.lean`)**:
   - `abs_sqrt_pmBezoutInteriorPronicEnergy_sub_sqrt_le_half`, `abs_pmBezoutInteriorPronicEnergy_sub_discreteEnergy_le`
   - `exists_pmBezoutInteriorGradient_add_localImpulse_compensated_bound`, `exists_pmBezoutInteriorPronicEnergy_sub_compensated_martingale_le_sqrt_add`
   - `interiorReceiverDampings_eq_receiverDampings`, `strictContractionDampings_eq_receiverDampings`, `strictInteriorContractionDampings_eq_receiverDampings`, `compensatedMartingaleDampings_eq_receiverDampings`, `mem_receiverDampings_iff_all_interior_forms`
   - `exists_pmBezoutInteriorPronicEnergy_budget_of_zetaZeroAbscissa_lt`, `exists_pmInterior_strict_contraction_of_zetaZeroAbscissa_lt`, `exists_pmInterior_strict_interior_contraction_of_zetaZeroAbscissa_lt`, `exists_compensated_pmBezoutInteriorMartingale_bound_of_zetaZeroAbscissa_lt`
   - `sInf_derivedSet_interiorReceiverDampings_eq_zetaZeroAbscissa_sub_half`, `sInf_derivedSet_strictContractionDampings_eq_zetaZeroAbscissa_sub_half`, `sInf_derivedSet_compensatedMartingaleDampings_eq_zetaZeroAbscissa_sub_half`
   - `analyticOrderAt_le_analyticOrderAt_sub_nat_mul_of_mem_receiverDampings`, `analyticOrderAt_le_analyticOrderAt_sub_nat_mul_of_mem_interiorReceiverDampings`, `analyticOrderAt_le_analyticOrderAt_sub_nat_mul_of_mem_strictContractionDampings`
   - `riemannHypothesis_iff_forall_pos_pmBezoutInteriorPronicEnergy_bounded`, `riemannHypothesis_iff_cofinal_pmBezoutInteriorPronicEnergy_bounded`, `riemannHypothesis_iff_forall_pos_pmInterior_strict_contraction`, `riemannHypothesis_iff_cofinal_pmInterior_strict_contraction_iff`, `riemannHypothesis_iff_forall_pos_compensated_pmBezoutInteriorMartingale_bounded`

2. **Module 2 (`formal/GaloisForLFunctions/BezoutValuationIncidence/AllDampingVinogradovKorobovBandAndInteriorGrowth.lean`)**:
   - `abs_weightCenteredPrefix_dampedSign_le_of_linear_all_pos`
   - `exists_abs_weightCenteredPrefix_pmPowerDamped_le_vk_all_pos`
   - `exists_receiver_le_on_vinogradovKorobovBand_of_pos`, `exists_interiorPronic_le_on_vinogradovKorobovBand_of_pos`, `exists_compensated_martingale_le_on_vinogradovKorobovBand_of_pos`
   - `parityPair_separated_on_vinogradovKorobovBand_of_pos`
   - `eventually_receiver_le_growth_of_pos`, `eventually_interiorPronic_le_growth_of_pos`, `eventually_receiver_le_mul_periodEnergy_of_pos`, `eventually_interiorPronic_le_mul_periodEnergy_of_pos`, `tendsto_interiorPronic_div_periodEnergy_zero_of_pos`

3. **Module 3 (`formal/GaloisForLFunctions/BezoutValuationIncidence/TheReceiverAndTheColumnsOfTheDampingChain.lean`)**:
   - `arithmeticDampingDilatedState`, `arithmeticDampingDilatedState_one`, `arithmeticDampingCenteredRow_eq_dilatedState_diff`
   - `sum_range_dilated_div_sq_le`, `sum_range_arithmeticDampingDilatedState_sq_le`
   - `sum_range_arithmeticDampingCenteredRow_sq_le`, `pmPowerDampedDivisorDiscreteEnergy_le_first_column_sum`
   - `mem_receiverDampings_iff_summable_first_column`, `mem_receiverDampings_iff_forall_column_summable`, `mem_receiverDampings_iff_finitelySupported_image_summable`
   - `summable_arithmeticDampingCenteredRow_sq_of_zetaZeroAbscissa_lt`, `exists_tsum_arithmeticDampingCenteredRow_sq_bound_of_zetaZeroAbscissa_lt`
   - `riemannHypothesis_iff_forall_pos_first_column_summable`, `riemannHypothesis_iff_cofinal_first_column_summable`

## Log
- 2026-10-24 — created in 1-in-progress
- 2026-10-24 — moved to 3-formalized after compiling and auditing all three modules with `lake --old env lean` and integrating into `BezoutValuationIncidence.lean` and `README.md`
