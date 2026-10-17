# CHMD + HF + EWU Three-Option Synthesis: Odd-Profile Collar/Chain Bridge, Clamped First-Cell Resolvent Bound, and Polar Blind Spectral Gap

- **ID:** chmd-hf-ewu-three-options-2026-10-17
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** docs/notes.md · docs/reports/rh-current-frontier-map.md
- **Statement:** Unconditional Lean 4 formalization of the three structural advances in `docs/notes.md`: (1) `CHMD` secondary odd-$m_a$ Doob collar absorption, prime-chain variance bridge, and reflected collar compensation (`CHMDOddProfileArchAbsorptionAndPrimeChainBridge.lean`); (2) `HF` clamped / $S(F)$-free rational-resolvent first-cell quadrature bound and tail-cell ($n \ge 3$) variance localization (`MarkovClampedFirstCellAndTailVarianceLocalizationPBAP.lean`); (3) `EWU` doubly polar-constrained smooth even prime-blind kinetic spectral gap ($S > 27 L$), pole-free Euler–Maclaurin conservation, and joint single-source mixture purification (`EvenSectorPolarBlindSpectralGapAndClampedQuadrature.lean`).

## Goal
Advance the three coupled bottlenecks identified in `docs/notes.md` toward a formal Lean 4 proof of the Riemann Hypothesis:
1. **Option 1 (`CHMD` Secondary Odd-$m_a$ Doob + Divisor-Chain Factorization):** Connect the odd ground profile factorization $f(x) = m_a(x) w(x) = \Theta(x) (\Psi_a(x) w(x))$ ($w$ even) in `CHMDOddHarmonicIdentityAndPolarDoobAbsorption.lean` to the complete divisor-chain variance factorization in `CHMDPrimeChainSourceFactorization.lean` and `CHMDReflectedPrimeSingularPart.lean`, proving the archimedean collar absorption integral, the exact algebraic identity between the $\Theta$-Doob collar killing density and the $m_a$-Doob pure Dirichlet collar jump, and convex gauge interpolation between the positive divisor-chain variances and the positive $+2\int_0^\infty m_a\sinh(x/2)w^2\,dx$ pole potential.
2. **Option 2 (`HF` Clamped High-Frequency $I_2(r)$ + Uncertainty Gap / Euler–Maclaurin Audit):** Replace the unbounded $r=0$ Taylor parabola $I_2(r) \ge -(7/480) r^2$ at high frequencies by exploiting the exact $(1/4+r^2)$ identity in `MarkovExactFirstCellCosLogIntegralAndTwentyThreeRatioPBAP.lean` to derive an $S(F)$-free rational-resolvent lower bound and a clamped two-regime bound $-\min((7/480)r^2, 91/100) \le I_2(r)$, and prove that under the exact Euler–Maclaurin conservation law on the primitive prime-blind cone (`coshHalfMoment = 0`, `logVector = 0`), high-frequency kinetic oscillation is forced out of the $n=2$ cell into the tail cells $n \ge 3$.
3. **Option 3 (`EWU` + Clamped `HF` / Doubly Polar-Constrained Even Blind Spectral Gap):** Bridge `EWU` (`WeilEvenPolarTestFn` and `SmoothEvenPolarTestFn` in `PrimitiveHyperplaneBlindPositivity.lean`, `EvenSectorExactMomentRealization.lean`, and `EvenSectorBlindMinimumSmallAperturePositivity.lean`) with the `HF` Euler–Maclaurin conservation hierarchy by proving that every even polar test has `(weilPoleTerm k_g).re = 0`, yielding the exact pole-free conservation law `rightCellQuadratureDefect + bochnerResolventEnergy = 0`, the unconditional cutoff-free 27-ratio kinetic spectral gap $S(f) > 27 L(f)$ on every nonzero prime-blind smooth even polar test, and joint single-source mixture purification with `evenBlindMinimum` and clamped conservation.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorems compiled with `lake build --old` and `lake env lean`, wired into `RHTower.lean`, zero lint warnings/errors
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Formalized Modules & Main Theorems
1. **`formal/GaloisForLFunctions/RHTower/CHMDOddProfileArchAbsorptionAndPrimeChainBridge.lean`:**
   - `integral_oddProfileCollarDiffSq_eq_two_mul_half` & `integral_oddProfileShiftJump_eq_two_mul_Ioi_sub_two_mul_half`: midpoint reflection folding of the origin-crossing collar on $(0, t)$ onto $2 \times (0, t/2)$.
   - `integral_arch_direct_sub_collar_eq_absorbed` & `integral_arch_direct_sub_collar_nonneg`: exact integral absorption of the origin-crossing archimedean collar into the direct half-line jump via `absorbedArchIntegrand ≥ 0`.
   - `phiDoobTest_oddPolarWeight_eq_oddProfileTest`, `oddProfileTest_markovEnergy_eq_chain_variances_sub_cosh`, `oddPolarWeight_reflected_compensation_hasSum_chains`: exact gauge bridge `oddProfileTest a w = phiDoobTest (oddPolarWeight a w)` and complete divisor-chain variance decomposition for $f = m_a w$.
   - `collar_sumSq_add_oddProfile_diffSq_eq_mixed`, `phiDoobCollarSumSq_oddPolarWeight_add_oddProfileCollarDiffSq_eq`, `primeCrossing_oddPolarWeight_add_oddProfileCollar_eq_mixed`: universal origin-crossing collar duality $(\psi_1 w_1 + \psi_2 w_2)^2 + \psi_1 \psi_2 (w_1 - w_2)^2 = (\psi_1 + \psi_2)(\psi_1 w_1^2 + \psi_2 w_2^2)$.
   - `integral_oddProfileCollarDiffSq_eq_zero_of_symmetric`, `integral_oddProfileShiftJump_nonneg_of_collar_symmetric`, `convex_doob_chain_sinh_interpolation`.
2. **`formal/GaloisForLFunctions/RHTower/MarkovClampedFirstCellAndTailVarianceLocalizationPBAP.lean`:**
   - `neg_sqrt_two_mul_sin_sub_mul_one_sub_cos_le`, `neg_two_sqrt_two_sub_one_sub_resolvent_le_integral_one_two_cosLogProfile`, `neg_rational_sub_resolvent_le_integral_one_two_cosLogProfile`: exact sum-of-squares completion and global rational-resolvent lower bounds on $I_2(r)$ with zero $r^2$ growth.
   - `neg_ninety_one_hundredths_le_integral_one_two_cosLogProfile` & `neg_min_seven_four_eightieths_sq_ninety_one_hundredths_le_integral_one_two_cosLogProfile`: uniform bound $-91/100 \le I_2(r)$ and clamped two-regime bound $-\min((7/480)r^2, 91/100) \le I_2(r)$.
   - `neg_four_sqrt_two_sub_one_l2_sub_resolvent_le_integral_one_two`, `neg_rational_l2_sub_resolvent_le_integral_one_two`, `neg_ninety_one_fiftieths_l2_le_integral_one_two`, `neg_min_first_cell_le_integral_one_two`, `neg_clamped_first_cell_sub_seventy_one_geom_le_secantNumeratorCellDefect`.
   - `tail_cell_variance_localization_of_cosh_zero_of_logVector_eq_zero`, `clamped_all_ratio_conservation_bound_of_cosh_zero`, `clamped_all_ratio_markovEnergy_nonneg_of_sinh_sq_dominates`.
3. **`formal/GaloisForLFunctions/RHTower/EvenSectorPolarBlindSpectralGapAndClampedQuadrature.lean`:**
   - `exists_support_cutoff_weilTest`: automatic integer support-cutoff existence `2 ≤ N` for every `f : WeilTestFn`.
   - `WeilEvenPolarTestFn.unitStep_add_rightCellQuadratureDefect_add_bochnerResolventEnergy_eq_zero` & `WeilEvenPolarTestFn.rightCellQuadratureDefect_add_bochnerResolventEnergy_eq_zero_of_logVector_eq_zero`: exact pole-free Euler–Maclaurin conservation on `EWU`.
   - `WeilEvenPolarTestFn.fifty_one_halves_l2_lt_spectralSecondMoment_of_unitStep_nonneg`, `WeilEvenPolarTestFn.twenty_seven_l2_lt_spectralSecondMoment_of_logValue_nonneg`, `WeilEvenPolarTestFn.twenty_seven_l2_lt_spectralSecondMoment_of_logVector_eq_zero`, `SmoothEvenPolarTestFn.twenty_seven_l2_lt_spectralSecondMoment_of_logVector_eq_zero`: unconditional cutoff-free kinetic spectral gaps.
   - `WeilEvenPolarTestFn.clamped_all_ratio_conservation_bound_of_logVector_eq_zero`, `WeilEvenPolarTestFn.tail_cell_variance_localization_of_logVector_eq_zero`, `exists_single_smooth_blind_purification_with_clamped_conservation`.

## No-go closure (mandatory when falsified)
- **Exact killing theorem/mechanism:** In Option 2, `unitStep_add_rightCellQuadratureDefect_add_bochnerResolventEnergy_add_sinh_sq_eq_zero_of_cosh_zero` is an exact identity on `logVector F = 0`: the sum of the full right-cell quadrature defect, the Bochner resolvent energy, and $+2\operatorname{sinhHalfMoment}(f)^2$ is identically zero. Thus clamping $I_2(r)$ on the $n=2$ cell alone cannot make `rightCellQuadratureDefect + bochnerResolventEnergy + 2 sinhHalfMoment² > 0` on `logVector F = 0`.
- **Strongest positive survivor:** The exact $(1/4+r^2)$ resolvent division on the $n=2$ cell eliminates $S(F) = \int r^2|F(r)|^2\,dr$ completely from the first-cell lower bound, bounding $\int_1^2 \frac{C_f(x)-\operatorname{cellSecant}(C_f,2,x)}{\sqrt{x}}\,dx$ from below purely by $\|f\|_2^2$ and `bochnerResolventEnergy` (and via the clamped $\min((7/480)r^2, 91/100)$ law), which—combined with the conservation identity—forces all unbounded high-frequency defect into the tail cells $n \ge 3$ (`tail_cell_variance_localization_of_cosh_zero_of_logVector_eq_zero`).
- **New insight:** Separates the $O(1)$ bounded-symbol first-cell regime ($n=2$) from the Euler–Maclaurin tail ($n \ge 3$), and shows that on the doubly polar-constrained even sector (`EWU`), the pole term vanishes identically, transferring the entire 27-ratio kinetic spectral gap and clamped resolvent bounds unconditionally to `WeilEvenPolarTestFn` and `SmoothEvenPolarTestFn`.
- **Status:** Formalized in Lean 4 (`3-formalized`).

## Log
- 2026-10-17 — created in 1-in-progress
- 2026-10-17 — all three Lean 4 modules proved, compiled (`lake env lean` + `lake build --old`), wired into `RHTower.lean`, moved to 3-formalized
