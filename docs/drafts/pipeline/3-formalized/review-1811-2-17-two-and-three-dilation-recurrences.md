# Complete Resolution of the Two- and Three-Clock Prime-Error Dilation Recurrence Question (§2.17)

- **ID:** review-1811-2-17-two-and-three-dilation-recurrences
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean 4)
- **Source:** `docs/reports/review-1811/obstacles-summary.md` §2.17
- **Statement:** For $E(x) = \psi(x) - x$, $1/2 < \beta < 1$, $\gamma > 0$, and $a > 1$, let
  $$R_a(\beta, \gamma; x) = E(a^2 x) - 2 a^\beta \cos(\gamma \log a) E(a x) + a^{2\beta} E(x).$$
  Complete unconditional answer, exact pointwise and global characterizations on $\{2, 3\}$ and $\{2, 3, 5\}$, cross-sign aliasing and three-prime pigeonhole de-aliasing theorems, unconditional resolution zones, Lindelöf / finite-stratum dichotomy, cross-route corollaries (`ECS`, `HF`, `ZCG`, `ELT`), and model-realization firewalls in Lean 4.

## Summary of Verdicts & Unconditional Mathematical Solution

| Aspect | Final Verdict & Unconditional Mathematical Fact | Lean Module(s) | Status |
|---|---|---|---|
| **1. Hidden $(2, 3)$ cross-sign aliasing vs. $(2, 3, 5)$ pigeonhole de-aliasing** | **Two clocks $\{2, 3\}$ DO have a hidden cross-sign aliasing obstruction; three clocks $\{2, 3, 5\}$ eliminate it completely.** Because $R_a(\beta, \gamma)$ is a real second-order cosine operator with symbol $(1 - a^{\beta + i\gamma - s})(1 - a^{\beta - i\gamma - s})$, joint vanishing at $a \in \{2, 3\}$ requires $\cos(\omega \log 2) = \cos(\gamma \log 2)$ and $\cos(\omega \log 3) = \cos(\gamma \log 3)$. Same-sign branches $(\pm, \pm)$ force $\omega = \pm\gamma$ by $\log 2 / \log 3 \notin \mathbb{Q}$, **but** opposite-sign branches $(\pm, \mp)$ admit up to one distinct positive partner $\omega^* \ne \gamma$ (`isCrossResonantPair_unique`). By Dirichlet approximation (`dense_exists_isCrossResonantPair`), pairs $(\gamma, \omega^*)$ with $\omega^* > H$ (e.g. $H = 67$) are **dense in $(0, \infty)$**, and the planted two-frequency wave $f(x) = \operatorname{Re}(x^{\beta + i\gamma}) + \operatorname{Re}(x^{\beta + i\omega^*})$ satisfies $\limsup |f(x)|/x^\beta > 0$ and $D_2 f = D_3 f \equiv 0$ on $(0, \infty)$ while driving $|D_5 f(x)|/(\sqrt{x}\log^2 x)$ unbounded (`plantedAliasedDoubleWave_separates_two_and_three_clocks`). For any three distinct primes $\{p_1, p_2, p_3\}$ (in particular $\{2, 3, 5\}$), pigeonhole over $\{\pm 1\}^3$ forces $\omega = \pm\gamma$ everywhere on $[0, \infty)$ (`abs_eq_of_threePrime_cos_eq`). | `TwoClockDilationAliasingAndThreePrimePinning.lean` | formalized |
| **2. Exact pointwise & global answer on $\zeta$** | **REALIZED in every single-input model (planted waves, $\{0, 1, 2\}$-prime Beurling edits `sEdit` with integer norm count $c < 1/2$, over-regular Beurling $\zeta$, positive Euler twins); OPEN globally on $\zeta$ as the exact $(N_{\text{quartet}} = 1) \vee ((2, 3)\text{-aliased } N_{\text{quartet}} = 2)$ core of Obstacle B13.** Unconditionally on $\zeta$: (i) if $|R_a(\beta, \gamma; x)|/(\sqrt{x}\log^2 x)$ is bounded ($a > 1$), **every** zero $\rho \ne 1$ of $\zeta$ in $\{\operatorname{Re} s > 1/2\}$ satisfies $\operatorname{Re}\rho = \beta$ and $\cos(\operatorname{Im}\rho \cdot \log a) = \cos(\gamma \log a)$ (`re_eq_and_cos_im_eq_of_not_isSqrtLogSqUnbounded`); (ii) pointwise for $1/2 < \beta < 1$, $\gamma > 0$, $\limsup |E(x)|/x^\beta > 0$ with $R_2, R_3 = O(\sqrt{x}\log^2 x)$ holds **iff** `HasSingleOffLineQuartet (β + iγ)` holds, or $\gamma$ has a $(2, 3)$ cross-resonant partner $\omega > 67$ and either `HasSingleOffLineQuartet (β + iω)` or `HasTwoThreeAliasedQuartets β γ ω` holds (`twoClock_bounded_and_limsup_iff`); (iii) on $\{2, 3, 5\}$ for **all** $\gamma > 0$ (and on $\{2, 3\}$ whenever no cross-alias $> 67$ exists), it is unconditionally equivalent to `HasSingleOffLineQuartet (β + iγ)` (`threeClock_bounded_and_limsup_iff`, `twoClock_nonCrossResonant_iff_singleQuartet`); (iv) globally, `TwoClockPrimeRecurrenceLaw ↔ (∀ ρ₀, ¬ HasSingleOffLineQuartet ρ₀) ∧ (∀ β γ ω, ¬ HasTwoThreeAliasedQuartets β γ ω)` (`twoClockPrimeRecurrenceLaw_iff`), while `ThreeClockPrimeRecurrenceLaw ↔ ∀ ρ₀, ¬ HasSingleOffLineQuartet ρ₀` (`threeClockPrimeRecurrenceLaw_iff`). | `TwoClockDilationAliasingAndThreePrimePinning.lean`, `TwoAndThreeDilationRecurrencesAndSingleQuartetStratum.lean` | formalized |
| **3. Unconditional resolution zones & Lindelöf dichotomy** | **Proved unconditionally across four regimes on $\zeta$:** (i) for all $\beta > 20999/24000$, $\Theta \le 20999/24000 < \beta$ gives $\limsup |E(x)|/x^\beta = 0$ (`not_hasPositivePowerLimsup_of_sub_seven_eighths_lt`, `twoClock_unbounded_of_sub_seven_eighths_lt`); (ii) for all $1/2 < \beta < \text{zeroReSup}$, $\limsup |E(x)|/x^\beta > 0$ **and** $|R_a(\beta, \gamma; x)|/(\sqrt{x}\log^2 x)$ is unbounded for **every** $a > 1$, hence for **both** $a = 2$ and $a = 3$ (`hasPositivePowerLimsup_and_all_clocks_unbounded_of_lt_zeroReSup`); (iii) by `rhVerifiedThrough_sixtySeven`, every off-line zero has $|\operatorname{Im}\rho| > 67$ (`sixtySeven_lt_abs_im_of_offLine_zeta_zero`), resolving all $0 < \gamma \le 67$ on $\{2, 3, 5\}$ (`threeClock_unbounded_of_le_sixtySeven`) and all $0 < \gamma \le 67$ without a $> 67$ cross-alias on $\{2, 3\}$ (`twoClock_unbounded_of_le_sixtySeven`); (iv) any failure of `FiniteOffLine`, `ZerosApproachLine`, or `LindelofCriticalLine` forces `TwoClockPrimeRecurrenceLaw` globally (`twoClockPrimeRecurrenceLaw_of_not_finiteOffLine`, `twoClockPrimeRecurrenceLaw_of_not_lindelof`, `twoClockPrimeRecurrenceLaw_or_lindelof_finite_stratum`). | `TwoClockDilationAliasingAndThreePrimePinning.lean`, `TwoAndThreeDilationRecurrencesAndSingleQuartetStratum.lean` | formalized |
| **4. Cross-route corollaries & model firewall** | `TwoClockPrimeRecurrenceLaw` (and `ThreeClockPrimeRecurrenceLaw`) unconditionally implies: (i) `∀ ρ₀, ¬ HasSingleOffLineQuartet ρ₀` at arbitrary divisor multiplicity $m \ge 1$; (ii) $\mathrm{RH} \vee 4 \le \#Z_{\text{right}}$ and `realPacketNegIndex ≠ 2`; (iii) under $\neg\mathrm{RH}$, existence of $(R, S, H)$ with $3 \le \operatorname{hermNegIndex}(\text{confinedGram } R\ H)$ (eliminating the two-rung confined critical-state ladder in `ECS` / `HF`); (iv) cofinal odd primes $2t + 1$ excluding single-wave adjacent Vaughan cofactor errors (`corollaries_of_threeClockPrimeRecurrenceLaw`, `corollaries_of_twoClockPrimeRecurrenceLaw`); while single-input models violate it whenever either $\Lambda \ge 0$ or the $\Gamma_{\mathbb{R}}$ functional equation is dropped (`model_firewall_for_two_and_three_clocks`). | `TwoAndThreeDilationRecurrencesAndSingleQuartetStratum.lean` | formalized |

## Formalized Declarations

### `GaloisForLFunctions.ZeroConfigurationGeometry` (`ZeroConfigurationGeometry/TwoClockDilationAliasingAndThreePrimePinning.lean`)
- `primeError`, `dilationRecurrenceOp`, `primeDilationResidual`
- `HasPositivePowerLimsup`, `IsSqrtLogSqUnbounded`
- `hasPositivePowerLimsup_iff_limsup_pos`, `isSqrtLogSqUnbounded_iff_not_eventually_le`
- `natDegree_dilationPairPoly`, `dilationSetOp_singleton_apply`, `dilationSetOp_singleton_sq_mul`
- `primeDilationResidual_eq_dilationSetOp`
- `dilationRecurrenceOp_re_cpow_eq`, `dilationRecurrenceOp_re_cpow_eq_zero`
- `abs_dilationRecurrenceOp_le_of_sqrt_log_sq`
- `cos_eq_cos_iff_exists_int`, `cos_mul_log_eq_iff`
- `re_eq_and_cos_im_eq_of_not_isSqrtLogSqUnbounded`
- `IsCrossResonantPair`, `isCrossResonantPair_unique`, `abs_eq_or_isCrossResonantPair_of_twoPrime_cos_eq`
- `dense_exists_isCrossResonantPair`
- `abs_eq_of_threePrime_cos_eq`
- `plantedAliasedDoubleWave_separates_two_and_three_clocks`
- `not_hasPositivePowerLimsup_of_zeroReSup_lt`, `zeroReSup_le_sub_seven_eighths`, `not_hasPositivePowerLimsup_of_sub_seven_eighths_lt`
- `twoClock_unbounded_of_sub_seven_eighths_lt`
- `hasPositivePowerLimsup_and_all_clocks_unbounded_of_lt_zeroReSup`
- `sixtySeven_lt_abs_im_of_offLine_zeta_zero`
- `threeClock_unbounded_of_le_sixtySeven`, `twoClock_unbounded_of_le_sixtySeven`

### `GaloisForLFunctions.ExceptionalLayerTheory` (`ExceptionalLayerTheory/TwoAndThreeDilationRecurrencesAndSingleQuartetStratum.lean`)
- `HasTwoThreeAliasedQuartets`, `TwoClockPrimeRecurrenceLaw`, `ThreeClockPrimeRecurrenceLaw`
- `not_isSqrtLogSqUnbounded_of_finite_and_cos_eq`, `hasPositivePowerLimsup_of_finite_and_top_zero`
- `singleQuartet_obeys_all_dilation_recurrences`
- `HasTwoThreeAliasedQuartets.finiteOffLine_copies`, `HasTwoThreeAliasedQuartets.finiteOffLine`
- `lindelof_all_forms_of_twoThreeAliasedQuartets`
- `twoThreeAliasedQuartets_obey_two_and_three_not_five`
- `twoClock_bounded_and_limsup_iff`, `twoClock_nonCrossResonant_iff_singleQuartet`
- `threeClock_bounded_and_limsup_iff`
- `twoClockPrimeRecurrenceLaw_iff`, `threeClockPrimeRecurrenceLaw_iff`, `threeClockPrimeRecurrenceLaw_of_twoClock`
- `twoClockPrimeRecurrenceLaw_of_not_finiteOffLine`, `twoClockPrimeRecurrenceLaw_of_not_zerosApproachLine`
- `twoClockPrimeRecurrenceLaw_of_not_lindelof`, `twoClockPrimeRecurrenceLaw_of_riemannHypothesis`
- `twoClockPrimeRecurrenceLaw_or_lindelof_finite_stratum`
- `corollaries_of_threeClockPrimeRecurrenceLaw`, `corollaries_of_twoClockPrimeRecurrenceLaw`
- `model_firewall_for_two_and_three_clocks`

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven
- [x] 2 → 3  formalized and verified via `lake --old env lean`
