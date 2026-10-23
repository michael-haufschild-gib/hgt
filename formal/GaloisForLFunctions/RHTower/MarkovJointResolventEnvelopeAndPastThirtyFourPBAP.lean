import GaloisForLFunctions.RHTower.EvenSectorPolarBlindSpectralGapAndClampedQuadrature

/-!
# The Joint First-Cell Cosine-Log + Resolvent Envelope, Coercivity & Spectral Gap Laws up to `33` and `69 / 2 = 34.5`, Exact Vanishing of Prime-Blind Tail Secants (`n ≥ 3`), and Arbitrary-`M` `O(M^{-3/2})` Far-Tail Variance Localization for Route HF / PBAP

In `MarkovDegreeSixteenFirstCellAndTwentySevenRatioPBAP` and
`EvenSectorPolarBlindSpectralGapAndClampedQuadrature`, the first-cell cosine-log quadrature integral
$$I_2(r) = \int_1^2 \frac{\cos(r\log x) - \operatorname{cellSecant}(\cos(r\log\cdot), 2, x)}{\sqrt{x}}\,dx$$
and the Bochner–Poisson resolvent kernel $\frac{1/2}{1/4 + r^2}$ were bounded separately:
$-I_2(r) \le \frac{7}{480} r^2$ (tight only near $r^2 \approx 50$) and
$-\frac{1/2}{1/4 + r^2} \le -2t + 2t^2(r^2 + 1/4)$ (tight near $r^2 \approx 13.5$). Because $-I_2(r)$ is
strictly negative on $(0, 14.85)$ (reaching $-0.345$ near $r^2 \approx 6.8$), bounding the two terms
separately discarded the low-frequency concavity surplus of $I_2(r)$, limiting the critical kinetic
ratio to $S / L \le 51 / 2 = 25.5$ on the general cone and $S / L \le 27$ on the nonnegative
log-value and prime-blind cones.

In this module, we exploit the fact that $I_2(r)$ and the Bochner–Poisson resolvent share the
**exact same denominator $(1/4 + r^2)$**, and we combine this joint spectral envelope with exact
tail-secant vanishing and arbitrary-$M$ far-tail localization:

1. **Section 1 (The Joint First-Cell Cosine-Log + Resolvent Envelope and the Symmetric `71 / 3600`
   Resolvent + Secant Numerator Law):**
   - For **every** frequency $r \in \mathbb{R}$, the combined numerator of $I_2(r) + \frac{1/2}{1/4 + r^2}$
     satisfies (`neg_mul_integral_one_two_cosLogProfile_sub_half_le_joint_resolvent` and
     `joint_resolvent_envelope_le_integral_one_two_cosLogProfile`):
     $$\forall r \in \mathbb{R},\qquad
       -\frac{71}{3600} r^2 + \frac{91}{360} - \frac{1/2}{1/4 + r^2} \le I_2(r).$$
   - Integrating against $\frac{1}{2\pi}\|F(r)\|^2 \cdot 2$ proves the **Joint First-Cell + Resolvent
     Spectral Inequality** (`ninety_one_one_eightieths_l2_sub_seventy_one_second_le_bochnerResolventEnergy_add_integral_one_two`):
     $$\frac{91}{180}\int \|f.1\|^2 - \frac{71}{3600}\operatorname{spectralSecondMoment}(f.1)
       \le \operatorname{bochnerResolventEnergy}(k_f)
         + \int_1^2 \frac{C_f(x) - \operatorname{cellSecant}(C_f, 2, x)}{\sqrt{x}}\,dx,$$
     and combining with the Quintic Chebyshev tail bound on $n \in [3, N]$ yields the **Symmetric
     `71 / 3600` Resolvent + Secant Numerator Law**
     (`ninety_one_one_eightieths_l2_sub_seventy_one_second_add_geom_le_bochnerResolventEnergy_add_secantNumeratorCellDefect`):
     $$\frac{91}{180} L - \frac{71}{3600}\Bigl(S + \sqrt{S(S + 2L)}\Bigr)
       \le \operatorname{bochnerResolventEnergy}(k_f) + \operatorname{secantNumeratorCellDefect}(f.1, N).$$

2. **Section 2 (Coercivity, Unconditional `0 ≤ markovEnergy`, and Cutoff-Free `EWU` Spectral Gaps
   up to `33` and `69 / 2 = 34.5`, Deep into the `S / L > 27` Regime):**
   - Combining the Symmetric `71 / 3600` Resolvent + Secant Numerator Law with the Four-Stage
     Secular Counterterm Surplus (`247 / 300` general, `1261 / 1440` nonnegative log-value /
     prime-blind) and the tangent envelope $\sqrt{S(S + 2L)} \le \frac{2313}{2312} S + \frac{34}{35} L$
     upgrades:
     - **General Cone Coercivity, Unconditional `0 ≤ markovEnergy F` on `coshHalfMoment f = 0`, and
       Spectral Gap Laws** from $S / L \le 51 / 2 = 25.5$ to **$S / L \le 33$**
       (`one_one_fiftieth_l2_le_bochnerResolventEnergy_add_rightCellQuadratureDefect_of_spectralSecondMoment_le_thirty_three`,
       `markovEnergy_ofReal_nonneg_of_spectralSecondMoment_le_thirty_three_of_cosh_zero`,
       `thirty_three_l2_lt_spectralSecondMoment_of_cosh_zero_of_unitStep_nonneg`,
       `WeilEvenPolarTestFn.thirty_three_l2_lt_spectralSecondMoment_of_unitStep_nonneg`).
     - **Nonnegative Log-Value Cone & Prime-Blind Cone (`logVector f = 0`) Coercivity, Unconditional
       `0 ≤ markovEnergy F`, and Cutoff-Free `EWU` Spectral Gap Laws** from $S / L \le 27$ to
       **$S / L \le 69 / 2 = 34.5$** (`> 27` by $+7.5$ full units!)
       (`one_twelve_hundredth_l2_le_bochnerResolventEnergy_add_rightCellQuadratureDefect_of_spectralSecondMoment_le_sixty_nine_halves_of_logValue_nonneg`,
       `one_twelve_hundredth_l2_le_bochnerResolventEnergy_add_rightCellQuadratureDefect_of_spectralSecondMoment_le_sixty_nine_halves_of_logVector_eq_zero`,
       `markovEnergy_ofReal_nonneg_of_spectralSecondMoment_le_sixty_nine_halves_of_cosh_zero_of_logValue_nonneg`,
       `sixty_nine_halves_l2_lt_spectralSecondMoment_of_cosh_zero_of_logValue_nonneg`,
       `sixty_nine_halves_l2_lt_spectralSecondMoment_of_cosh_zero_of_logVector_eq_zero`,
       `WeilEvenPolarTestFn.sixty_nine_halves_l2_lt_spectralSecondMoment_of_logVector_eq_zero`,
       `SmoothEvenPolarTestFn.sixty_nine_halves_l2_lt_spectralSecondMoment_of_logVector_eq_zero`,
       `exists_single_smooth_blind_purification_with_thirty_four_point_five_gap`).

3. **Section 3 (Exact Vanishing of Prime-Blind Tail Secants for `n ≥ 3`, `S(f)`-Free Multi-Cell
   Physical-Space Clamping on `[2, M]`, and Arbitrary-`M` `O(M^{-3/2})` Far-Tail Variance Localization):**
   - For every prime-blind `f : WeilTestFn` (`logVector f = 0`), `weilSymmetricLogNumerator f.1 (n : ℝ) = 0`
     for all $n \ge 2$, so for every tail cell $n \ge 3$ and all $x \in \mathbb{R}$,
     `cellSecant (weilSymmetricLogNumerator f.1) n x = 0` identically
     (`cellSecant_weilSymmetricLogNumerator_eq_zero_of_logVector_eq_zero`)!
   - Consequently, on every tail cell $n \ge 3$, the prime-blind cell integral is bounded below
     without $S(f)$ by $-4(\sqrt{n} - \sqrt{n - 1}) L$ (twice as sharp as the general $-8(\sqrt{n} - \sqrt{n - 1}) L$
     bound), telescoping over $n \in [3, M]$ ($M \ge 2$) to $-4(\sqrt{M} - \sqrt{2}) L$
     (`neg_four_mul_sqrt_sub_sqrt_two_l2_le_sum_Icc_three_of_logVector_eq_zero`).
   - For every $M \ge 4$ and $N \in \mathbb{N}$, the Quintic Chebyshev weights on the far tail
     $n \in \operatorname{Finset.Icc} (M + 1) N$ telescope to
     $$\sum_{n=M+1}^N \operatorname{hermiteQuinticCellWeight}(n)
       \le \frac{811}{14580 M \sqrt{M}} = O(M^{-3/2})$$
     (`sum_Icc_succ_hermiteQuinticCellWeight_le`), yielding the **Arbitrary-`M` `O(M^{-3/2})` Far-Tail
     Geometric-Mean Law** (`neg_far_tail_geom_le_sum_Icc_succ`) and the **Multi-Cell Clamped All-Ratio
     Conservation Law** (`multi_cell_clamped_conservation_bound_of_logVector_eq_zero`).
-/

open Complex MeasureTheory Filter Topology Set Finsupp
open scoped Real ComplexConjugate ContDiff FourierTransform BigOperators
open Zeta23
open GaloisForLFunctions.RHTower
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

open WeilOneSided WeilSpectral WeilLevyPole WeilLevyPoleGauss WeilLevyCoshCrossover LebesgueAtomWeil
open RHTower.NonnegativeCone EvenSector

/-! ## Section 1: The Joint First-Cell Cosine-Log + Resolvent Envelope and the Symmetric `71 / 3600` Resolvent + Secant Numerator Law -/

/-- Sum-of-squares polynomial inequality on `0 ≤ u ≤ 10` for the joint first-cell + resolvent
envelope:
`u * (c0 + c1 * u + ... + c8 * u ^ 8) - 1 / 2 ≤ ((71 / 3600) * u - 91 / 360) * (1 / 4 + u)`. -/
lemma first_cell_poly_of_coeffs_joint_low {c0 c1 c2 c3 c4 c5 c6 c7 c8 u : ℝ}
    (hc0 : c0 ≤ -5415 / 1000000) (hc1 : c1 ≤ -21160 / 1000000)
    (hc2 : c2 ≤ 19647 / 10000000) (hc3 : c3 ≤ -39380 / 1000000000)
    (hc4 : c4 ≤ 37740 / 100000000000) (hc5 : c5 ≤ -21409 / 10000000000000)
    (hc6 : c6 ≤ 8140 / 1000000000000000) (hc7 : c7 ≤ -2201 / 100000000000000000)
    (hc8 : c8 ≤ 531 / 10000000000000000000)
    (hu_nonneg : 0 ≤ u) (hr : u ≤ 10) :
    u * (c0 + c1 * u + c2 * u ^ 2 + c3 * u ^ 3 + c4 * u ^ 4 +
        c5 * u ^ 5 + c6 * u ^ 6 + c7 * u ^ 7 + c8 * u ^ 8) - 1 / 2 ≤
      ((71 / 3600) * u - 91 / 360) * (1 / 4 + u) := by
  have hm0 := mul_le_mul_of_nonneg_right hc0 hu_nonneg
  have hm1 := mul_le_mul_of_nonneg_right hc1 (sq_nonneg u)
  have hm2 := mul_le_mul_of_nonneg_right hc2 (by positivity : 0 ≤ u ^ 3)
  have hm3 := mul_le_mul_of_nonneg_right hc3 (by positivity : 0 ≤ u ^ 4)
  have hm4 := mul_le_mul_of_nonneg_right hc4 (by positivity : 0 ≤ u ^ 5)
  have hm5 := mul_le_mul_of_nonneg_right hc5 (by positivity : 0 ≤ u ^ 6)
  have hm6 := mul_le_mul_of_nonneg_right hc6 (by positivity : 0 ≤ u ^ 7)
  have hm7 := mul_le_mul_of_nonneg_right hc7 (by positivity : 0 ≤ u ^ 8)
  have hm8 := mul_le_mul_of_nonneg_right hc8 (by positivity : 0 ≤ u ^ 9)
  have hb9 : 0 ≤ 10 * u ^ 8 - u ^ 9 := by
    rw [show 10 * u ^ 8 - u ^ 9 = u ^ 8 * (10 - u) by ring]
    exact mul_nonneg (by positivity) (by linarith)
  have hb8 : 0 ≤ u ^ 8 := by positivity
  have hb7 : 0 ≤ 10 * u ^ 6 - u ^ 7 := by
    rw [show 10 * u ^ 6 - u ^ 7 = u ^ 6 * (10 - u) by ring]
    exact mul_nonneg (by positivity) (by linarith)
  have hb6 : 0 ≤ u ^ 6 := by positivity
  have hb5 : 0 ≤ 10 * u ^ 4 - u ^ 5 := by
    rw [show 10 * u ^ 4 - u ^ 5 = u ^ 4 * (10 - u) by ring]
    exact mul_nonneg (by positivity) (by linarith)
  have hb4 : 0 ≤ u ^ 4 - 8 * u ^ 3 + 16 * u ^ 2 := by
    rw [show u ^ 4 - 8 * u ^ 3 + 16 * u ^ 2 = u ^ 2 * (u - 4) ^ 2 by ring]
    positivity
  have hb3 : 0 ≤ -u ^ 3 + 18 * u ^ 2 - 96 * u + 160 := by
    rw [show -u ^ 3 + 18 * u ^ 2 - 96 * u + 160 = (10 - u) * (u - 4) ^ 2 by ring]
    exact mul_nonneg (by linarith) (sq_nonneg _)
  have hb2 : 0 ≤ u ^ 2 - 8 * u + 16 := by
    rw [show u ^ 2 - 8 * u + 16 = (u - 4) ^ 2 by ring]
    positivity
  have hexp :
      u * (c0 + c1 * u + c2 * u ^ 2 + c3 * u ^ 3 + c4 * u ^ 4 +
        c5 * u ^ 5 + c6 * u ^ 6 + c7 * u ^ 7 + c8 * u ^ 8) =
      c0 * u + c1 * u ^ 2 + c2 * u ^ 3 + c3 * u ^ 4 + c4 * u ^ 5 +
        c5 * u ^ 6 + c6 * u ^ 7 + c7 * u ^ 8 + c8 * u ^ 9 := by ring
  have hrhs :
      ((71 / 3600) * u - 91 / 360) * (1 / 4 + u) =
        (71 / 3600) * u ^ 2 - (3569 / 14400) * u - 91 / 1440 := by ring
  linarith only [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8,
    hb9, hb8, hb7, hb6, hb5, hb4, hb3, hb2, hexp, hrhs, hu_nonneg, hr]

/-- Sum-of-squares polynomial inequality on `10 ≤ u ≤ 49` bounding `P(u) ≤ (4979 / 256000) * u - 6509 / 28800`,
which is the tangent line to `(((71 / 3600) * u - 91 / 360) * (1 / 4 + u) + 1 / 2) / u` at `u = 40`. -/
lemma first_cell_poly_of_coeffs_joint_mid {c0 c1 c2 c3 c4 c5 c6 c7 c8 u : ℝ}
    (hc0 : c0 ≤ -5415 / 1000000) (hc1 : c1 ≤ -21160 / 1000000)
    (hc2 : c2 ≤ 19647 / 10000000) (hc3 : c3 ≤ -39380 / 1000000000)
    (hc4 : c4 ≤ 37740 / 100000000000) (hc5 : c5 ≤ -21409 / 10000000000000)
    (hc6 : c6 ≤ 8140 / 1000000000000000) (hc7 : c7 ≤ -2201 / 100000000000000000)
    (hc8 : c8 ≤ 531 / 10000000000000000000)
    (hr_low : 10 ≤ u) (hr_high : u ≤ 49) :
    u * (c0 + c1 * u + c2 * u ^ 2 + c3 * u ^ 3 + c4 * u ^ 4 +
        c5 * u ^ 5 + c6 * u ^ 6 + c7 * u ^ 7 + c8 * u ^ 8) - 1 / 2 ≤
      ((71 / 3600) * u - 91 / 360) * (1 / 4 + u) := by
  have hu_nonneg : 0 ≤ u := by linarith
  have hm1 := mul_le_mul_of_nonneg_right hc1 hu_nonneg
  have hm2 := mul_le_mul_of_nonneg_right hc2 (sq_nonneg u)
  have hm3 := mul_le_mul_of_nonneg_right hc3 (by positivity : 0 ≤ u ^ 3)
  have hm4 := mul_le_mul_of_nonneg_right hc4 (by positivity : 0 ≤ u ^ 4)
  have hm5 := mul_le_mul_of_nonneg_right hc5 (by positivity : 0 ≤ u ^ 5)
  have hm6 := mul_le_mul_of_nonneg_right hc6 (by positivity : 0 ≤ u ^ 6)
  have hm7 := mul_le_mul_of_nonneg_right hc7 (by positivity : 0 ≤ u ^ 7)
  have hm8 := mul_le_mul_of_nonneg_right hc8 (by positivity : 0 ≤ u ^ 8)
  have hb8 : 0 ≤ -u ^ 8 + 133 * u ^ 7 - 5880 * u ^ 6 + 86436 * u ^ 5 := by
    rw [show -u ^ 8 + 133 * u ^ 7 - 5880 * u ^ 6 + 86436 * u ^ 5 =
      u ^ 5 * (49 - u) * (u - 42) ^ 2 by ring]
    exact mul_nonneg (mul_nonneg (by positivity) (by linarith)) (sq_nonneg _)
  have hb7 : 0 ≤ u ^ 7 - 84 * u ^ 6 + 1764 * u ^ 5 := by
    rw [show u ^ 7 - 84 * u ^ 6 + 1764 * u ^ 5 = u ^ 5 * (u - 42) ^ 2 by ring]
    positivity
  have hb6 : 0 ≤ -u ^ 6 + 133 * u ^ 5 - 5880 * u ^ 4 + 86436 * u ^ 3 := by
    rw [show -u ^ 6 + 133 * u ^ 5 - 5880 * u ^ 4 + 86436 * u ^ 3 =
      u ^ 3 * (49 - u) * (u - 42) ^ 2 by ring]
    exact mul_nonneg (mul_nonneg (by positivity) (by linarith)) (sq_nonneg _)
  have hb5 : 0 ≤ u ^ 5 - 84 * u ^ 4 + 1764 * u ^ 3 := by
    rw [show u ^ 5 - 84 * u ^ 4 + 1764 * u ^ 3 = u ^ 3 * (u - 42) ^ 2 by ring]
    positivity
  have hb4 : 0 ≤ -u ^ 4 + 143 * u ^ 3 - 7210 * u ^ 2 + 145236 * u - 864360 := by
    rw [show -u ^ 4 + 143 * u ^ 3 - 7210 * u ^ 2 + 145236 * u - 864360 =
      (u - 10) * (49 - u) * (u - 42) ^ 2 by ring]
    exact mul_nonneg (mul_nonneg (by linarith) (by linarith)) (sq_nonneg _)
  have hb3 : 0 ≤ u ^ 3 - 94 * u ^ 2 + 2604 * u - 17640 := by
    rw [show u ^ 3 - 94 * u ^ 2 + 2604 * u - 17640 =
      (u - 10) * (u - 42) ^ 2 by ring]
    exact mul_nonneg (by linarith) (sq_nonneg _)
  have hb2 : 0 ≤ u ^ 2 - 98 * u + 2401 := by
    rw [show u ^ 2 - 98 * u + 2401 = (u - 49) ^ 2 by ring]
    positivity
  have hP_le :
      c0 + c1 * u + c2 * u ^ 2 + c3 * u ^ 3 + c4 * u ^ 4 +
        c5 * u ^ 5 + c6 * u ^ 6 + c7 * u ^ 7 + c8 * u ^ 8 ≤
      (4979 / 256000) * u - 6509 / 28800 := by
    linarith only [hc0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8,
      hb8, hb7, hb6, hb5, hb4, hb3, hb2, hr_low, hr_high]
  have huP := mul_le_mul_of_nonneg_left hP_le hu_nonneg
  have htan :
      ((71 / 3600) * u - 91 / 360) * (1 / 4 + u) -
        (u * ((4979 / 256000) * u - 6509 / 28800) - 1 / 2) =
      (629 / 2304000) * (u - 40) ^ 2 := by ring
  have hsq_nn : 0 ≤ (629 / 2304000 : ℝ) * (u - 40) ^ 2 := by positivity
  linarith

/-- **Degree-16 Polynomial Taylor Bound for the Joint First-Cell + Resolvent Envelope (`0 ≤ u ≤ 49`)**. -/
theorem first_cell_taylor_poly_le_joint_resolvent {ℓ s2 u : ℝ}
    (hℓ_low : 693146 / 1000000 ≤ ℓ) (hℓ_high : ℓ ≤ 693148 / 1000000)
    (hs2_low : 47321 / 33461 ≤ s2) (hs2_high : s2 ≤ 114243 / 80782)
    (hu_nonneg : 0 ≤ u) (hr : u ≤ 49) :
    u * ((2 * (s2 - 1) - s2 * ℓ + (2 * s2 - 1) / 6 * ℓ ^ 2) +
      (s2 * ℓ ^ 3 / 6 - (2 * s2 - 1) / 72 * ℓ ^ 4 - (4 - 2 * s2) / 6 * ℓ ^ 2) * u +
      (-s2 * ℓ ^ 5 / 120 + (2 * s2 - 1) / 2160 * ℓ ^ 6 + (4 - 2 * s2) / 72 * ℓ ^ 4) * u ^ 2 +
      (s2 * ℓ ^ 7 / 5040 - (4 - 2 * s2) / 2160 * ℓ ^ 6 -
        (2 * s2 - 1) / 120960 * ℓ ^ 8) * u ^ 3 +
      (-s2 * ℓ ^ 9 / 362880 + (4 - 2 * s2) / 120960 * ℓ ^ 8 +
        (2 * s2 - 1) / 10886400 * ℓ ^ 10) * u ^ 4 +
      (s2 * ℓ ^ 11 / 39916800 - (4 - 2 * s2) / 10886400 * ℓ ^ 10 -
        (2 * s2 - 1) / 1437004800 * ℓ ^ 12) * u ^ 5 +
      (-s2 * ℓ ^ 13 / 6227020800 + (4 - 2 * s2) / 1437004800 * ℓ ^ 12 +
        (2 * s2 - 1) / 261534873600 * ℓ ^ 14) * u ^ 6 +
      (s2 * ℓ ^ 15 / 1307674368000 - (4 - 2 * s2) / 261534873600 * ℓ ^ 14) * u ^ 7 +
      ((4 - 2 * s2) / 62768369664000 * ℓ ^ 16) * u ^ 8) - 1 / 2 ≤
    ((71 / 3600) * u - 91 / 360) * (1 / 4 + u) := by
  have hℓ0 : 0 ≤ ℓ := by linarith only [hℓ_low]
  have hs2_0 : 0 ≤ s2 := by linarith only [hs2_low]
  have hℓ1_1 : (693146 / 1000000 : ℝ) ≤ ℓ := hℓ_low
  have hℓ1_2 : ℓ ≤ 693148 / 1000000 := hℓ_high
  have hℓ2_1 : (480451 / 1000000 : ℝ) ≤ ℓ ^ 2 :=
    le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hℓ1_1 2)
  have hℓ2_2 : ℓ ^ 2 ≤ 480455 / 1000000 :=
    le_trans (pow_le_pow_left₀ hℓ0 hℓ1_2 2) (by norm_num)
  have hℓ3_1 : (333022 / 1000000 : ℝ) ≤ ℓ ^ 3 := by
    rw [show ℓ ^ 3 = ℓ ^ 2 * ℓ by ring]
    exact le_trans (by norm_num) (mul_le_mul hℓ2_1 hℓ1_1 (by norm_num) (sq_nonneg ℓ))
  have hℓ3_2 : ℓ ^ 3 ≤ 333027 / 1000000 := by
    rw [show ℓ ^ 3 = ℓ ^ 2 * ℓ by ring]
    exact le_trans (mul_le_mul hℓ2_2 hℓ1_2 hℓ0 (by norm_num)) (by norm_num)
  have hℓ4_1 : (230833 / 1000000 : ℝ) ≤ ℓ ^ 4 := by
    rw [show ℓ ^ 4 = ℓ ^ 2 * ℓ ^ 2 by ring]
    exact le_trans (by norm_num) (mul_le_mul hℓ2_1 hℓ2_1 (by norm_num) (sq_nonneg ℓ))
  have hℓ4_2 : ℓ ^ 4 ≤ 230838 / 1000000 := by
    rw [show ℓ ^ 4 = ℓ ^ 2 * ℓ ^ 2 by ring]
    exact le_trans (mul_le_mul hℓ2_2 hℓ2_2 (sq_nonneg ℓ) (by norm_num)) (by norm_num)
  have hℓ5_1 : (159999 / 1000000 : ℝ) ≤ ℓ ^ 5 := by
    rw [show ℓ ^ 5 = ℓ ^ 4 * ℓ by ring]
    exact le_trans (by norm_num) (mul_le_mul hℓ4_1 hℓ1_1 (by norm_num) (by positivity))
  have hℓ6_1 : (110903 / 1000000 : ℝ) ≤ ℓ ^ 6 := by
    rw [show ℓ ^ 6 = ℓ ^ 3 * ℓ ^ 3 by ring]
    exact le_trans (by norm_num) (mul_le_mul hℓ3_1 hℓ3_1 (by norm_num) (by positivity))
  have hℓ6_2 : ℓ ^ 6 ≤ 110907 / 1000000 := by
    rw [show ℓ ^ 6 = ℓ ^ 3 * ℓ ^ 3 by ring]
    exact le_trans (mul_le_mul hℓ3_2 hℓ3_2 (by positivity) (by norm_num)) (by norm_num)
  have hℓ7_2 : ℓ ^ 7 ≤ 76875 / 1000000 := by
    rw [show ℓ ^ 7 = ℓ ^ 6 * ℓ by ring]
    exact le_trans (mul_le_mul hℓ6_2 hℓ1_2 hℓ0 (by norm_num)) (by norm_num)
  have hℓ8_1 : (53283 / 1000000 : ℝ) ≤ ℓ ^ 8 := by
    rw [show ℓ ^ 8 = ℓ ^ 4 * ℓ ^ 4 by ring]
    exact le_trans (by norm_num) (mul_le_mul hℓ4_1 hℓ4_1 (by norm_num) (by positivity))
  have hℓ8_2 : ℓ ^ 8 ≤ 53286 / 1000000 := by
    rw [show ℓ ^ 8 = ℓ ^ 2 * ℓ ^ 6 by ring]
    exact le_trans (mul_le_mul hℓ2_2 hℓ6_2 (by positivity) (by norm_num)) (by norm_num)
  have hℓ9_1 : (36932 / 1000000 : ℝ) ≤ ℓ ^ 9 := by
    rw [show ℓ ^ 9 = ℓ ^ 8 * ℓ by ring]
    exact le_trans (by norm_num) (mul_le_mul hℓ8_1 hℓ1_1 (by norm_num) (by positivity))
  have hℓ10_1 : (25599 / 1000000 : ℝ) ≤ ℓ ^ 10 := by
    rw [show ℓ ^ 10 = ℓ ^ 5 * ℓ ^ 5 by ring]
    exact le_trans (by norm_num) (mul_le_mul hℓ5_1 hℓ5_1 (by norm_num) (by positivity))
  have hℓ10_2 : ℓ ^ 10 ≤ 25602 / 1000000 := by
    rw [show ℓ ^ 10 = ℓ ^ 4 * ℓ ^ 6 by ring]
    exact le_trans (mul_le_mul hℓ4_2 hℓ6_2 (by positivity) (by norm_num)) (by norm_num)
  have hℓ11_2 : ℓ ^ 11 ≤ 17746 / 1000000 := by
    rw [show ℓ ^ 11 = ℓ ^ 10 * ℓ by ring]
    exact le_trans (mul_le_mul hℓ10_2 hℓ1_2 hℓ0 (by norm_num)) (by norm_num)
  have hℓ12_1 : (12299 / 1000000 : ℝ) ≤ ℓ ^ 12 := by
    rw [show ℓ ^ 12 = ℓ ^ 6 * ℓ ^ 6 by ring]
    exact le_trans (by norm_num) (mul_le_mul hℓ6_1 hℓ6_1 (by norm_num) (by positivity))
  have hℓ12_2 : ℓ ^ 12 ≤ 12301 / 1000000 := by
    rw [show ℓ ^ 12 = ℓ ^ 6 * ℓ ^ 6 by ring]
    exact le_trans (mul_le_mul hℓ6_2 hℓ6_2 (by positivity) (by norm_num)) (by norm_num)
  have hℓ13_1 : (8525 / 1000000 : ℝ) ≤ ℓ ^ 13 := by
    rw [show ℓ ^ 13 = ℓ ^ 12 * ℓ by ring]
    exact le_trans (by norm_num) (mul_le_mul hℓ12_1 hℓ1_1 (by norm_num) (by positivity))
  have hℓ14_1 : (5909 / 1000000 : ℝ) ≤ ℓ ^ 14 := by
    rw [show ℓ ^ 14 = ℓ ^ 12 * ℓ ^ 2 by ring]
    exact le_trans (by norm_num) (mul_le_mul hℓ12_1 hℓ2_1 (by norm_num) (by positivity))
  have hℓ14_2 : ℓ ^ 14 ≤ 5911 / 1000000 := by
    rw [show ℓ ^ 14 = ℓ ^ 12 * ℓ ^ 2 by ring]
    exact le_trans (mul_le_mul hℓ12_2 hℓ2_2 (sq_nonneg ℓ) (by norm_num)) (by norm_num)
  have hℓ15_2 : ℓ ^ 15 ≤ 4098 / 1000000 := by
    rw [show ℓ ^ 15 = ℓ ^ 14 * ℓ by ring]
    exact le_trans (mul_le_mul hℓ14_2 hℓ1_2 hℓ0 (by norm_num)) (by norm_num)
  have hℓ16_2 : ℓ ^ 16 ≤ 2840 / 1000000 := by
    rw [show ℓ ^ 16 = ℓ ^ 8 * ℓ ^ 8 by ring]
    exact le_trans (mul_le_mul hℓ8_2 hℓ8_2 (by positivity) (by norm_num)) (by norm_num)
  have hc0 : 2 * (s2 - 1) - s2 * ℓ + (2 * s2 - 1) / 6 * ℓ ^ 2 ≤ -5415 / 1000000 := by
    have hlin : 2 - ℓ + ℓ ^ 2 / 3 ≤ 2 - 693146 / 1000000 + (480455 / 1000000) / 3 := by
      linarith only [hℓ1_1, hℓ2_2]
    have hmul := mul_le_mul hlin hs2_high hs2_0 (by norm_num)
    have hexp : 2 * (s2 - 1) - s2 * ℓ + (2 * s2 - 1) / 6 * ℓ ^ 2 =
        (2 - ℓ + ℓ ^ 2 / 3) * s2 - 2 - ℓ ^ 2 / 6 := by ring
    linarith only [hℓ2_1, hmul, hexp]
  have hc1 : s2 * ℓ ^ 3 / 6 - (2 * s2 - 1) / 72 * ℓ ^ 4 - (4 - 2 * s2) / 6 * ℓ ^ 2 ≤
      -21160 / 1000000 := by
    have hlin : ℓ ^ 3 / 6 - ℓ ^ 4 / 36 + ℓ ^ 2 / 3 ≤
        (333027 / 1000000) / 6 - (230833 / 1000000) / 36 + (480455 / 1000000) / 3 := by
      linarith only [hℓ3_2, hℓ4_1, hℓ2_2]
    have hmul := mul_le_mul hlin hs2_high hs2_0 (by norm_num)
    have hexp : s2 * ℓ ^ 3 / 6 - (2 * s2 - 1) / 72 * ℓ ^ 4 - (4 - 2 * s2) / 6 * ℓ ^ 2 =
        (ℓ ^ 3 / 6 - ℓ ^ 4 / 36 + ℓ ^ 2 / 3) * s2 + ℓ ^ 4 / 72 - 2 / 3 * ℓ ^ 2 := by ring
    linarith only [hℓ4_2, hℓ2_1, hmul, hexp]
  have hc2 : -s2 * ℓ ^ 5 / 120 + (2 * s2 - 1) / 2160 * ℓ ^ 6 + (4 - 2 * s2) / 72 * ℓ ^ 4 ≤
      19647 / 10000000 := by
    have hlin : (159999 / 1000000 : ℝ) / 120 - (110907 / 1000000) / 1080 +
        (230833 / 1000000) / 36 ≤ ℓ ^ 5 / 120 - ℓ ^ 6 / 1080 + ℓ ^ 4 / 36 := by
      linarith only [hℓ5_1, hℓ6_2, hℓ4_1]
    have hmul := mul_le_mul hlin hs2_low (by norm_num) (by linarith only [hlin])
    have hexp : -s2 * ℓ ^ 5 / 120 + (2 * s2 - 1) / 2160 * ℓ ^ 6 + (4 - 2 * s2) / 72 * ℓ ^ 4 =
        -(ℓ ^ 5 / 120 - ℓ ^ 6 / 1080 + ℓ ^ 4 / 36) * s2 - ℓ ^ 6 / 2160 + ℓ ^ 4 / 18 := by ring
    linarith only [hℓ6_1, hℓ4_2, hmul, hexp]
  have hc3 : s2 * ℓ ^ 7 / 5040 - (4 - 2 * s2) / 2160 * ℓ ^ 6 -
      (2 * s2 - 1) / 120960 * ℓ ^ 8 ≤ -39380 / 1000000000 := by
    have hlin : ℓ ^ 7 / 5040 + ℓ ^ 6 / 1080 - ℓ ^ 8 / 60480 ≤
        (76875 / 1000000) / 5040 + (110907 / 1000000) / 1080 - (53283 / 1000000) / 60480 := by
      linarith only [hℓ7_2, hℓ6_2, hℓ8_1]
    have hmul := mul_le_mul hlin hs2_high hs2_0 (by norm_num)
    have hexp : s2 * ℓ ^ 7 / 5040 - (4 - 2 * s2) / 2160 * ℓ ^ 6 -
        (2 * s2 - 1) / 120960 * ℓ ^ 8 =
        (ℓ ^ 7 / 5040 + ℓ ^ 6 / 1080 - ℓ ^ 8 / 60480) * s2 - ℓ ^ 6 / 540 + ℓ ^ 8 / 120960 := by
      ring
    linarith only [hℓ6_1, hℓ8_2, hmul, hexp]
  have hc4 : -s2 * ℓ ^ 9 / 362880 + (4 - 2 * s2) / 120960 * ℓ ^ 8 +
      (2 * s2 - 1) / 10886400 * ℓ ^ 10 ≤ 37740 / 100000000000 := by
    have hlin : (36932 / 1000000 : ℝ) / 362880 + (53283 / 1000000) / 60480 -
        (25602 / 1000000) / 5443200 ≤
        ℓ ^ 9 / 362880 + ℓ ^ 8 / 60480 - ℓ ^ 10 / 5443200 := by
      linarith only [hℓ9_1, hℓ8_1, hℓ10_2]
    have hmul := mul_le_mul hlin hs2_low (by norm_num) (by linarith only [hlin])
    have hexp : -s2 * ℓ ^ 9 / 362880 + (4 - 2 * s2) / 120960 * ℓ ^ 8 +
        (2 * s2 - 1) / 10886400 * ℓ ^ 10 =
        -(ℓ ^ 9 / 362880 + ℓ ^ 8 / 60480 - ℓ ^ 10 / 5443200) * s2 +
          ℓ ^ 8 / 30240 - ℓ ^ 10 / 10886400 := by ring
    linarith only [hℓ8_2, hℓ10_1, hmul, hexp]
  have hc5 : s2 * ℓ ^ 11 / 39916800 - (4 - 2 * s2) / 10886400 * ℓ ^ 10 -
      (2 * s2 - 1) / 1437004800 * ℓ ^ 12 ≤ -21409 / 10000000000000 := by
    have hlin : ℓ ^ 11 / 39916800 + ℓ ^ 10 / 5443200 - ℓ ^ 12 / 718502400 ≤
        (17746 / 1000000) / 39916800 + (25602 / 1000000) / 5443200 -
          (12299 / 1000000) / 718502400 := by
      linarith only [hℓ11_2, hℓ10_2, hℓ12_1]
    have hmul := mul_le_mul hlin hs2_high hs2_0 (by norm_num)
    have hexp : s2 * ℓ ^ 11 / 39916800 - (4 - 2 * s2) / 10886400 * ℓ ^ 10 -
        (2 * s2 - 1) / 1437004800 * ℓ ^ 12 =
        (ℓ ^ 11 / 39916800 + ℓ ^ 10 / 5443200 - ℓ ^ 12 / 718502400) * s2 -
          ℓ ^ 10 / 2721600 + ℓ ^ 12 / 1437004800 := by ring
    linarith only [hℓ10_1, hℓ12_2, hmul, hexp]
  have hc6 : -s2 * ℓ ^ 13 / 6227020800 + (4 - 2 * s2) / 1437004800 * ℓ ^ 12 +
      (2 * s2 - 1) / 261534873600 * ℓ ^ 14 ≤ 8140 / 1000000000000000 := by
    have hlin : (8525 / 1000000 : ℝ) / 6227020800 + (12299 / 1000000) / 718502400 -
        (5911 / 1000000) / 130767436800 ≤
        ℓ ^ 13 / 6227020800 + ℓ ^ 12 / 718502400 - ℓ ^ 14 / 130767436800 := by
      linarith only [hℓ13_1, hℓ12_1, hℓ14_2]
    have hmul := mul_le_mul hlin hs2_low (by norm_num) (by linarith only [hlin])
    have hexp : -s2 * ℓ ^ 13 / 6227020800 + (4 - 2 * s2) / 1437004800 * ℓ ^ 12 +
        (2 * s2 - 1) / 261534873600 * ℓ ^ 14 =
        -(ℓ ^ 13 / 6227020800 + ℓ ^ 12 / 718502400 - ℓ ^ 14 / 130767436800) * s2 +
          ℓ ^ 12 / 359251200 - ℓ ^ 14 / 261534873600 := by ring
    linarith only [hℓ12_2, hℓ14_1, hmul, hexp]
  have hc7 : s2 * ℓ ^ 15 / 1307674368000 - (4 - 2 * s2) / 261534873600 * ℓ ^ 14 ≤
      -2201 / 100000000000000000 := by
    have hlin : ℓ ^ 15 / 1307674368000 + ℓ ^ 14 / 130767436800 ≤
        (4098 / 1000000) / 1307674368000 + (5911 / 1000000) / 130767436800 := by
      linarith only [hℓ15_2, hℓ14_2]
    have hmul := mul_le_mul hlin hs2_high hs2_0 (by norm_num)
    have hexp : s2 * ℓ ^ 15 / 1307674368000 - (4 - 2 * s2) / 261534873600 * ℓ ^ 14 =
        (ℓ ^ 15 / 1307674368000 + ℓ ^ 14 / 130767436800) * s2 - ℓ ^ 14 / 65383718400 := by ring
    linarith only [hℓ14_1, hmul, hexp]
  have hc8 : (4 - 2 * s2) / 62768369664000 * ℓ ^ 16 ≤ 531 / 10000000000000000000 := by
    have hlin : (4 - 2 * s2) / 62768369664000 ≤ (4 - 2 * (47321 / 33461)) / 62768369664000 := by
      linarith only [hs2_low]
    have hmul := mul_le_mul hlin hℓ16_2 (by positivity) (by norm_num)
    linarith only [hmul]
  rcases le_total u 10 with h10 | h10
  · exact first_cell_poly_of_coeffs_joint_low hc0 hc1 hc2 hc3 hc4 hc5 hc6 hc7 hc8 hu_nonneg h10
  · exact first_cell_poly_of_coeffs_joint_mid hc0 hc1 hc2 hc3 hc4 hc5 hc6 hc7 hc8 h10 hr

/-- **Joint First-Cell + Resolvent Numerator Bound (`∀ r : ℝ`)**:
for **every** `r : ℝ`,
`-(1 / 4 + r ^ 2) * ∫ x in 1..2, (cosLogProfile r x - cellSecant (cosLogProfile r) 2 x) / √x - 1 / 2 ≤ ((71 / 3600) * r ^ 2 - 91 / 360) * (1 / 4 + r ^ 2)`. -/
theorem neg_mul_integral_one_two_cosLogProfile_sub_half_le_joint_resolvent (r : ℝ) :
    -(1 / 4 + r ^ 2) *
        (∫ x in (1 : ℝ)..2,
          (cosLogProfile r x - cellSecant (cosLogProfile r) 2 x) / Real.sqrt x) -
      1 / 2 ≤
    ((71 / 3600) * r ^ 2 - 91 / 360) * (1 / 4 + r ^ 2) := by
  rcases le_total (r ^ 2) 49 with hr | hr
  · rw [neg_mul_integral_one_two_cosLogProfile_sub_cellSecant_div_sqrt_eq r]
    set ℓ := Real.log 2
    set s2 := Real.sqrt 2
    set u := r ^ 2
    have hu_nonneg : 0 ≤ u := sq_nonneg r
    have hℓ_low : (693146 / 1000000 : ℝ) ≤ ℓ := eight_panel_log_two_lower
    have hℓ_high : ℓ ≤ 693148 / 1000000 := eight_panel_log_two_upper
    have hℓ_pos : 0 < ℓ := lt_of_lt_of_le (by norm_num) hℓ_low
    have hs2_low : (47321 / 33461 : ℝ) ≤ s2 := pell_sqrt_two_lower
    have hs2_high : s2 ≤ 114243 / 80782 := pell_sqrt_two_upper
    set θ := r * ℓ
    have hcos_up := one_sub_cos_le_taylor_degree_fourteen θ
    have hcos_low := taylor_degree_sixteen_le_one_sub_cos θ
    have hsin_low := mul_sin_ge_taylor_degree_sixteen θ
    have hsin_scaled :
        r ^ 2 * (ℓ - ℓ ^ 3 * u / 6 + ℓ ^ 5 * u ^ 2 / 120 - ℓ ^ 7 * u ^ 3 / 5040 +
          ℓ ^ 9 * u ^ 4 / 362880 - ℓ ^ 11 * u ^ 5 / 39916800 +
          ℓ ^ 13 * u ^ 6 / 6227020800 - ℓ ^ 15 * u ^ 7 / 1307674368000) ≤
          r * Real.sin θ := by
      have hdiv := div_le_div_of_nonneg_right hsin_low hℓ_pos.le
      have h1 : (θ ^ 2 - θ ^ 4 / 6 + θ ^ 6 / 120 - θ ^ 8 / 5040 +
          θ ^ 10 / 362880 - θ ^ 12 / 39916800 +
          θ ^ 14 / 6227020800 - θ ^ 16 / 1307674368000) / ℓ =
          r ^ 2 * (ℓ - ℓ ^ 3 * u / 6 + ℓ ^ 5 * u ^ 2 / 120 - ℓ ^ 7 * u ^ 3 / 5040 +
            ℓ ^ 9 * u ^ 4 / 362880 - ℓ ^ 11 * u ^ 5 / 39916800 +
            ℓ ^ 13 * u ^ 6 / 6227020800 - ℓ ^ 15 * u ^ 7 / 1307674368000) := by
        dsimp [θ, u]
        field_simp [hℓ_pos.ne']
      have h2 : θ * Real.sin θ / ℓ = r * Real.sin θ := by
        dsimp [θ]
        field_simp [hℓ_pos.ne']
      linarith
    have hcoeff_pos1 : 0 ≤ (2 * s2 - 1) / 3 := by linarith
    have hcoeff_pos2 : 0 ≤ ((4 - 2 * s2) / 3) * r ^ 2 :=
      mul_nonneg (by linarith) (sq_nonneg r)
    have hterm_cos1 := mul_le_mul_of_nonneg_left hcos_up hcoeff_pos1
    have hterm_cos2 := mul_le_mul_of_nonneg_left hcos_low hcoeff_pos2
    have hterm_sin := mul_le_mul_of_nonneg_left hsin_scaled (by linarith : 0 ≤ s2)
    have hpoly_id :
        2 * (s2 - 1) * r ^ 2 -
          s2 * (r ^ 2 * (ℓ - ℓ ^ 3 * u / 6 + ℓ ^ 5 * u ^ 2 / 120 - ℓ ^ 7 * u ^ 3 / 5040 +
            ℓ ^ 9 * u ^ 4 / 362880 - ℓ ^ 11 * u ^ 5 / 39916800 +
            ℓ ^ 13 * u ^ 6 / 6227020800 - ℓ ^ 15 * u ^ 7 / 1307674368000)) +
          ((2 * s2 - 1) / 3) *
            (θ ^ 2 / 2 - θ ^ 4 / 24 + θ ^ 6 / 720 - θ ^ 8 / 40320 +
              θ ^ 10 / 3628800 - θ ^ 12 / 479001600 + θ ^ 14 / 87178291200) -
          (((4 - 2 * s2) / 3) * r ^ 2) *
            (θ ^ 2 / 2 - θ ^ 4 / 24 + θ ^ 6 / 720 - θ ^ 8 / 40320 +
              θ ^ 10 / 3628800 - θ ^ 12 / 479001600 + θ ^ 14 / 87178291200 -
              θ ^ 16 / 20922789888000) =
        u * ((2 * (s2 - 1) - s2 * ℓ + (2 * s2 - 1) / 6 * ℓ ^ 2) +
          (s2 * ℓ ^ 3 / 6 - (2 * s2 - 1) / 72 * ℓ ^ 4 - (4 - 2 * s2) / 6 * ℓ ^ 2) * u +
          (-s2 * ℓ ^ 5 / 120 + (2 * s2 - 1) / 2160 * ℓ ^ 6 + (4 - 2 * s2) / 72 * ℓ ^ 4) * u ^ 2 +
          (s2 * ℓ ^ 7 / 5040 - (4 - 2 * s2) / 2160 * ℓ ^ 6 -
            (2 * s2 - 1) / 120960 * ℓ ^ 8) * u ^ 3 +
          (-s2 * ℓ ^ 9 / 362880 + (4 - 2 * s2) / 120960 * ℓ ^ 8 +
            (2 * s2 - 1) / 10886400 * ℓ ^ 10) * u ^ 4 +
          (s2 * ℓ ^ 11 / 39916800 - (4 - 2 * s2) / 10886400 * ℓ ^ 10 -
            (2 * s2 - 1) / 1437004800 * ℓ ^ 12) * u ^ 5 +
          (-s2 * ℓ ^ 13 / 6227020800 + (4 - 2 * s2) / 1437004800 * ℓ ^ 12 +
            (2 * s2 - 1) / 261534873600 * ℓ ^ 14) * u ^ 6 +
          (s2 * ℓ ^ 15 / 1307674368000 - (4 - 2 * s2) / 261534873600 * ℓ ^ 14) * u ^ 7 +
          ((4 - 2 * s2) / 62768369664000 * ℓ ^ 16) * u ^ 8) := by
      dsimp [θ, u]
      ring
    have hinner_le :=
      first_cell_taylor_poly_le_joint_resolvent hℓ_low hℓ_high hs2_low hs2_high hu_nonneg hr
    dsimp [u] at hinner_le hpoly_id ⊢
    linarith
  · have h7 := neg_seven_four_eightieths_mul_sq_le_integral_one_two_cosLogProfile r
    have hden_pos : (0 : ℝ) ≤ 1 / 4 + r ^ 2 := by positivity
    have hmul := mul_le_mul_of_nonneg_left h7 hden_pos
    have hquad : 0 ≤ (r ^ 2 - 49) ^ 2 := sq_nonneg (r ^ 2 - 49)
    nlinarith

/-- **The Global Joint First-Cell Cosine-Log + Resolvent Envelope (`-(71 / 3600) r² + 91 / 360 - (1 / 2) / (1 / 4 + r²) ≤ I_2(r)`)**:
for **every** `r : ℝ`,
`-(71 / 3600) * r ^ 2 + 91 / 360 - (1 / 2) * (1 / (1 / 4 + r ^ 2)) ≤ ∫ x in 1..2, (cosLogProfile r x - cellSecant (cosLogProfile r) 2 x) / Real.sqrt x`. -/
theorem joint_resolvent_envelope_le_integral_one_two_cosLogProfile (r : ℝ) :
    -(71 / 3600 : ℝ) * r ^ 2 + 91 / 360 - (1 / 2) * (1 / (1 / 4 + r ^ 2)) ≤
      ∫ x in (1 : ℝ)..2,
        (cosLogProfile r x - cellSecant (cosLogProfile r) 2 x) / Real.sqrt x := by
  have hden_pos : (0 : ℝ) < 1 / 4 + r ^ 2 := by positivity
  have hden_ne : (1 / 4 + r ^ 2 : ℝ) ≠ 0 := hden_pos.ne'
  have hle := div_le_div_of_nonneg_right
    (neg_mul_integral_one_two_cosLogProfile_sub_half_le_joint_resolvent r) hden_pos.le
  have hlhs :
      (-(1 / 4 + r ^ 2) *
          (∫ x in (1 : ℝ)..2,
            (cosLogProfile r x - cellSecant (cosLogProfile r) 2 x) / Real.sqrt x) -
          1 / 2) /
          (1 / 4 + r ^ 2) =
        -(∫ x in (1 : ℝ)..2,
          (cosLogProfile r x - cellSecant (cosLogProfile r) 2 x) / Real.sqrt x) -
          (1 / 2) * (1 / (1 / 4 + r ^ 2)) := by
    field_simp [hden_ne]
  have hrhs :
      (((71 / 3600) * r ^ 2 - 91 / 360) * (1 / 4 + r ^ 2)) / (1 / 4 + r ^ 2) =
        (71 / 3600) * r ^ 2 - 91 / 360 := by
    field_simp [hden_ne]
  rw [hlhs, hrhs] at hle
  linarith

/-- **The Joint First-Cell + Resolvent Spectral Inequality (`91 / 180 = 1820 / 3600` Surplus)**:
for every `f : WeilTestFn` with `Integrable (fun r => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))`,
`(91 / 180) * ∫ ‖f.1‖² - (71 / 3600) * spectralSecondMoment f.1 ≤ bochnerResolventEnergy (EF.weilTest f.1 f.1) + ∫ x in 1..2, (weilSymmetricLogNumerator f.1 x - cellSecant (weilSymmetricLogNumerator f.1) 2 x) / √x`. -/
theorem ninety_one_one_eightieths_l2_sub_seventy_one_second_le_bochnerResolventEnergy_add_integral_one_two
    (f : WeilTestFn)
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2)) :
    (91 / 180 : ℝ) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) -
        (71 / 3600) * spectralSecondMoment f.1 ≤
      bochnerResolventEnergy (EF.weilTest f.1 f.1) +
        ∫ x in (1 : ℝ)..2,
          (weilSymmetricLogNumerator f.1 x - cellSecant (weilSymmetricLogNumerator f.1) 2 x) /
            Real.sqrt x := by
  rw [integral_one_two_weilSymmetricLogNumerator_sub_cellSecant_div_sqrt_eq_spectral f,
    bochnerResolventEnergy_weilTest_eq f]
  have hsq := integrable_paperFT_norm_sq f
  have hres_int := integrable_paperFT_norm_sq_mul_inv_quarter_add_sq f
  have hcell_int := integrable_paperFT_norm_sq_mul_two_integral_one_two_cosLogProfile f
  have hplanch := one_div_two_pi_mul_integral_paperFT_norm_sq_mul_two_eq f
  have hlhs_eq :
      (91 / 180 : ℝ) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) -
          (71 / 3600) * spectralSecondMoment f.1 =
        (1 / (2 * Real.pi)) *
          ∫ r : ℝ,
            ((91 / 360 : ℝ) * (‖paperFT f.1 r‖ ^ 2 * 2) +
              (-(71 / 3600 : ℝ)) * (‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))) := by
    unfold spectralSecondMoment
    rw [integral_add ((hsq.mul_const 2).const_mul (91 / 360 : ℝ))
      (hint2.const_mul (-(71 / 3600 : ℝ))),
      integral_const_mul, integral_const_mul]
    linear_combination -(91 / 360 : ℝ) * hplanch
  have hrhs_eq :
      (1 / (2 * Real.pi)) * (∫ r : ℝ, ‖paperFT f.1 r‖ ^ 2 * (1 / (1 / 4 + r ^ 2))) +
          (1 / (2 * Real.pi)) *
            (∫ r : ℝ,
              ‖paperFT f.1 r‖ ^ 2 *
                (2 * ∫ x in (1 : ℝ)..2,
                  (cosLogProfile r x - cellSecant (cosLogProfile r) 2 x) / Real.sqrt x)) =
        (1 / (2 * Real.pi)) *
          ∫ r : ℝ,
            (‖paperFT f.1 r‖ ^ 2 * (1 / (1 / 4 + r ^ 2)) +
              ‖paperFT f.1 r‖ ^ 2 *
                (2 * ∫ x in (1 : ℝ)..2,
                  (cosLogProfile r x - cellSecant (cosLogProfile r) 2 x) / Real.sqrt x)) := by
    rw [← mul_add, ← integral_add hres_int hcell_int]
  rw [hlhs_eq, hrhs_eq]
  refine mul_le_mul_of_nonneg_left ?_ (div_nonneg zero_le_one Real.two_pi_pos.le)
  refine integral_mono
    (((hsq.mul_const 2).const_mul (91 / 360 : ℝ)).add (hint2.const_mul (-(71 / 3600 : ℝ))))
    (hres_int.add hcell_int) fun r => ?_
  dsimp only
  have hpt := joint_resolvent_envelope_le_integral_one_two_cosLogProfile r
  have hmul := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hpt (by norm_num : (0 : ℝ) ≤ 2))
    (sq_nonneg ‖paperFT f.1 r‖)
  linarith

/-- **The Symmetric `71 / 3600` Resolvent + Secant Numerator Law**:
for every `f : WeilTestFn` with `Integrable (fun r => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))` and `1 ≤ N`,
`(91 / 180) * ∫ ‖f.1‖² - (71 / 3600) * (spectralSecondMoment f.1 + √(spectralSecondMoment f.1 * (spectralSecondMoment f.1 + 2 * ∫ ‖f.1‖²))) ≤ bochnerResolventEnergy (EF.weilTest f.1 f.1) + secantNumeratorCellDefect f.1 N`. -/
theorem ninety_one_one_eightieths_l2_sub_seventy_one_second_add_geom_le_bochnerResolventEnergy_add_secantNumeratorCellDefect
    (f : WeilTestFn)
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))
    {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest f.1 f.1 (Real.log N) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log N) = 0) :
    (91 / 180 : ℝ) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) -
        (71 / 3600) *
          (spectralSecondMoment f.1 +
            Real.sqrt
              (spectralSecondMoment f.1 *
                (spectralSecondMoment f.1 + 2 * ∫ u : ℝ, ‖f.1 u‖ ^ 2))) ≤
      bochnerResolventEnergy (EF.weilTest f.1 f.1) +
        secantNumeratorCellDefect f.1 N := by
  by_cases hN2 : 2 ≤ N
  · unfold secantNumeratorCellDefect
    rw [sum_Icc_two_eq_add_sum_Icc_three _ hN2]
    have h2 :=
      ninety_one_one_eightieths_l2_sub_seventy_one_second_le_bochnerResolventEnergy_add_integral_one_two
        f hint2
    have h3 := neg_seventy_one_thirty_six_hundredths_sqrt_le_sum_Icc_three f hint2 N
    linarith
  · have hN_eq : N = 1 := by omega
    subst hN_eq
    have h1 : weilSymmetricLogNumerator f.1 1 = 0 := by
      unfold weilSymmetricLogNumerator
      have h0 : EF.weilTest f.1 f.1 (Real.log (1 : ℕ)) = 0 ∧
          EF.weilTest f.1 f.1 (-Real.log (1 : ℕ)) = 0 := hN0
      push_cast at h0
      rw [h0.1, h0.2, add_zero, Complex.zero_re]
    have hL0 : ∫ u : ℝ, ‖f.1 u‖ ^ 2 = 0 := by
      have h2 := weilSymmetricLogNumerator_one_eq_two_mul_integral_norm_sq f
      linarith
    have hS_nn : 0 ≤ spectralSecondMoment f.1 := spectralSecondMoment_nonneg f.1
    have hsqrt_nn : 0 ≤ Real.sqrt
        (spectralSecondMoment f.1 *
          (spectralSecondMoment f.1 + 2 * ∫ u : ℝ, ‖f.1 u‖ ^ 2)) := Real.sqrt_nonneg _
    have hres_nn : 0 ≤ bochnerResolventEnergy (EF.weilTest f.1 f.1) :=
      bochnerResolventEnergy_weilTest_nonneg f
    unfold secantNumeratorCellDefect
    rw [Finset.Icc_eq_empty (by omega : ¬ 2 ≤ 1), Finset.sum_empty]
    linarith

/-! ## Section 2: Coercivity, Unconditional `0 ≤ markovEnergy`, and Cutoff-Free `EWU` Spectral Gaps up to `33` and `69 / 2 = 34.5` -/

/-- **Universal Tangent Upper Bound `Real.sqrt (S * (S + 2 * L)) ≤ (2381 / 2380) * S + (34 / 35) * L`**:
evaluating the variational envelope at `b = 17 / 35` (`((2381 / 2380) S + (34 / 35) L)² - S(S + 2L) = ((69 / 2380) S - (34 / 35) L)² ≥ 0`) gives a linear upper bound that is exact at `S / L = 80920 / 2415 ≈ 33.51`. -/
theorem sqrt_spectralSecondMoment_mul_add_two_l2_le_add_seventeen_thirty_fifths
    (f : WeilTestFn) :
    Real.sqrt
        (spectralSecondMoment f.1 *
          (spectralSecondMoment f.1 + 2 * ∫ u : ℝ, ‖f.1 u‖ ^ 2)) ≤
      (2381 / 2380) * spectralSecondMoment f.1 + (34 / 35) * ∫ u : ℝ, ‖f.1 u‖ ^ 2 := by
  let S := spectralSecondMoment f.1
  let L := ∫ u : ℝ, ‖f.1 u‖ ^ 2
  have hS_nonneg : 0 ≤ S := spectralSecondMoment_nonneg f.1
  have hL_nonneg : 0 ≤ L := integral_nonneg fun _ => sq_nonneg _
  rw [← Real.sqrt_sq (by positivity : 0 ≤ (2381 / 2380) * S + (34 / 35) * L)]
  refine Real.sqrt_le_sqrt ?_
  have hsq : 0 ≤ ((69 / 2380) * S - (34 / 35) * L) ^ 2 := sq_nonneg _
  linarith

/-- **Resolvent-Enhanced Quadrature Coercivity up to Critical Ratio `33` (Upgraded from `51 / 2 = 25.5`)**:
whenever `spectralSecondMoment f.1 ≤ 33 * ∫ ‖f.1‖²`, we have
`(1 / 150) * ∫ ‖f.1‖² ≤ bochnerResolventEnergy (EF.weilTest f.1 f.1) + rightCellQuadratureDefect (weilContinuumLogProfile f.1) N`! -/
theorem one_one_fiftieth_l2_le_bochnerResolventEnergy_add_rightCellQuadratureDefect_of_spectralSecondMoment_le_thirty_three
    (f : WeilTestFn)
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))
    {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest f.1 f.1 (Real.log N) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log N) = 0)
    (hN : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0)
    (hsec : spectralSecondMoment f.1 ≤ 33 * ∫ u : ℝ, ‖f.1 u‖ ^ 2) :
    (1 / 150) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) ≤
      bochnerResolventEnergy (EF.weilTest f.1 f.1) +
        rightCellQuadratureDefect (weilContinuumLogProfile f.1) N := by
  have hL : 0 ≤ ∫ u : ℝ, ‖f.1 u‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have h1 :=
    two_forty_seven_three_hundredths_l2_add_secantNumerator_le_rightCellQuadratureDefect
      f hN1 hN0 hN
  have h2 :=
    ninety_one_one_eightieths_l2_sub_seventy_one_second_add_geom_le_bochnerResolventEnergy_add_secantNumeratorCellDefect
      f hint2 hN1 hN0
  have hamgm := sqrt_spectralSecondMoment_mul_add_two_l2_le_add_seventeen_thirty_fifths f
  linarith

/-- **Resolvent-Enhanced Quadrature Coercivity on the Nonnegative Log-Value Cone up to `69 / 2 = 34.5`
(Upgraded from `27`, Deep into the `S / L > 27` Regime)**:
whenever `∀ n ∈ Finset.Icc 2 N, 0 ≤ logValue f.1 n` and `spectralSecondMoment f.1 ≤ (69 / 2) * ∫ ‖f.1‖²`,
`(1 / 1200) * ∫ ‖f.1‖² ≤ bochnerResolventEnergy (EF.weilTest f.1 f.1) + rightCellQuadratureDefect (weilContinuumLogProfile f.1) N`! -/
theorem one_twelve_hundredth_l2_le_bochnerResolventEnergy_add_rightCellQuadratureDefect_of_spectralSecondMoment_le_sixty_nine_halves_of_logValue_nonneg
    (f : WeilTestFn)
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))
    {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest f.1 f.1 (Real.log N) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log N) = 0)
    (hN : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0)
    (hpos : ∀ n ∈ Finset.Icc 2 N, 0 ≤ logValue f.1 n)
    (hsec : spectralSecondMoment f.1 ≤ (69 / 2) * ∫ u : ℝ, ‖f.1 u‖ ^ 2) :
    (1 / 1200) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) ≤
      bochnerResolventEnergy (EF.weilTest f.1 f.1) +
        rightCellQuadratureDefect (weilContinuumLogProfile f.1) N := by
  have hL : 0 ≤ ∫ u : ℝ, ‖f.1 u‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have h1 :=
    twelve_sixty_one_fourteen_fortieths_l2_add_secantNumerator_le_rightCellQuadratureDefect_of_logValue_nonneg
      f hN1 hN0 hN hpos
  have h2 :=
    ninety_one_one_eightieths_l2_sub_seventy_one_second_add_geom_le_bochnerResolventEnergy_add_secantNumeratorCellDefect
      f hint2 hN1 hN0
  have hamgm := sqrt_spectralSecondMoment_mul_add_two_l2_le_add_seventeen_thirty_fifths f
  linarith

/-- **Resolvent-Enhanced Quadrature Coercivity on the Prime-Blind Cone (`logVector f = 0`) up to `69 / 2 = 34.5`
(Upgraded from `27`, Deep into the `S / L > 27` Regime)**: -/
theorem one_twelve_hundredth_l2_le_bochnerResolventEnergy_add_rightCellQuadratureDefect_of_spectralSecondMoment_le_sixty_nine_halves_of_logVector_eq_zero
    (f : WeilTestFn) (hblind : logVector f = 0)
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))
    {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest f.1 f.1 (Real.log N) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log N) = 0)
    (hN : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0)
    (hsec : spectralSecondMoment f.1 ≤ (69 / 2) * ∫ u : ℝ, ‖f.1 u‖ ^ 2) :
    (1 / 1200) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) ≤
      bochnerResolventEnergy (EF.weilTest f.1 f.1) +
        rightCellQuadratureDefect (weilContinuumLogProfile f.1) N := by
  have hL : 0 ≤ ∫ u : ℝ, ‖f.1 u‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have h1 :=
    twelve_sixty_one_fourteen_fortieths_l2_add_secantNumerator_le_rightCellQuadratureDefect_of_logVector_eq_zero
      f hblind hN1 hN0 hN
  have h2 :=
    ninety_one_one_eightieths_l2_sub_seventy_one_second_add_geom_le_bochnerResolventEnergy_add_secantNumeratorCellDefect
      f hint2 hN1 hN0
  have hamgm := sqrt_spectralSecondMoment_mul_add_two_l2_le_add_seventeen_thirty_fifths f
  linarith

/-- **Unconditional `0 ≤ markovEnergy F` on the Primitive Hyperplane up to `33 * ∫ ‖F‖²`
(Upgraded from `(51 / 2) * ∫ ‖F‖² = 25.5 * ∫ ‖F‖²`)**: -/
theorem markovEnergy_ofReal_nonneg_of_spectralSecondMoment_le_thirty_three_of_cosh_zero
    (m : ℕ) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hcosh : coshHalfMoment f = 0)
    (hint2 : Integrable fun r : ℝ => ‖paperFT (realWeilTestFn f hf hfc).1 r‖ ^ 2 * (2 * r ^ 2))
    {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log N) = 0 ∧
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log N) = 0)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log x) = 0 ∧
        EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log x) = 0)
    (hdiff : ∀ n ∈ Finset.Icc 2 N,
      0 ≤ iteratedForwardDiff m (logValue (realWeilTestFn f hf hfc).1) n)
    (hsec_bound : spectralSecondMoment (realWeilTestFn f hf hfc).1 ≤
      33 * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) :
    0 ≤ markovEnergy (realWeilTestFn f hf hfc).1 := by
  have hL_nonneg : 0 ≤ ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  let θ := max (max 1 (Real.log (N : ℝ))) 401
  have hθlog : Real.log (N : ℝ) ≤ θ :=
    (le_max_right 1 (Real.log (N : ℝ))).trans (le_max_left _ _)
  have hθ_large : (401 : ℝ) ≤ θ := le_max_right _ _
  have hθ_sub : (400 : ℝ) ≤ θ - 1 := by linarith
  have hbase := one_hundredth_l2_add_theta_slope_quadrature_le_markovEnergy_of_cosh_zero
    m hf hfc hcosh hN1 hθlog hN hdiff
  have hatom := atomPairRe_weilTest_le_two_mul_integral_norm_sq (realWeilTestFn f hf hfc)
  have h1 :=
    two_forty_seven_three_hundredths_l2_add_secantNumerator_le_rightCellQuadratureDefect
      (realWeilTestFn f hf hfc) hN1 hN0 (fun n hn => hN n (by exact_mod_cast hn))
  have h2 :=
    neg_seven_four_eightieths_second_sub_seventy_one_geom_le_secantNumeratorCellDefect
      (realWeilTestFn f hf hfc) hint2 N
  have hamgm :=
    sqrt_spectralSecondMoment_mul_add_two_l2_le_add_seventeen_thirty_fifths
      (realWeilTestFn f hf hfc)
  have hcomb :=
    one_one_fiftieth_l2_le_bochnerResolventEnergy_add_rightCellQuadratureDefect_of_spectralSecondMoment_le_thirty_three
      (realWeilTestFn f hf hfc) hint2 hN1 hN0 (fun n hn => hN n (by exact_mod_cast hn)) hsec_bound
  have hθ_comb :
      (400 : ℝ) * ((1 / 150) * (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2)) ≤
        (θ - 1) *
          (bochnerResolventEnergy
            (EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1) +
            rightCellQuadratureDefect (weilContinuumLogProfile (realWeilTestFn f hf hfc).1) N) :=
    mul_le_mul hθ_sub hcomb (by positivity) (by linarith)
  have hsinh_nonneg : 0 ≤ 2 * θ * sinhHalfMoment f ^ 2 := by positivity
  linarith

/-- **Unconditional `0 ≤ markovEnergy F` on the Nonnegative Log-Value Cone up to `(69 / 2) * ∫ ‖F‖² = 34.5 * ∫ ‖F‖²`
(Upgraded from `27 * ∫ ‖F‖²`, Deep into the `S / L > 27` Regime)**: -/
theorem markovEnergy_ofReal_nonneg_of_spectralSecondMoment_le_sixty_nine_halves_of_cosh_zero_of_logValue_nonneg
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hcosh : coshHalfMoment f = 0)
    (hint2 : Integrable fun r : ℝ => ‖paperFT (realWeilTestFn f hf hfc).1 r‖ ^ 2 * (2 * r ^ 2))
    {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log N) = 0 ∧
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log N) = 0)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log x) = 0 ∧
        EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log x) = 0)
    (hpos : ∀ n ∈ Finset.Icc 2 N, 0 ≤ logValue (realWeilTestFn f hf hfc).1 n)
    (hsec_bound : spectralSecondMoment (realWeilTestFn f hf hfc).1 ≤
      (69 / 2) * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) :
    0 ≤ markovEnergy (realWeilTestFn f hf hfc).1 := by
  have hL_nonneg : 0 ≤ ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  let θ := max (max 1 (Real.log (N : ℝ))) 2801
  have hθlog : Real.log (N : ℝ) ≤ θ :=
    (le_max_right 1 (Real.log (N : ℝ))).trans (le_max_left _ _)
  have hθ_large : (2801 : ℝ) ≤ θ := le_max_right _ _
  have hθ_sub : (2800 : ℝ) ≤ θ - 1 := by linarith
  have hbase := one_hundredth_l2_add_theta_slope_quadrature_le_markovEnergy_of_cosh_zero
    0 hf hfc hcosh hN1 hθlog hN (fun n hn => by simpa [iteratedForwardDiff] using hpos n hn)
  have hatom := atomPairRe_weilTest_le_two_mul_integral_norm_sq (realWeilTestFn f hf hfc)
  have h1 :=
    twelve_sixty_one_fourteen_fortieths_l2_add_secantNumerator_le_rightCellQuadratureDefect_of_logValue_nonneg
      (realWeilTestFn f hf hfc) hN1 hN0 (fun n hn => hN n (by exact_mod_cast hn)) hpos
  have h2 :=
    neg_seven_four_eightieths_second_sub_seventy_one_geom_le_secantNumeratorCellDefect
      (realWeilTestFn f hf hfc) hint2 N
  have hamgm :=
    sqrt_spectralSecondMoment_mul_add_two_l2_le_add_seventeen_thirty_fifths
      (realWeilTestFn f hf hfc)
  have hcomb :=
    one_twelve_hundredth_l2_le_bochnerResolventEnergy_add_rightCellQuadratureDefect_of_spectralSecondMoment_le_sixty_nine_halves_of_logValue_nonneg
      (realWeilTestFn f hf hfc) hint2 hN1 hN0 (fun n hn => hN n (by exact_mod_cast hn)) hpos hsec_bound
  have hθ_comb :
      (2800 : ℝ) * ((1 / 1200) * (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2)) ≤
        (θ - 1) *
          (bochnerResolventEnergy
            (EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1) +
            rightCellQuadratureDefect (weilContinuumLogProfile (realWeilTestFn f hf hfc).1) N) :=
    mul_le_mul hθ_sub hcomb (by positivity) (by linarith)
  have hsinh_nonneg : 0 ≤ 2 * θ * sinhHalfMoment f ^ 2 := by positivity
  linarith

/-- **The `33` Spectral Poincaré / Uncertainty Gap Law on the Primitive Hyperplane
(Upgraded from `51 / 2 = 25.5`)**: -/
theorem thirty_three_l2_lt_spectralSecondMoment_of_cosh_zero_of_unitStep_nonneg
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hcosh : coshHalfMoment f = 0)
    (hint2 : Integrable fun r : ℝ => ‖paperFT (realWeilTestFn f hf hfc).1 r‖ ^ 2 * (2 * r ^ 2))
    {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log N) = 0 ∧
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log N) = 0)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log x) = 0 ∧
        EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log x) = 0)
    (hunit : 0 ≤ primeBlindCounterterm unitStepCountertermWeight (realWeilTestFn f hf hfc))
    (hpos_l2 : 0 < ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) :
    33 * (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) <
      spectralSecondMoment (realWeilTestFn f hf hfc).1 := by
  by_contra! hle
  have hcons :=
    unitStep_add_rightCellQuadratureDefect_add_bochnerResolventEnergy_add_sinh_sq_eq_zero_of_cosh_zero
      hf hfc hcosh hN1 hN
  have hcoerc :=
    one_one_fiftieth_l2_le_bochnerResolventEnergy_add_rightCellQuadratureDefect_of_spectralSecondMoment_le_thirty_three
      (realWeilTestFn f hf hfc) hint2 hN1 hN0 (fun n hn => hN n (by exact_mod_cast hn)) hle
  have hsinh_nonneg : 0 ≤ 2 * sinhHalfMoment f ^ 2 := by positivity
  linarith

/-- **The `69 / 2 = 34.5` Spectral Poincaré / Uncertainty Gap Law on the Nonnegative Log-Value Cone
(Upgraded from `27`, Deep into the `S / L > 27` Regime)**: -/
theorem sixty_nine_halves_l2_lt_spectralSecondMoment_of_cosh_zero_of_logValue_nonneg
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hcosh : coshHalfMoment f = 0)
    (hint2 : Integrable fun r : ℝ => ‖paperFT (realWeilTestFn f hf hfc).1 r‖ ^ 2 * (2 * r ^ 2))
    {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log N) = 0 ∧
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log N) = 0)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log x) = 0 ∧
        EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log x) = 0)
    (hpos : ∀ n ∈ Finset.Icc 2 N, 0 ≤ logValue (realWeilTestFn f hf hfc).1 n)
    (hpos_l2 : 0 < ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) :
    (69 / 2) * (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) <
      spectralSecondMoment (realWeilTestFn f hf hfc).1 := by
  by_contra! hle
  have hcons :=
    unitStep_add_rightCellQuadratureDefect_add_bochnerResolventEnergy_add_sinh_sq_eq_zero_of_cosh_zero
      hf hfc hcosh hN1 hN
  have hcoerc :=
    one_twelve_hundredth_l2_le_bochnerResolventEnergy_add_rightCellQuadratureDefect_of_spectralSecondMoment_le_sixty_nine_halves_of_logValue_nonneg
      (realWeilTestFn f hf hfc) hint2 hN1 hN0 (fun n hn => hN n (by exact_mod_cast hn)) hpos hle
  have hunit_nonneg :
      0 ≤ primeBlindCounterterm unitStepCountertermWeight (realWeilTestFn f hf hfc) := by
    rw [primeBlindCounterterm_eq_sum_Icc unitStepCountertermWeight (realWeilTestFn f hf hfc)
      (fun n hn => hN n (by exact_mod_cast hn))]
    refine Finset.sum_nonneg fun n hn => ?_
    have hn_mem := Finset.mem_Icc.mp hn
    unfold unitStepCountertermWeight
    rw [if_pos hn_mem.1]
    exact mul_nonneg zero_le_one (hpos n hn)
  have hsinh_nonneg : 0 ≤ 2 * sinhHalfMoment f ^ 2 := by positivity
  linarith

/-- **The `69 / 2 = 34.5` Spectral Poincaré / Uncertainty Gap Law on the Prime-Blind Cone
(Upgraded from `27`, Deep into the `S / L > 27` Regime)**: -/
theorem sixty_nine_halves_l2_lt_spectralSecondMoment_of_cosh_zero_of_logVector_eq_zero
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hcosh : coshHalfMoment f = 0)
    (hint2 : Integrable fun r : ℝ => ‖paperFT (realWeilTestFn f hf hfc).1 r‖ ^ 2 * (2 * r ^ 2))
    {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log N) = 0 ∧
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log N) = 0)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log x) = 0 ∧
        EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log x) = 0)
    (hblind : logVector (realWeilTestFn f hf hfc) = 0)
    (hpos_l2 : 0 < ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) :
    (69 / 2) * (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) <
      spectralSecondMoment (realWeilTestFn f hf hfc).1 := by
  by_contra! hle
  have hcons :=
    unitStep_add_rightCellQuadratureDefect_add_bochnerResolventEnergy_add_sinh_sq_eq_zero_of_cosh_zero
      hf hfc hcosh hN1 hN
  have hcoerc :=
    one_twelve_hundredth_l2_le_bochnerResolventEnergy_add_rightCellQuadratureDefect_of_spectralSecondMoment_le_sixty_nine_halves_of_logVector_eq_zero
      (realWeilTestFn f hf hfc) hblind hint2 hN1 hN0 (fun n hn => hN n (by exact_mod_cast hn)) hle
  have hunit_zero :
      primeBlindCounterterm unitStepCountertermWeight (realWeilTestFn f hf hfc) = 0 := by
    unfold primeBlindCounterterm
    rw [hblind, map_zero]
  have hsinh_nonneg : 0 ≤ 2 * sinhHalfMoment f ^ 2 := by positivity
  linarith

/-- **Cutoff-Free `33` Kinetic Spectral Gap on `WeilEvenPolarTestFn` (Upgraded from `51 / 2 = 25.5`)**: -/
theorem WeilEvenPolarTestFn.thirty_three_l2_lt_spectralSecondMoment_of_unitStep_nonneg
    (g : WeilEvenPolarTestFn)
    (hint2 : Integrable fun r : ℝ => ‖paperFT g.1.1 r‖ ^ 2 * (2 * r ^ 2))
    (hunit : 0 ≤ primeBlindCounterterm unitStepCountertermWeight g.1)
    (hpos_l2 : 0 < ∫ u : ℝ, ‖g.1.1 u‖ ^ 2) :
    33 * (∫ u : ℝ, ‖g.1.1 u‖ ^ 2) < spectralSecondMoment g.1.1 := by
  by_contra! hle
  obtain ⟨N, hN2, hN0, hN⟩ := exists_support_cutoff_weilTest g.1
  have hN1 : 1 ≤ N := by omega
  have hcons :=
    WeilEvenPolarTestFn.unitStep_add_rightCellQuadratureDefect_add_bochnerResolventEnergy_eq_zero
      g hN1 hN
  have hcoerc :=
    one_one_fiftieth_l2_le_bochnerResolventEnergy_add_rightCellQuadratureDefect_of_spectralSecondMoment_le_thirty_three
      g.1 hint2 hN1 hN0 (fun n hn => hN n (by exact_mod_cast hn)) hle
  linarith

/-- **Cutoff-Free `69 / 2 = 34.5` Kinetic Spectral Gap on `WeilEvenPolarTestFn` with Nonnegative Log-Values
(Upgraded from `27`)**: -/
theorem WeilEvenPolarTestFn.sixty_nine_halves_l2_lt_spectralSecondMoment_of_logValue_nonneg
    (g : WeilEvenPolarTestFn)
    (hint2 : Integrable fun r : ℝ => ‖paperFT g.1.1 r‖ ^ 2 * (2 * r ^ 2))
    (hpos : ∀ n : ℕ, 2 ≤ n → 0 ≤ logValue g.1.1 n)
    (hpos_l2 : 0 < ∫ u : ℝ, ‖g.1.1 u‖ ^ 2) :
    (69 / 2) * (∫ u : ℝ, ‖g.1.1 u‖ ^ 2) < spectralSecondMoment g.1.1 := by
  by_contra! hle
  obtain ⟨N, hN2, hN0, hN⟩ := exists_support_cutoff_weilTest g.1
  have hN1 : 1 ≤ N := by omega
  have hcons :=
    WeilEvenPolarTestFn.unitStep_add_rightCellQuadratureDefect_add_bochnerResolventEnergy_eq_zero
      g hN1 hN
  have hpos_Icc : ∀ n ∈ Finset.Icc 2 N, 0 ≤ logValue g.1.1 n :=
    fun n hn => hpos n (Finset.mem_Icc.mp hn).1
  have hcoerc :=
    one_twelve_hundredth_l2_le_bochnerResolventEnergy_add_rightCellQuadratureDefect_of_spectralSecondMoment_le_sixty_nine_halves_of_logValue_nonneg
      g.1 hint2 hN1 hN0 (fun n hn => hN n (by exact_mod_cast hn)) hpos_Icc hle
  have hunit_nonneg : 0 ≤ primeBlindCounterterm unitStepCountertermWeight g.1 := by
    rw [primeBlindCounterterm_eq_sum_Icc unitStepCountertermWeight g.1
      (fun n hn => hN n (by exact_mod_cast hn))]
    refine Finset.sum_nonneg fun n hn => ?_
    have hn_mem := Finset.mem_Icc.mp hn
    unfold unitStepCountertermWeight
    rw [if_pos hn_mem.1]
    exact mul_nonneg zero_le_one (hpos n hn_mem.1)
  linarith

/-- **Cutoff-Free `69 / 2 = 34.5` Kinetic Spectral Gap on Prime-Blind `WeilEvenPolarTestFn` (`logVector g.1 = 0`)
(Upgraded from `27`, Deep into the `S / L > 27` Regime)**: -/
theorem WeilEvenPolarTestFn.sixty_nine_halves_l2_lt_spectralSecondMoment_of_logVector_eq_zero
    (g : WeilEvenPolarTestFn) (hblind : logVector g.1 = 0)
    (hint2 : Integrable fun r : ℝ => ‖paperFT g.1.1 r‖ ^ 2 * (2 * r ^ 2))
    (hpos_l2 : 0 < ∫ u : ℝ, ‖g.1.1 u‖ ^ 2) :
    (69 / 2) * (∫ u : ℝ, ‖g.1.1 u‖ ^ 2) < spectralSecondMoment g.1.1 := by
  by_contra! hle
  obtain ⟨N, hN2, hN0, hN⟩ := exists_support_cutoff_weilTest g.1
  have hN1 : 1 ≤ N := by omega
  have hcons :=
    WeilEvenPolarTestFn.rightCellQuadratureDefect_add_bochnerResolventEnergy_eq_zero_of_logVector_eq_zero
      g hblind hN1 hN
  have hcoerc :=
    one_twelve_hundredth_l2_le_bochnerResolventEnergy_add_rightCellQuadratureDefect_of_spectralSecondMoment_le_sixty_nine_halves_of_logVector_eq_zero
      g.1 hblind hint2 hN1 hN0 (fun n hn => hN n (by exact_mod_cast hn)) hle
  linarith

/-- **Cutoff-Free `69 / 2 = 34.5` Kinetic Spectral Gap on Prime-Blind `SmoothEvenPolarTestFn`**: -/
theorem SmoothEvenPolarTestFn.sixty_nine_halves_l2_lt_spectralSecondMoment_of_logVector_eq_zero
    (f : SmoothEvenPolarTestFn) (hblind : logVector f.1.1 = 0)
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1.1.1 r‖ ^ 2 * (2 * r ^ 2))
    (hpos_l2 : 0 < ∫ u : ℝ, ‖f.1.1.1 u‖ ^ 2) :
    (69 / 2) * (∫ u : ℝ, ‖f.1.1.1 u‖ ^ 2) < spectralSecondMoment f.1.1.1 :=
  WeilEvenPolarTestFn.sixty_nine_halves_l2_lt_spectralSecondMoment_of_logVector_eq_zero
    f.1 hblind hint2 hpos_l2

/-- **Cutoff-Free `69 / 2 = 34.5` Kinetic Spectral Gap on Prime-Blind Real Primitive-Hyperplane Tests**: -/
theorem sixty_nine_halves_l2_lt_spectralSecondMoment_of_cosh_zero_of_logVector_eq_zero_unconditional
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hcosh : coshHalfMoment f = 0)
    (hint2 : Integrable fun r : ℝ => ‖paperFT (realWeilTestFn f hf hfc).1 r‖ ^ 2 * (2 * r ^ 2))
    (hblind : logVector (realWeilTestFn f hf hfc) = 0)
    (hpos_l2 : 0 < ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) :
    (69 / 2) * (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) <
      spectralSecondMoment (realWeilTestFn f hf hfc).1 := by
  obtain ⟨N, hN2, hN0, hN⟩ := exists_support_cutoff_weilTest (realWeilTestFn f hf hfc)
  exact sixty_nine_halves_l2_lt_spectralSecondMoment_of_cosh_zero_of_logVector_eq_zero
    hf hfc hcosh hint2 (by omega) hN0 hN hblind hpos_l2

/-- **Joint Single-Source Mixture Purification with `evenBlindMinimum` and the `69 / 2 = 34.5` Spectral Gap**: -/
theorem exists_single_smooth_blind_purification_with_thirty_four_point_five_gap
    (c : WeilTestFn →₀ ℝ) (hc : ∀ g, 0 ≤ c g)
    (hblind_c : linearCombination ℝ logVector c = 0) :
    ∃ (f : SmoothEvenPolarTestFn) (a : SuzukiPositiveAperture)
      (u : CCMArchimedeanFormDomain a) (N : ℕ),
      2 ≤ N ∧
      logVector f.1.1 = 0 ∧
      weilArchRe (EF.weilTest f.1.1.1 f.1.1.1) = fullMixtureEnergy c ∧
      evenBlindMinimum a * ‖ccmArchimedeanFormToAperture a u‖ ^ 2 ≤ fullMixtureEnergy c ∧
      rightCellQuadratureDefect (weilContinuumLogProfile f.1.1.1) N +
        bochnerResolventEnergy (EF.weilTest f.1.1.1 f.1.1.1) = 0 ∧
      (∑ n ∈ Finset.Icc 3 N,
          ∫ x in ((n : ℝ) - 1)..(n : ℝ),
            (weilSymmetricLogNumerator f.1.1.1 x -
                cellSecant (weilSymmetricLogNumerator f.1.1.1) n x) /
              Real.sqrt x) ≤
        (79 / 100) * (∫ x : ℝ, ‖f.1.1.1 x‖ ^ 2) +
          (31 / 5) * bochnerResolventEnergy (EF.weilTest f.1.1.1 f.1.1.1) ∧
      (Integrable (fun r : ℝ => ‖paperFT f.1.1.1 r‖ ^ 2 * (2 * r ^ 2)) →
        0 < (∫ x : ℝ, ‖f.1.1.1 x‖ ^ 2) →
        (69 / 2) * (∫ x : ℝ, ‖f.1.1.1 x‖ ^ 2) < spectralSecondMoment f.1.1.1) := by
  obtain ⟨f, a, u, N, hN2, hf0, hfe, hmin, hcons, htail, _⟩ :=
    exists_single_smooth_blind_purification_with_clamped_conservation c hc hblind_c
  exact ⟨f, a, u, N, hN2, hf0, hfe, hmin, hcons, htail,
    fun hint2 hpos =>
      SmoothEvenPolarTestFn.sixty_nine_halves_l2_lt_spectralSecondMoment_of_logVector_eq_zero
        f hf0 hint2 hpos⟩

/-! ## Section 3: Exact Vanishing of Prime-Blind Tail Secants (`n ≥ 3`), `S(f)`-Free Multi-Cell Clamping on `[2, M]`, and Arbitrary-`M` `O(M^{-3/2})` Far-Tail Variance Localization -/

/-- **Exact Vanishing of `weilSymmetricLogNumerator f.1 (n : ℝ)` at Integer Nodes `2 ≤ n` on the Prime-Blind Cone**:
for every prime-blind `f : WeilTestFn` (`logVector f = 0`) and every `2 ≤ n`,
`weilSymmetricLogNumerator f.1 (n : ℝ) = 0`. -/
theorem weilSymmetricLogNumerator_natCast_eq_zero_of_logVector_eq_zero
    (f : WeilTestFn) (hblind : logVector f = 0) {n : ℕ} (hn : 2 ≤ n) :
    weilSymmetricLogNumerator f.1 (n : ℝ) = 0 := by
  have hlog : logValue f.1 n = 0 := by
    rw [← logVector_apply f ⟨n, hn⟩, hblind, Finsupp.zero_apply]
  rw [weilSymmetricLogNumerator_natCast_eq_sqrt_mul_logValue f.1 (by omega : 1 ≤ n),
    hlog, mul_zero]

/-- **Exact Identical Vanishing of Tail Secants (`3 ≤ n`) on the Prime-Blind Cone**:
for every prime-blind `f : WeilTestFn` (`logVector f = 0`), every tail cell `3 ≤ n`, and every `x : ℝ`,
both endpoint values `C_f(n - 1)` and `C_f(n)` vanish, so
`cellSecant (weilSymmetricLogNumerator f.1) n x = 0` identically! -/
theorem cellSecant_weilSymmetricLogNumerator_eq_zero_of_logVector_eq_zero
    (f : WeilTestFn) (hblind : logVector f = 0) {n : ℕ} (hn : 3 ≤ n) (x : ℝ) :
    cellSecant (weilSymmetricLogNumerator f.1) n x = 0 := by
  unfold cellSecant
  have h1 : ((n : ℝ) - 1) = ((n - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  rw [h1,
    weilSymmetricLogNumerator_natCast_eq_zero_of_logVector_eq_zero f hblind (by omega : 2 ≤ n - 1),
    weilSymmetricLogNumerator_natCast_eq_zero_of_logVector_eq_zero f hblind (by omega : 2 ≤ n)]
  ring

/-- **`S(f)`-Free Physical-Space Cell Lower Bound on the Prime-Blind Cone (`3 ≤ n`)**:
because `cellSecant (weilSymmetricLogNumerator f.1) n x = 0` identically for `3 ≤ n` when
`logVector f = 0`, and `|weilSymmetricLogNumerator f.1 x| ≤ 2 * ∫ ‖f.1‖²`, each tail cell integral
is bounded below by `-4 * (√n - √(n - 1)) * ∫ ‖f.1‖²` with **zero `spectralSecondMoment` dependence**. -/
theorem neg_four_mul_sqrt_sub_pred_l2_le_cell_integral_of_logVector_eq_zero
    (f : WeilTestFn) (hblind : logVector f = 0) {n : ℕ} (hn : 3 ≤ n) :
    -4 * (Real.sqrt n - Real.sqrt ((n : ℝ) - 1)) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) ≤
      ∫ x in ((n : ℝ) - 1)..(n : ℝ),
        (weilSymmetricLogNumerator f.1 x - cellSecant (weilSymmetricLogNumerator f.1) n x) /
          Real.sqrt x := by
  let L := ∫ u : ℝ, ‖f.1 u‖ ^ 2
  have hn2 : 2 ≤ n := by omega
  have hn2_real : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have hn_le : (n : ℝ) - 1 ≤ (n : ℝ) := by linarith
  have hlhs_eq :
      -4 * (Real.sqrt n - Real.sqrt ((n : ℝ) - 1)) * L =
        ∫ x in ((n : ℝ) - 1)..(n : ℝ), (-2 * L) * (Real.sqrt x)⁻¹ := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral_inv_sqrt_cell hn2]
    ring
  rw [hlhs_eq]
  have hint_low : IntervalIntegrable
      (fun x : ℝ => (-2 * L) * (Real.sqrt x)⁻¹) volume ((n : ℝ) - 1) (n : ℝ) := by
    refine ContinuousOn.intervalIntegrable (continuousOn_const.mul ?_)
    rw [uIcc_of_le hn_le]
    exact ContinuousOn.inv₀ (Real.continuous_sqrt.continuousOn) fun x hx =>
      ne_of_gt (Real.sqrt_pos.mpr (by linarith [hx.1, hn2_real]))
  have hint_high : IntervalIntegrable
      (fun x : ℝ =>
        (weilSymmetricLogNumerator f.1 x - cellSecant (weilSymmetricLogNumerator f.1) n x) /
          Real.sqrt x)
      volume ((n : ℝ) - 1) (n : ℝ) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hn_le]
    refine ContinuousOn.div ?_ (Real.continuous_sqrt.continuousOn) ?_
    · refine ((continuousOn_weilSymmetricLogNumerator f).mono ?_).sub ?_
      · intro x hx; exact mem_Ici.mpr (by linarith [hx.1, hn2_real])
      · unfold cellSecant; fun_prop
    · intro x hx
      exact ne_of_gt (Real.sqrt_pos.mpr (by linarith [hx.1, hn2_real]))
  refine intervalIntegral.integral_mono_on hn_le hint_low hint_high fun x hx => ?_
  rw [cellSecant_weilSymmetricLogNumerator_eq_zero_of_logVector_eq_zero f hblind hn x, sub_zero,
    div_eq_mul_inv]
  have hx_pos : 0 < Real.sqrt x := Real.sqrt_pos.mpr (by linarith [hx.1, hn2_real])
  have habs := (abs_le.mp (abs_weilSymmetricLogNumerator_le_two_mul_integral_norm_sq f x)).1
  exact mul_le_mul_of_nonneg_right (by dsimp [L]; linarith) (inv_nonneg.mpr hx_pos.le)

/-- Telescoping identity `∑ n ∈ Finset.Icc 3 M, (√n - √(n - 1)) = √M - √2` for `2 ≤ M`. -/
theorem sum_Icc_three_sqrt_sub_pred_eq {M : ℕ} (hM : 2 ≤ M) :
    (∑ n ∈ Finset.Icc 3 M, (Real.sqrt n - Real.sqrt ((n : ℝ) - 1))) =
      Real.sqrt M - Real.sqrt 2 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hM
  induction k with
  | zero =>
    rw [Finset.Icc_eq_empty (by omega : ¬ 3 ≤ 2 + 0), Finset.sum_empty]
    norm_num
  | succ k ih =>
    have hIcc : Finset.Icc 3 (2 + (k + 1)) =
        insert (2 + (k + 1)) (Finset.Icc 3 (2 + k)) := by
      ext m
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hnotmem : 2 + (k + 1) ∉ Finset.Icc 3 (2 + k) := by
      simp only [Finset.mem_Icc]
      omega
    rw [hIcc, Finset.sum_insert hnotmem, ih (by omega : 2 ≤ 2 + k)]
    have hcast : ((2 + (k + 1) : ℕ) : ℝ) - 1 = ((2 + k : ℕ) : ℝ) := by
      push_cast
      ring
    rw [hcast]
    ring

/-- **`S(f)`-Free Multi-Cell Telescoping Lower Bound on `Finset.Icc 3 M` for Prime-Blind Tests (`logVector f = 0`)**:
for every prime-blind `f : WeilTestFn` and `2 ≤ M`,
`-4 * (√M - √2) * ∫ ‖f.1‖² ≤ ∑ n ∈ Finset.Icc 3 M, ∫ x in (n - 1)..n, (C_f x - cellSecant C_f n x) / √x`. -/
theorem neg_four_mul_sqrt_sub_sqrt_two_l2_le_sum_Icc_three_of_logVector_eq_zero
    (f : WeilTestFn) (hblind : logVector f = 0) {M : ℕ} (hM : 2 ≤ M) :
    -4 * (Real.sqrt M - Real.sqrt 2) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) ≤
      ∑ n ∈ Finset.Icc 3 M,
        ∫ x in ((n : ℝ) - 1)..(n : ℝ),
          (weilSymmetricLogNumerator f.1 x - cellSecant (weilSymmetricLogNumerator f.1) n x) /
            Real.sqrt x := by
  have hsum :
      (∑ n ∈ Finset.Icc 3 M,
        -4 * (Real.sqrt n - Real.sqrt ((n : ℝ) - 1)) * (∫ u : ℝ, ‖f.1 u‖ ^ 2)) ≤
      ∑ n ∈ Finset.Icc 3 M,
        ∫ x in ((n : ℝ) - 1)..(n : ℝ),
          (weilSymmetricLogNumerator f.1 x - cellSecant (weilSymmetricLogNumerator f.1) n x) /
            Real.sqrt x := by
    refine Finset.sum_le_sum fun n hn => ?_
    exact neg_four_mul_sqrt_sub_pred_l2_le_cell_integral_of_logVector_eq_zero
      f hblind (Finset.mem_Icc.mp hn).1
  have hlhs :
      (∑ n ∈ Finset.Icc 3 M,
        -4 * (Real.sqrt n - Real.sqrt ((n : ℝ) - 1)) * (∫ u : ℝ, ‖f.1 u‖ ^ 2)) =
      -4 * (Real.sqrt M - Real.sqrt 2) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) := by
    calc (∑ n ∈ Finset.Icc 3 M,
          -4 * (Real.sqrt n - Real.sqrt ((n : ℝ) - 1)) * (∫ u : ℝ, ‖f.1 u‖ ^ 2))
      _ = ∑ n ∈ Finset.Icc 3 M,
          (Real.sqrt n - Real.sqrt ((n : ℝ) - 1)) * (-4 * ∫ u : ℝ, ‖f.1 u‖ ^ 2) := by
          refine Finset.sum_congr rfl fun n _ => by ring
      _ = (∑ n ∈ Finset.Icc 3 M, (Real.sqrt n - Real.sqrt ((n : ℝ) - 1))) *
          (-4 * ∫ u : ℝ, ‖f.1 u‖ ^ 2) := (Finset.sum_mul _ _ _).symm
      _ = -4 * (Real.sqrt M - Real.sqrt 2) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) := by
          rw [sum_Icc_three_sqrt_sub_pred_eq hM]
          ring
  linarith

/-- **Arbitrary-`M` Far-Tail `O(M^{-3/2})` Sum Bound on `Finset.Icc (M + 1) N` (`4 ≤ M`)**:
for every `4 ≤ M` and `N : ℕ`,
`∑ n ∈ Finset.Icc (M + 1) N, hermiteQuinticCellWeight n ≤ (811 / 14580) * ((1 / M) * (1 / √M))`. -/
theorem sum_Icc_succ_hermiteQuinticCellWeight_le {M : ℕ} (hM : 4 ≤ M) (N : ℕ) :
    (∑ n ∈ Finset.Icc (M + 1) N, hermiteQuinticCellWeight n) ≤
      (811 / 14580) * ((1 / (M : ℝ)) * (1 / Real.sqrt (M : ℝ))) := by
  let g : ℕ → ℝ := fun n => (1 / ((n : ℝ) - 1)) * (1 / Real.sqrt ((n : ℝ) - 1))
  have htel_all : ∀ k : ℕ,
      (∑ n ∈ Finset.Icc (M + 1) ((M + 1) + k), (g n - g (n + 1))) =
        g (M + 1) - g ((M + 1) + k + 1) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hIcc : Finset.Icc (M + 1) ((M + 1) + (k + 1)) =
          insert ((M + 1) + (k + 1)) (Finset.Icc (M + 1) ((M + 1) + k)) := by
        ext m
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      have hnotmem : (M + 1) + (k + 1) ∉ Finset.Icc (M + 1) ((M + 1) + k) := by
        simp only [Finset.mem_Icc]
        omega
      rw [hIcc, Finset.sum_insert hnotmem, ih, ← Nat.add_assoc]
      ring
  have hle :
      (∑ n ∈ Finset.Icc (M + 1) N, hermiteQuinticCellWeight n) ≤
        (811 / 14580) * ∑ n ∈ Finset.Icc (M + 1) N, (g n - g (n + 1)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun n hn => ?_
    rw [Finset.mem_Icc] at hn
    have hstep := hermiteQuinticCellWeight_le_of_five_le (by omega : 5 ≤ n)
    have hg_succ : g (n + 1) = (1 / (n : ℝ)) * (1 / Real.sqrt (n : ℝ)) := by
      dsimp [g]
      push_cast
      rw [add_sub_cancel_right]
    rw [hg_succ]
    exact hstep
  by_cases hN : M + 1 ≤ N
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
    have htel := htel_all k
    have hgM : g (M + 1) = (1 / (M : ℝ)) * (1 / Real.sqrt (M : ℝ)) := by
      dsimp [g]
      push_cast
      rw [add_sub_cancel_right]
    have hg_nonneg : 0 ≤ g ((M + 1) + k + 1) := by
      dsimp [g]
      have hpos : (0 : ℝ) ≤ ((M + 1) + k + 1 : ℕ) - 1 := by
        push_cast
        linarith
      positivity
    rw [htel, hgM] at hle
    linarith
  · rw [Finset.Icc_eq_empty hN, Finset.sum_empty]
    positivity

/-- **The Arbitrary-`M` `O(M^{-3/2})` Far-Tail Geometric-Mean Law (`Finset.Icc (M + 1) N`, `4 ≤ M`)**:
for every `f : WeilTestFn`, `4 ≤ M`, and `N : ℕ`, the high-frequency curvature slope on the far tail
`n ∈ [M + 1, N]` decays as `(811 / 14580) / (M √M) = O(M^{-3/2})`:
`-((811 / 14580) * ((1 / M) * (1 / √M))) * √(S(S + 2L)) ≤ ∑ n ∈ Finset.Icc (M + 1) N, ∫ x in (n - 1)..n, (C_f x - cellSecant C_f n x) / √x`. -/
theorem neg_far_tail_geom_le_sum_Icc_succ
    (f : WeilTestFn)
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))
    {M : ℕ} (hM : 4 ≤ M) (N : ℕ) :
    -((811 / 14580 : ℝ) * ((1 / (M : ℝ)) * (1 / Real.sqrt (M : ℝ)))) *
        Real.sqrt
          (spectralSecondMoment f.1 *
            (spectralSecondMoment f.1 + 2 * ∫ u : ℝ, ‖f.1 u‖ ^ 2)) ≤
      ∑ n ∈ Finset.Icc (M + 1) N,
        ∫ x in ((n : ℝ) - 1)..(n : ℝ),
          (weilSymmetricLogNumerator f.1 x - cellSecant (weilSymmetricLogNumerator f.1) n x) /
            Real.sqrt x := by
  let S := spectralSecondMoment f.1
  let L := ∫ u : ℝ, ‖f.1 u‖ ^ 2
  let W := (811 / 14580 : ℝ) * ((1 / (M : ℝ)) * (1 / Real.sqrt (M : ℝ)))
  have hS_nonneg : 0 ≤ S := spectralSecondMoment_nonneg f.1
  have hL_nonneg : 0 ≤ L := integral_nonneg fun _ => sq_nonneg _
  have hM_pos : (0 : ℝ) < (M : ℝ) := by positivity
  have hW_pos : 0 < W := by dsimp [W]; positivity
  have hvar : ∀ {b : ℝ}, 0 < b →
      -W * ((b + 1 / (4 * b)) * S + 2 * b * L) ≤
        ∑ n ∈ Finset.Icc (M + 1) N,
          ∫ x in ((n : ℝ) - 1)..(n : ℝ),
            (weilSymmetricLogNumerator f.1 x - cellSecant (weilSymmetricLogNumerator f.1) n x) /
              Real.sqrt x := by
    intro b hb
    let K := (b + 1 / (4 * b)) * S + 2 * b * L
    have hK_nonneg : 0 ≤ K := by dsimp only [K]; positivity
    have hcell_le : ∀ n ∈ Finset.Icc (M + 1) N,
        -K * hermiteQuinticCellWeight n ≤
          ∫ x in ((n : ℝ) - 1)..(n : ℝ),
            (weilSymmetricLogNumerator f.1 x - cellSecant (weilSymmetricLogNumerator f.1) n x) /
              Real.sqrt x := by
      intro n hn
      have hnM : M + 1 ≤ n := (Finset.mem_Icc.mp hn).1
      have hn2 : 2 ≤ n := by omega
      have hn2_real : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
      have hn_le : (n : ℝ) - 1 ≤ (n : ℝ) := by linarith
      have hint_low : IntervalIntegrable
          (fun x => -K * ((Real.log x - cellSecant Real.log n x) / Real.sqrt x))
          volume ((n : ℝ) - 1) (n : ℝ) := by
        refine ContinuousOn.intervalIntegrable ?_
        rw [uIcc_of_le hn_le]
        refine continuousOn_const.mul (ContinuousOn.div ?_ (Real.continuous_sqrt.continuousOn) ?_)
        · refine (Real.continuousOn_log.mono ?_).sub ?_
          · intro x hx
            have hx_pos : 0 < x := by linarith [hx.1, hn2_real]
            exact hx_pos.ne'
          · unfold cellSecant; fun_prop
        · intro x hx
          have hx_pos : 0 < x := by linarith [hx.1, hn2_real]
          exact (Real.sqrt_pos.mpr hx_pos).ne'
      have hint_high : IntervalIntegrable
          (fun x =>
            (weilSymmetricLogNumerator f.1 x - cellSecant (weilSymmetricLogNumerator f.1) n x) /
              Real.sqrt x)
          volume ((n : ℝ) - 1) (n : ℝ) := by
        refine ContinuousOn.intervalIntegrable ?_
        rw [uIcc_of_le hn_le]
        refine ContinuousOn.div ?_ (Real.continuous_sqrt.continuousOn) ?_
        · refine ((continuousOn_weilSymmetricLogNumerator f).mono ?_).sub ?_
          · intro x hx; exact mem_Ici.mpr (by linarith [hx.1, hn2_real])
          · unfold cellSecant; fun_prop
        · intro x hx
          have hx_pos : 0 < x := by linarith [hx.1, hn2_real]
          exact (Real.sqrt_pos.mpr hx_pos).ne'
      have hmono := intervalIntegral.integral_mono_on hn_le hint_low hint_high fun x hx => by
        have hx_pos : 0 < Real.sqrt x := Real.sqrt_pos.mpr (by linarith [hx.1, hn2_real])
        have habs := (abs_le.mp
          (abs_weilSymmetricLogNumerator_sub_cellSecant_le_variational f hint2 hb hn2 hx)).1
        have hdiv := div_le_div_of_nonneg_right habs hx_pos.le
        dsimp only [K, S, L]
        linarith [show -(((b + 1 / (4 * b)) * spectralSecondMoment f.1 +
            2 * b * ∫ u : ℝ, ‖f.1 u‖ ^ 2) * (Real.log x - cellSecant Real.log n x)) /
            Real.sqrt x =
          -((b + 1 / (4 * b)) * spectralSecondMoment f.1 + 2 * b * ∫ u : ℝ, ‖f.1 u‖ ^ 2) *
            ((Real.log x - cellSecant Real.log n x) / Real.sqrt x) by ring]
      rw [intervalIntegral.integral_const_mul] at hmono
      have hweight := mul_le_mul_of_nonneg_left
        (integral_log_sub_cellSecant_div_sqrt_le_hermiteQuinticCellWeight hn2) hK_nonneg
      linarith
    have hsum := Finset.sum_le_sum hcell_le
    rw [← Finset.mul_sum] at hsum
    have htail := mul_le_mul_of_nonneg_left
      (sum_Icc_succ_hermiteQuinticCellWeight_le hM N) hK_nonneg
    dsimp [W] at htail ⊢
    linarith
  change -W * Real.sqrt (S * (S + 2 * L)) ≤ _
  rcases eq_or_lt_of_le hS_nonneg with hS0 | hS_pos
  · rw [← hS0, zero_mul, Real.sqrt_zero, mul_zero]
    refine le_of_forall_pos_le_add fun ε hε => ?_
    rcases eq_or_lt_of_le hL_nonneg with hL0 | hL_pos
    · have h1 := hvar zero_lt_one
      rw [← hS0, ← hL0] at h1
      linarith
    · let b := ε / (2 * W * L)
      have hb_pos : 0 < b := by dsimp only [b]; positivity
      have h1 := hvar hb_pos
      rw [← hS0, mul_zero, zero_add] at h1
      have h2 : W * (2 * b * L) = ε := by
        dsimp only [b]
        have hW_ne : W ≠ 0 := hW_pos.ne'
        have hL_ne : L ≠ 0 := hL_pos.ne'
        field_simp [hW_ne, hL_ne]
      linarith
  · have hSL_pos : 0 < S + 2 * L := by linarith
    have hprod_pos : 0 < S * (S + 2 * L) := mul_pos hS_pos hSL_pos
    have hsqrt_pos : 0 < Real.sqrt (S * (S + 2 * L)) := Real.sqrt_pos.mpr hprod_pos
    let b := S / (2 * Real.sqrt (S * (S + 2 * L)))
    have hb_pos : 0 < b := div_pos hS_pos (mul_pos zero_lt_two hsqrt_pos)
    have h1 := hvar hb_pos
    have hopt : (b + 1 / (4 * b)) * S + 2 * b * L = Real.sqrt (S * (S + 2 * L)) := by
      dsimp only [b]
      have hS_ne : S ≠ 0 := hS_pos.ne'
      have hsqrt_ne : Real.sqrt (S * (S + 2 * L)) ≠ 0 := hsqrt_pos.ne'
      have hsq : Real.sqrt (S * (S + 2 * L)) ^ 2 = S * (S + 2 * L) :=
        Real.sq_sqrt hprod_pos.le
      calc (S / (2 * Real.sqrt (S * (S + 2 * L))) +
              1 / (4 * (S / (2 * Real.sqrt (S * (S + 2 * L)))))) * S +
            2 * (S / (2 * Real.sqrt (S * (S + 2 * L)))) * L
        _ = (S * (S + 2 * L) + Real.sqrt (S * (S + 2 * L)) ^ 2) /
              (2 * Real.sqrt (S * (S + 2 * L))) := by
            field_simp [hS_ne, hsqrt_ne]
            ring
        _ = (Real.sqrt (S * (S + 2 * L)) ^ 2 + Real.sqrt (S * (S + 2 * L)) ^ 2) /
              (2 * Real.sqrt (S * (S + 2 * L))) := by rw [hsq]
        _ = Real.sqrt (S * (S + 2 * L)) := by
            field_simp [hsqrt_ne]
            ring
    rw [hopt] at h1
    exact h1

/-- **Multi-Cell Clamped All-Ratio Conservation Law on Prime-Blind Primitive Tests (`4 ≤ M ≤ N`)**:
for every prime-blind `f ∈ C²_c(ℝ)` (`logVector F = 0`) with `coshHalfMoment f = 0` and any splitting
threshold `4 ≤ M ≤ N`, clamping the first `M` cells `[1, M]` in physical space (`S`-free) and
applying the Quintic Chebyshev bound only on `[M + 1, N]` reduces the high-frequency slope on
`√(S(S + 2L))` from `71 / 3600` to `(811 / 14580) / (M √M) = O(M^{-3/2})`! -/
theorem multi_cell_clamped_conservation_bound_of_logVector_eq_zero
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hcosh : coshHalfMoment f = 0)
    (hint2 : Integrable fun r : ℝ => ‖paperFT (realWeilTestFn f hf hfc).1 r‖ ^ 2 * (2 * r ^ 2))
    {M N : ℕ} (hM : 4 ≤ M) (hMN : M ≤ N)
    (hN0 : EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log N) = 0 ∧
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log N) = 0)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log x) = 0 ∧
        EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log x) = 0)
    (hblind : logVector (realWeilTestFn f hf hfc) = 0) :
    (1261 / 1440) * (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) +
        bochnerResolventEnergy
          (EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1) +
        2 * sinhHalfMoment f ^ 2 ≤
      min ((7 / 480 : ℝ) * spectralSecondMoment (realWeilTestFn f hf hfc).1)
          ((91 / 50) * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) +
        4 * (Real.sqrt M - Real.sqrt 2) * (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) +
        ((811 / 14580 : ℝ) * ((1 / (M : ℝ)) * (1 / Real.sqrt (M : ℝ)))) *
          Real.sqrt
            (spectralSecondMoment (realWeilTestFn f hf hfc).1 *
              (spectralSecondMoment (realWeilTestFn f hf hfc).1 +
                2 * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2)) := by
  let F := realWeilTestFn f hf hfc
  have hN1 : 1 ≤ N := by omega
  have hN2 : 2 ≤ N := by omega
  have hcons :=
    unitStep_add_rightCellQuadratureDefect_add_bochnerResolventEnergy_add_sinh_sq_eq_zero_of_cosh_zero
      hf hfc hcosh hN1 hN
  have hunit_zero : primeBlindCounterterm unitStepCountertermWeight F = 0 := by
    unfold primeBlindCounterterm
    rw [hblind, map_zero]
  have h1 :=
    twelve_sixty_one_fourteen_fortieths_l2_add_secantNumerator_le_rightCellQuadratureDefect_of_logVector_eq_zero
      F hblind hN1 hN0 (fun n hn => hN n (by exact_mod_cast hn))
  have hcell2 := neg_min_first_cell_le_integral_one_two F hint2
  have hmid :=
    neg_four_mul_sqrt_sub_sqrt_two_l2_le_sum_Icc_three_of_logVector_eq_zero
      F hblind (by omega : 2 ≤ M)
  have hfar := neg_far_tail_geom_le_sum_Icc_succ F hint2 hM N
  have hsplit_sum :
      secantNumeratorCellDefect F.1 N =
        (∫ x in (1 : ℝ)..2,
          (weilSymmetricLogNumerator F.1 x - cellSecant (weilSymmetricLogNumerator F.1) 2 x) /
            Real.sqrt x) +
        (∑ n ∈ Finset.Icc 3 M,
          ∫ x in ((n : ℝ) - 1)..(n : ℝ),
            (weilSymmetricLogNumerator F.1 x - cellSecant (weilSymmetricLogNumerator F.1) n x) /
              Real.sqrt x) +
        (∑ n ∈ Finset.Icc (M + 1) N,
          ∫ x in ((n : ℝ) - 1)..(n : ℝ),
            (weilSymmetricLogNumerator F.1 x - cellSecant (weilSymmetricLogNumerator F.1) n x) /
              Real.sqrt x) := by
    unfold secantNumeratorCellDefect
    rw [sum_Icc_two_eq_add_sum_Icc_three _ hN2]
    have hIcc_union : Finset.Icc 3 N = Finset.Icc 3 M ∪ Finset.Icc (M + 1) N := by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_union]
      omega
    have hdisj : Disjoint (Finset.Icc 3 M) (Finset.Icc (M + 1) N) := by
      rw [Finset.disjoint_left]
      intro n hn1 hn2
      simp only [Finset.mem_Icc] at hn1 hn2
      omega
    rw [hIcc_union, Finset.sum_union hdisj,
      show ((2 : ℕ) : ℝ) - 1 = 1 by norm_num, show ((2 : ℕ) : ℝ) = 2 by norm_num]
    ring
  linarith

end RHTower

end
