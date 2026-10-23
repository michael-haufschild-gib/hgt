import GaloisForLFunctions.RHTower.MarkovJointResolventEnvelopeAndPastThirtyFourPBAP

/-!
# Two-Cell (`[1, 3]`) Cosine-Log Spectral Telescoping, the `41 / 2880 + 31 / 2880 = 1 / 40` Resolvent + Secant Numerator Law, and Coercivity & Cutoff-Free `EWU` Spectral Gaps up to `43` and `45` for Route HF / PBAP

In `MarkovJointResolventEnvelopeAndPastThirtyFourPBAP`, combining the first-cell cosine-log quadrature
integral $I_2(r)$ on $[1, 2]$ with the Bochner–Poisson resolvent kernel $\frac{1/2}{1/4 + r^2}$ over
their shared denominator $(1/4 + r^2)$ established the Symmetric `71 / 3600` Resolvent + Secant
Numerator Law and pushed the critical kinetic spectral gap ratio from $S / L \le 27$ to
$S / L \le 69 / 2 = 34.5$ on the nonnegative log-value and prime-blind cones (`S / L ≤ 33` on the
general cone). In that decomposition, cell $n = 3$ ($[2, 3]$) was still bounded by the Quintic
Chebyshev logarithmic envelope ($\operatorname{hermiteQuinticCellWeight}(3) \approx 0.008819$),
which accounted for nearly $45\%$ of the entire tail curvature weight $71 / 3600 \approx 0.019722$.

In this module, we evaluate cell $n = 3$ ($[2, 3]$) **exactly** in spectral space and telescope the
two-cell cosine-log integral $I_2(r) + I_3(r)$ together with the Bochner–Poisson resolvent across
$[1, 3]$:

1. **Section 1 (Universal Degree-28 Alternating Taylor Hierarchy, 8th-Order Artanh Logarithm Bounds,
   and Exact Two-Cell `[1, 3]` Cosine-Log Spectral Telescoping):**
   - We extend the universal alternating Taylor polynomial hierarchy for $\sin\theta$, $1 - \cos\theta$,
     and $\theta\sin\theta$ up to **degree 28** (`sin_le_taylor_degree_seventeen_of_nonneg` through
     `taylor_degree_twenty_eight_le_one_sub_cos` and `mul_sin_ge_taylor_degree_twenty_eight`).
   - We prove the 8th-order artanh/Padé enclosures for $\log b - \log a$
     (`artanh_degree_seven_le_log_sub_log` and `log_sub_log_le_artanh_degree_nine`), yielding $10^{-9}$
     rational enclosures for $\log 2$ and $\log 3$ (`four_panel_artanh_log_two_lower`,
     `four_panel_artanh_log_two_upper`, `four_panel_artanh_log_three_lower`,
     `four_panel_artanh_log_three_upper`).
   - By the Fundamental Theorem of Calculus (`neg_mul_integral_two_three_cosLogProfile_sub_cellSecant_div_sqrt_eq`
     and `neg_mul_integral_one_three_cosLogProfile_sub_half_eq`), when $I_2(r) + I_3(r) + \frac{1/2}{1/4 + r^2}$
     is summed across $[1, 2] \cup [2, 3]$, **both the internal boundary antiderivative
     $\operatorname{cosLogAntideriv}(r, 2)$ (including $\sqrt{2}\,r\sin(r\log 2)$) and the origin
     resolvent boundary $\operatorname{cosLogAntideriv}(r, 1) = \frac{1/2}{1/4 + r^2}$ cancel
     identically**, leaving a pure even function of $r$ with strictly positive interior node weight
     $w_2 = \frac{4 + 12\sqrt{3} - 16\sqrt{2}}{3} > 0$:
     $$-\left(\frac{1}{4} + r^2\right)\bigl(I_2(r) + I_3(r)\bigr) - \frac{1}{2}
       = -\frac{1}{2} + 2(\sqrt{3} - 1)r^2 - \sqrt{3}\,r\sin(r\log 3)
         + \left(\sqrt{3} - \frac{2}{3}\sqrt{2} - \frac{8\sqrt{2} - 6\sqrt{3}}{3}r^2\right)\bigl(1 - \cos(r\log 3)\bigr)
         - \left(\frac{1}{4} + r^2\right)\frac{4 + 12\sqrt{3} - 16\sqrt{2}}{3}\bigl(1 - \cos(r\log 2)\bigr).$$

2. **Section 2 (The Global Two-Cell + Resolvent Envelope `-(41 / 2880) r² + 19 / 144 - (1 / 2) / (1 / 4 + r²) ≤ I_2(r) + I_3(r)`
   and the `41 / 2880 + 31 / 2880 = 1 / 40` Resolvent + Secant Numerator Law):**
   - Combining a three-interval degree-15 Bernstein positivity certificate on $r^2 \in [0, 18] \cup [18, 90] \cup [90, 116]$
     with a high-frequency Cauchy–Schwarz envelope on $r^2 \ge 116$ proves the global pointwise
     inequality (`two_cell_resolvent_envelope_le_integral_one_three_cosLogProfile`):
     $$\forall r \in \mathbb{R},\qquad
       -\frac{41}{2880} r^2 + \frac{19}{144} - \frac{1/2}{1/4 + r^2} \le I_2(r) + I_3(r).$$
   - Proving the clamped product-measure Fubini identity on cell $n = 3$ (`[2, 3]`)
     (`integral_two_three_weilSymmetricLogNumerator_sub_cellSecant_div_sqrt_eq_spectral`) and the
     sharp Quintic Chebyshev tail bound on $n \ge 4$
     (`sum_Icc_four_hermiteQuinticCellWeight_le : ∑_{n=4}^N hermiteQuinticCellWeight n ≤ 31 / 2880`)
     yields the **Two-Cell `41 / 2880 + 31 / 2880 = 1 / 40` Resolvent + Secant Numerator Law**
     (`nineteen_seventy_seconds_l2_sub_forty_one_second_sub_thirty_one_geom_le_bochnerResolventEnergy_add_secantNumeratorCellDefect`):
     $$\frac{19}{72} L - \frac{41}{2880} S - \frac{31}{2880}\sqrt{S(S + 2L)}
       \le \operatorname{bochnerResolventEnergy}(k_f) + \operatorname{secantNumeratorCellDefect}(f.1, N),$$
     reducing the total high-frequency slope from $\frac{71}{3600} + \frac{71}{3600} = \frac{71}{1800} \approx 0.039444$
     to $\frac{41}{2880} + \frac{31}{2880} = \frac{72}{2880} = \frac{1}{40} = 0.025$ (`-36.6%`!).

3. **Section 3 (Coercivity, Unconditional `0 ≤ markovEnergy`, and Cutoff-Free `EWU` Spectral Gaps up
   to `43` and `45`, Deep into the `S / L > 69 / 2 = 34.5` Regime):**
   - Combining the Two-Cell `1 / 40` Resolvent + Secant Numerator Law with the Four-Stage Secular
     Counterterm Surplus (`247 / 300` general, `1261 / 1440` nonnegative log-value / prime-blind)
     and the tangent bound $\sqrt{S(S + 2L)} \le \frac{3961}{3960} S + \frac{44}{45} L$ upgrades:
     - **General Cone Coercivity, Unconditional `0 ≤ markovEnergy F` on `coshHalfMoment f = 0`, and
       Spectral Gap Laws** from $S / L \le 33$ to **$S / L \le 43$**
       (`one_seven_hundredth_l2_le_bochnerResolventEnergy_add_rightCellQuadratureDefect_of_spectralSecondMoment_le_forty_three`,
       `markovEnergy_ofReal_nonneg_of_spectralSecondMoment_le_forty_three_of_cosh_zero`,
       `forty_three_l2_lt_spectralSecondMoment_of_cosh_zero_of_unitStep_nonneg`,
       `WeilEvenPolarTestFn.forty_three_l2_lt_spectralSecondMoment_of_unitStep_nonneg`).
     - **Nonnegative Log-Value Cone & Prime-Blind Cone (`logVector f = 0`) Coercivity, Unconditional
       `0 ≤ markovEnergy F`, and Cutoff-Free `EWU` Spectral Gap Laws** from $S / L \le 69 / 2 = 34.5$
       to **$S / L \le 45$** (`+10.5` full units past `69 / 2 = 34.5` and `+18` full units past `27`!)
       (`one_three_hundredth_l2_le_bochnerResolventEnergy_add_rightCellQuadratureDefect_of_spectralSecondMoment_le_forty_five_of_logValue_nonneg`,
       `one_three_hundredth_l2_le_bochnerResolventEnergy_add_rightCellQuadratureDefect_of_spectralSecondMoment_le_forty_five_of_logVector_eq_zero`,
       `markovEnergy_ofReal_nonneg_of_spectralSecondMoment_le_forty_five_of_cosh_zero_of_logValue_nonneg`,
       `forty_five_l2_lt_spectralSecondMoment_of_cosh_zero_of_logValue_nonneg`,
       `forty_five_l2_lt_spectralSecondMoment_of_cosh_zero_of_logVector_eq_zero`,
       `WeilEvenPolarTestFn.forty_five_l2_lt_spectralSecondMoment_of_logVector_eq_zero`,
       `SmoothEvenPolarTestFn.forty_five_l2_lt_spectralSecondMoment_of_logVector_eq_zero`,
       `exists_single_smooth_blind_purification_with_forty_five_gap`).
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

/-! ## Section 1: Universal Degree-28 Alternating Taylor Hierarchy, 8th-Order Artanh Logarithm Bounds, and Exact Two-Cell `[1, 3]` Cosine-Log Spectral Telescoping -/


/-- Step 17 (`f_17`): degree-17 alternating Taylor upper bound for `Real.sin θ` on `0 ≤ θ`. -/
theorem sin_le_taylor_degree_seventeen_of_nonneg {θ : ℝ} (hθ : 0 ≤ θ) :
    Real.sin θ ≤ θ - θ ^ 3 / 6 + θ ^ 5 / 120 - θ ^ 7 / 5040 + θ ^ 9 / 362880 - θ ^ 11 / 39916800 + θ ^ 13 / 6227020800 - θ ^ 15 / 1307674368000 + θ ^ 17 / 355687428096000 := by
  have h := nonneg_of_deriv_nonneg
    (f := fun t => (t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040 + t ^ 9 / 362880 - t ^ 11 / 39916800 + t ^ 13 / 6227020800 - t ^ 15 / 1307674368000 + t ^ 17 / 355687428096000) - Real.sin t)
    (f' := fun t => (1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720 + t ^ 8 / 40320 - t ^ 10 / 3628800 + t ^ 12 / 479001600 - t ^ 14 / 87178291200 + t ^ 16 / 20922789888000) - Real.cos t)
    (by norm_num [Real.sin_zero])
    (fun t => by
      refine ((((((((((hasDerivAt_id t).sub ((hasDerivAt_pow 3 t).div_const 6)).add ((hasDerivAt_pow 5 t).div_const 120)).sub ((hasDerivAt_pow 7 t).div_const 5040)).add ((hasDerivAt_pow 9 t).div_const 362880)).sub ((hasDerivAt_pow 11 t).div_const 39916800)).add ((hasDerivAt_pow 13 t).div_const 6227020800)).sub ((hasDerivAt_pow 15 t).div_const 1307674368000)).add ((hasDerivAt_pow 17 t).div_const 355687428096000)).sub (Real.hasDerivAt_sin t)).congr_deriv ?_
      norm_num
      ring)
    (fun t _ => by linarith [taylor_degree_sixteen_le_one_sub_cos t])
    hθ
  linarith

/-- Step 18 (`f_18`): degree-18 alternating Taylor upper bound for `1 - Real.cos θ` (`∀ θ : ℝ`). -/
theorem one_sub_cos_le_taylor_degree_eighteen (θ : ℝ) :
    1 - Real.cos θ ≤ θ ^ 2 / 2 - θ ^ 4 / 24 + θ ^ 6 / 720 - θ ^ 8 / 40320 + θ ^ 10 / 3628800 - θ ^ 12 / 479001600 + θ ^ 14 / 87178291200 - θ ^ 16 / 20922789888000 + θ ^ 18 / 6402373705728000 := by
  suffices h : ∀ u : ℝ, 0 ≤ u → 0 ≤ Real.cos u - (1 - u ^ 2 / 2 + u ^ 4 / 24 - u ^ 6 / 720 + u ^ 8 / 40320 - u ^ 10 / 3628800 + u ^ 12 / 479001600 - u ^ 14 / 87178291200 + u ^ 16 / 20922789888000 - u ^ 18 / 6402373705728000) by
    rcases le_total 0 θ with hθ | hθ
    · linarith [h θ hθ]
    · have hneg := h (-θ) (by linarith)
      have hev : 1 - (-θ) ^ 2 / 2 + (-θ) ^ 4 / 24 - (-θ) ^ 6 / 720 + (-θ) ^ 8 / 40320 - (-θ) ^ 10 / 3628800 + (-θ) ^ 12 / 479001600 - (-θ) ^ 14 / 87178291200 + (-θ) ^ 16 / 20922789888000 - (-θ) ^ 18 / 6402373705728000 = 1 - θ ^ 2 / 2 + θ ^ 4 / 24 - θ ^ 6 / 720 + θ ^ 8 / 40320 - θ ^ 10 / 3628800 + θ ^ 12 / 479001600 - θ ^ 14 / 87178291200 + θ ^ 16 / 20922789888000 - θ ^ 18 / 6402373705728000 := by ring
      rw [Real.cos_neg, hev] at hneg
      linarith
  intro u hu
  refine nonneg_of_deriv_nonneg
    (f := fun t => Real.cos t - (1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720 + t ^ 8 / 40320 - t ^ 10 / 3628800 + t ^ 12 / 479001600 - t ^ 14 / 87178291200 + t ^ 16 / 20922789888000 - t ^ 18 / 6402373705728000))
    (f' := fun t => -Real.sin t + (t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040 + t ^ 9 / 362880 - t ^ 11 / 39916800 + t ^ 13 / 6227020800 - t ^ 15 / 1307674368000 + t ^ 17 / 355687428096000))
    (by norm_num)
    (fun t => by
      refine ((Real.hasDerivAt_cos t).sub ((((((((((hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_pow 2 t).div_const 2)).add ((hasDerivAt_pow 4 t).div_const 24)).sub ((hasDerivAt_pow 6 t).div_const 720)).add ((hasDerivAt_pow 8 t).div_const 40320)).sub ((hasDerivAt_pow 10 t).div_const 3628800)).add ((hasDerivAt_pow 12 t).div_const 479001600)).sub ((hasDerivAt_pow 14 t).div_const 87178291200)).add ((hasDerivAt_pow 16 t).div_const 20922789888000)).sub ((hasDerivAt_pow 18 t).div_const 6402373705728000))).congr_deriv ?_
      norm_num
      ring)
    (fun t ht => by linarith [sin_le_taylor_degree_seventeen_of_nonneg ht])
    hu

/-- Step 19 (`f_19`): degree-19 alternating Taylor lower bound for `Real.sin θ` on `0 ≤ θ`. -/
theorem taylor_degree_nineteen_le_sin_of_nonneg {θ : ℝ} (hθ : 0 ≤ θ) :
    θ - θ ^ 3 / 6 + θ ^ 5 / 120 - θ ^ 7 / 5040 + θ ^ 9 / 362880 - θ ^ 11 / 39916800 + θ ^ 13 / 6227020800 - θ ^ 15 / 1307674368000 + θ ^ 17 / 355687428096000 - θ ^ 19 / 121645100408832000 ≤ Real.sin θ := by
  have h := nonneg_of_deriv_nonneg
    (f := fun t => Real.sin t - (t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040 + t ^ 9 / 362880 - t ^ 11 / 39916800 + t ^ 13 / 6227020800 - t ^ 15 / 1307674368000 + t ^ 17 / 355687428096000 - t ^ 19 / 121645100408832000))
    (f' := fun t => Real.cos t - (1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720 + t ^ 8 / 40320 - t ^ 10 / 3628800 + t ^ 12 / 479001600 - t ^ 14 / 87178291200 + t ^ 16 / 20922789888000 - t ^ 18 / 6402373705728000))
    (by norm_num [Real.sin_zero])
    (fun t => by
      refine ((Real.hasDerivAt_sin t).sub ((((((((((hasDerivAt_id t).sub ((hasDerivAt_pow 3 t).div_const 6)).add ((hasDerivAt_pow 5 t).div_const 120)).sub ((hasDerivAt_pow 7 t).div_const 5040)).add ((hasDerivAt_pow 9 t).div_const 362880)).sub ((hasDerivAt_pow 11 t).div_const 39916800)).add ((hasDerivAt_pow 13 t).div_const 6227020800)).sub ((hasDerivAt_pow 15 t).div_const 1307674368000)).add ((hasDerivAt_pow 17 t).div_const 355687428096000)).sub ((hasDerivAt_pow 19 t).div_const 121645100408832000))).congr_deriv ?_
      norm_num
      ring)
    (fun t _ => by linarith [one_sub_cos_le_taylor_degree_eighteen t])
    hθ
  linarith

/-- Step 20 (`f_20`): degree-20 alternating Taylor lower bound for `1 - Real.cos θ` (`∀ θ : ℝ`). -/
theorem taylor_degree_twenty_le_one_sub_cos (θ : ℝ) :
    θ ^ 2 / 2 - θ ^ 4 / 24 + θ ^ 6 / 720 - θ ^ 8 / 40320 + θ ^ 10 / 3628800 - θ ^ 12 / 479001600 + θ ^ 14 / 87178291200 - θ ^ 16 / 20922789888000 + θ ^ 18 / 6402373705728000 - θ ^ 20 / 2432902008176640000 ≤ 1 - Real.cos θ := by
  suffices h : ∀ u : ℝ, 0 ≤ u → 0 ≤ (1 - u ^ 2 / 2 + u ^ 4 / 24 - u ^ 6 / 720 + u ^ 8 / 40320 - u ^ 10 / 3628800 + u ^ 12 / 479001600 - u ^ 14 / 87178291200 + u ^ 16 / 20922789888000 - u ^ 18 / 6402373705728000 + u ^ 20 / 2432902008176640000) - Real.cos u by
    rcases le_total 0 θ with hθ | hθ
    · linarith [h θ hθ]
    · have hneg := h (-θ) (by linarith)
      have hev : 1 - (-θ) ^ 2 / 2 + (-θ) ^ 4 / 24 - (-θ) ^ 6 / 720 + (-θ) ^ 8 / 40320 - (-θ) ^ 10 / 3628800 + (-θ) ^ 12 / 479001600 - (-θ) ^ 14 / 87178291200 + (-θ) ^ 16 / 20922789888000 - (-θ) ^ 18 / 6402373705728000 + (-θ) ^ 20 / 2432902008176640000 = 1 - θ ^ 2 / 2 + θ ^ 4 / 24 - θ ^ 6 / 720 + θ ^ 8 / 40320 - θ ^ 10 / 3628800 + θ ^ 12 / 479001600 - θ ^ 14 / 87178291200 + θ ^ 16 / 20922789888000 - θ ^ 18 / 6402373705728000 + θ ^ 20 / 2432902008176640000 := by ring
      rw [Real.cos_neg, hev] at hneg
      linarith
  intro u hu
  refine nonneg_of_deriv_nonneg
    (f := fun t => (1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720 + t ^ 8 / 40320 - t ^ 10 / 3628800 + t ^ 12 / 479001600 - t ^ 14 / 87178291200 + t ^ 16 / 20922789888000 - t ^ 18 / 6402373705728000 + t ^ 20 / 2432902008176640000) - Real.cos t)
    (f' := fun t => -(t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040 + t ^ 9 / 362880 - t ^ 11 / 39916800 + t ^ 13 / 6227020800 - t ^ 15 / 1307674368000 + t ^ 17 / 355687428096000 - t ^ 19 / 121645100408832000) + Real.sin t)
    (by norm_num)
    (fun t => by
      refine ((((((((((((hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_pow 2 t).div_const 2)).add ((hasDerivAt_pow 4 t).div_const 24)).sub ((hasDerivAt_pow 6 t).div_const 720)).add ((hasDerivAt_pow 8 t).div_const 40320)).sub ((hasDerivAt_pow 10 t).div_const 3628800)).add ((hasDerivAt_pow 12 t).div_const 479001600)).sub ((hasDerivAt_pow 14 t).div_const 87178291200)).add ((hasDerivAt_pow 16 t).div_const 20922789888000)).sub ((hasDerivAt_pow 18 t).div_const 6402373705728000)).add ((hasDerivAt_pow 20 t).div_const 2432902008176640000)).sub (Real.hasDerivAt_cos t)).congr_deriv ?_
      norm_num
      ring)
    (fun t ht => by linarith [taylor_degree_nineteen_le_sin_of_nonneg ht])
    hu

/-- Step 21 (`f_21`): degree-21 alternating Taylor upper bound for `Real.sin θ` on `0 ≤ θ`. -/
theorem sin_le_taylor_degree_twenty_one_of_nonneg {θ : ℝ} (hθ : 0 ≤ θ) :
    Real.sin θ ≤ θ - θ ^ 3 / 6 + θ ^ 5 / 120 - θ ^ 7 / 5040 + θ ^ 9 / 362880 - θ ^ 11 / 39916800 + θ ^ 13 / 6227020800 - θ ^ 15 / 1307674368000 + θ ^ 17 / 355687428096000 - θ ^ 19 / 121645100408832000 + θ ^ 21 / 51090942171709440000 := by
  have h := nonneg_of_deriv_nonneg
    (f := fun t => (t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040 + t ^ 9 / 362880 - t ^ 11 / 39916800 + t ^ 13 / 6227020800 - t ^ 15 / 1307674368000 + t ^ 17 / 355687428096000 - t ^ 19 / 121645100408832000 + t ^ 21 / 51090942171709440000) - Real.sin t)
    (f' := fun t => (1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720 + t ^ 8 / 40320 - t ^ 10 / 3628800 + t ^ 12 / 479001600 - t ^ 14 / 87178291200 + t ^ 16 / 20922789888000 - t ^ 18 / 6402373705728000 + t ^ 20 / 2432902008176640000) - Real.cos t)
    (by norm_num [Real.sin_zero])
    (fun t => by
      refine ((((((((((((hasDerivAt_id t).sub ((hasDerivAt_pow 3 t).div_const 6)).add ((hasDerivAt_pow 5 t).div_const 120)).sub ((hasDerivAt_pow 7 t).div_const 5040)).add ((hasDerivAt_pow 9 t).div_const 362880)).sub ((hasDerivAt_pow 11 t).div_const 39916800)).add ((hasDerivAt_pow 13 t).div_const 6227020800)).sub ((hasDerivAt_pow 15 t).div_const 1307674368000)).add ((hasDerivAt_pow 17 t).div_const 355687428096000)).sub ((hasDerivAt_pow 19 t).div_const 121645100408832000)).add ((hasDerivAt_pow 21 t).div_const 51090942171709440000)).sub (Real.hasDerivAt_sin t)).congr_deriv ?_
      norm_num
      ring)
    (fun t _ => by linarith [taylor_degree_twenty_le_one_sub_cos t])
    hθ
  linarith

/-- Step 22 (`f_22`): degree-22 alternating Taylor upper bound for `1 - Real.cos θ` (`∀ θ : ℝ`). -/
theorem one_sub_cos_le_taylor_degree_twenty_two (θ : ℝ) :
    1 - Real.cos θ ≤ θ ^ 2 / 2 - θ ^ 4 / 24 + θ ^ 6 / 720 - θ ^ 8 / 40320 + θ ^ 10 / 3628800 - θ ^ 12 / 479001600 + θ ^ 14 / 87178291200 - θ ^ 16 / 20922789888000 + θ ^ 18 / 6402373705728000 - θ ^ 20 / 2432902008176640000 + θ ^ 22 / 1124000727777607680000 := by
  suffices h : ∀ u : ℝ, 0 ≤ u → 0 ≤ Real.cos u - (1 - u ^ 2 / 2 + u ^ 4 / 24 - u ^ 6 / 720 + u ^ 8 / 40320 - u ^ 10 / 3628800 + u ^ 12 / 479001600 - u ^ 14 / 87178291200 + u ^ 16 / 20922789888000 - u ^ 18 / 6402373705728000 + u ^ 20 / 2432902008176640000 - u ^ 22 / 1124000727777607680000) by
    rcases le_total 0 θ with hθ | hθ
    · linarith [h θ hθ]
    · have hneg := h (-θ) (by linarith)
      have hev : 1 - (-θ) ^ 2 / 2 + (-θ) ^ 4 / 24 - (-θ) ^ 6 / 720 + (-θ) ^ 8 / 40320 - (-θ) ^ 10 / 3628800 + (-θ) ^ 12 / 479001600 - (-θ) ^ 14 / 87178291200 + (-θ) ^ 16 / 20922789888000 - (-θ) ^ 18 / 6402373705728000 + (-θ) ^ 20 / 2432902008176640000 - (-θ) ^ 22 / 1124000727777607680000 = 1 - θ ^ 2 / 2 + θ ^ 4 / 24 - θ ^ 6 / 720 + θ ^ 8 / 40320 - θ ^ 10 / 3628800 + θ ^ 12 / 479001600 - θ ^ 14 / 87178291200 + θ ^ 16 / 20922789888000 - θ ^ 18 / 6402373705728000 + θ ^ 20 / 2432902008176640000 - θ ^ 22 / 1124000727777607680000 := by ring
      rw [Real.cos_neg, hev] at hneg
      linarith
  intro u hu
  refine nonneg_of_deriv_nonneg
    (f := fun t => Real.cos t - (1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720 + t ^ 8 / 40320 - t ^ 10 / 3628800 + t ^ 12 / 479001600 - t ^ 14 / 87178291200 + t ^ 16 / 20922789888000 - t ^ 18 / 6402373705728000 + t ^ 20 / 2432902008176640000 - t ^ 22 / 1124000727777607680000))
    (f' := fun t => -Real.sin t + (t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040 + t ^ 9 / 362880 - t ^ 11 / 39916800 + t ^ 13 / 6227020800 - t ^ 15 / 1307674368000 + t ^ 17 / 355687428096000 - t ^ 19 / 121645100408832000 + t ^ 21 / 51090942171709440000))
    (by norm_num)
    (fun t => by
      refine ((Real.hasDerivAt_cos t).sub ((((((((((((hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_pow 2 t).div_const 2)).add ((hasDerivAt_pow 4 t).div_const 24)).sub ((hasDerivAt_pow 6 t).div_const 720)).add ((hasDerivAt_pow 8 t).div_const 40320)).sub ((hasDerivAt_pow 10 t).div_const 3628800)).add ((hasDerivAt_pow 12 t).div_const 479001600)).sub ((hasDerivAt_pow 14 t).div_const 87178291200)).add ((hasDerivAt_pow 16 t).div_const 20922789888000)).sub ((hasDerivAt_pow 18 t).div_const 6402373705728000)).add ((hasDerivAt_pow 20 t).div_const 2432902008176640000)).sub ((hasDerivAt_pow 22 t).div_const 1124000727777607680000))).congr_deriv ?_
      norm_num
      ring)
    (fun t ht => by linarith [sin_le_taylor_degree_twenty_one_of_nonneg ht])
    hu

/-- Step 23 (`f_23`): degree-23 alternating Taylor lower bound for `Real.sin θ` on `0 ≤ θ`. -/
theorem taylor_degree_twenty_three_le_sin_of_nonneg {θ : ℝ} (hθ : 0 ≤ θ) :
    θ - θ ^ 3 / 6 + θ ^ 5 / 120 - θ ^ 7 / 5040 + θ ^ 9 / 362880 - θ ^ 11 / 39916800 + θ ^ 13 / 6227020800 - θ ^ 15 / 1307674368000 + θ ^ 17 / 355687428096000 - θ ^ 19 / 121645100408832000 + θ ^ 21 / 51090942171709440000 - θ ^ 23 / 25852016738884976640000 ≤ Real.sin θ := by
  have h := nonneg_of_deriv_nonneg
    (f := fun t => Real.sin t - (t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040 + t ^ 9 / 362880 - t ^ 11 / 39916800 + t ^ 13 / 6227020800 - t ^ 15 / 1307674368000 + t ^ 17 / 355687428096000 - t ^ 19 / 121645100408832000 + t ^ 21 / 51090942171709440000 - t ^ 23 / 25852016738884976640000))
    (f' := fun t => Real.cos t - (1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720 + t ^ 8 / 40320 - t ^ 10 / 3628800 + t ^ 12 / 479001600 - t ^ 14 / 87178291200 + t ^ 16 / 20922789888000 - t ^ 18 / 6402373705728000 + t ^ 20 / 2432902008176640000 - t ^ 22 / 1124000727777607680000))
    (by norm_num [Real.sin_zero])
    (fun t => by
      refine ((Real.hasDerivAt_sin t).sub ((((((((((((hasDerivAt_id t).sub ((hasDerivAt_pow 3 t).div_const 6)).add ((hasDerivAt_pow 5 t).div_const 120)).sub ((hasDerivAt_pow 7 t).div_const 5040)).add ((hasDerivAt_pow 9 t).div_const 362880)).sub ((hasDerivAt_pow 11 t).div_const 39916800)).add ((hasDerivAt_pow 13 t).div_const 6227020800)).sub ((hasDerivAt_pow 15 t).div_const 1307674368000)).add ((hasDerivAt_pow 17 t).div_const 355687428096000)).sub ((hasDerivAt_pow 19 t).div_const 121645100408832000)).add ((hasDerivAt_pow 21 t).div_const 51090942171709440000)).sub ((hasDerivAt_pow 23 t).div_const 25852016738884976640000))).congr_deriv ?_
      norm_num
      ring)
    (fun t _ => by linarith [one_sub_cos_le_taylor_degree_twenty_two t])
    hθ
  linarith

/-- Step 24 (`f_24`): degree-24 alternating Taylor lower bound for `1 - Real.cos θ` (`∀ θ : ℝ`). -/
theorem taylor_degree_twenty_four_le_one_sub_cos (θ : ℝ) :
    θ ^ 2 / 2 - θ ^ 4 / 24 + θ ^ 6 / 720 - θ ^ 8 / 40320 + θ ^ 10 / 3628800 - θ ^ 12 / 479001600 + θ ^ 14 / 87178291200 - θ ^ 16 / 20922789888000 + θ ^ 18 / 6402373705728000 - θ ^ 20 / 2432902008176640000 + θ ^ 22 / 1124000727777607680000 - θ ^ 24 / 620448401733239439360000 ≤ 1 - Real.cos θ := by
  suffices h : ∀ u : ℝ, 0 ≤ u → 0 ≤ (1 - u ^ 2 / 2 + u ^ 4 / 24 - u ^ 6 / 720 + u ^ 8 / 40320 - u ^ 10 / 3628800 + u ^ 12 / 479001600 - u ^ 14 / 87178291200 + u ^ 16 / 20922789888000 - u ^ 18 / 6402373705728000 + u ^ 20 / 2432902008176640000 - u ^ 22 / 1124000727777607680000 + u ^ 24 / 620448401733239439360000) - Real.cos u by
    rcases le_total 0 θ with hθ | hθ
    · linarith [h θ hθ]
    · have hneg := h (-θ) (by linarith)
      have hev : 1 - (-θ) ^ 2 / 2 + (-θ) ^ 4 / 24 - (-θ) ^ 6 / 720 + (-θ) ^ 8 / 40320 - (-θ) ^ 10 / 3628800 + (-θ) ^ 12 / 479001600 - (-θ) ^ 14 / 87178291200 + (-θ) ^ 16 / 20922789888000 - (-θ) ^ 18 / 6402373705728000 + (-θ) ^ 20 / 2432902008176640000 - (-θ) ^ 22 / 1124000727777607680000 + (-θ) ^ 24 / 620448401733239439360000 = 1 - θ ^ 2 / 2 + θ ^ 4 / 24 - θ ^ 6 / 720 + θ ^ 8 / 40320 - θ ^ 10 / 3628800 + θ ^ 12 / 479001600 - θ ^ 14 / 87178291200 + θ ^ 16 / 20922789888000 - θ ^ 18 / 6402373705728000 + θ ^ 20 / 2432902008176640000 - θ ^ 22 / 1124000727777607680000 + θ ^ 24 / 620448401733239439360000 := by ring
      rw [Real.cos_neg, hev] at hneg
      linarith
  intro u hu
  refine nonneg_of_deriv_nonneg
    (f := fun t => (1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720 + t ^ 8 / 40320 - t ^ 10 / 3628800 + t ^ 12 / 479001600 - t ^ 14 / 87178291200 + t ^ 16 / 20922789888000 - t ^ 18 / 6402373705728000 + t ^ 20 / 2432902008176640000 - t ^ 22 / 1124000727777607680000 + t ^ 24 / 620448401733239439360000) - Real.cos t)
    (f' := fun t => -(t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040 + t ^ 9 / 362880 - t ^ 11 / 39916800 + t ^ 13 / 6227020800 - t ^ 15 / 1307674368000 + t ^ 17 / 355687428096000 - t ^ 19 / 121645100408832000 + t ^ 21 / 51090942171709440000 - t ^ 23 / 25852016738884976640000) + Real.sin t)
    (by norm_num)
    (fun t => by
      refine ((((((((((((((hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_pow 2 t).div_const 2)).add ((hasDerivAt_pow 4 t).div_const 24)).sub ((hasDerivAt_pow 6 t).div_const 720)).add ((hasDerivAt_pow 8 t).div_const 40320)).sub ((hasDerivAt_pow 10 t).div_const 3628800)).add ((hasDerivAt_pow 12 t).div_const 479001600)).sub ((hasDerivAt_pow 14 t).div_const 87178291200)).add ((hasDerivAt_pow 16 t).div_const 20922789888000)).sub ((hasDerivAt_pow 18 t).div_const 6402373705728000)).add ((hasDerivAt_pow 20 t).div_const 2432902008176640000)).sub ((hasDerivAt_pow 22 t).div_const 1124000727777607680000)).add ((hasDerivAt_pow 24 t).div_const 620448401733239439360000)).sub (Real.hasDerivAt_cos t)).congr_deriv ?_
      norm_num
      ring)
    (fun t ht => by linarith [taylor_degree_twenty_three_le_sin_of_nonneg ht])
    hu

/-- Step 25 (`f_25`): degree-25 alternating Taylor upper bound for `Real.sin θ` on `0 ≤ θ`. -/
theorem sin_le_taylor_degree_twenty_five_of_nonneg {θ : ℝ} (hθ : 0 ≤ θ) :
    Real.sin θ ≤ θ - θ ^ 3 / 6 + θ ^ 5 / 120 - θ ^ 7 / 5040 + θ ^ 9 / 362880 - θ ^ 11 / 39916800 + θ ^ 13 / 6227020800 - θ ^ 15 / 1307674368000 + θ ^ 17 / 355687428096000 - θ ^ 19 / 121645100408832000 + θ ^ 21 / 51090942171709440000 - θ ^ 23 / 25852016738884976640000 + θ ^ 25 / 15511210043330985984000000 := by
  have h := nonneg_of_deriv_nonneg
    (f := fun t => (t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040 + t ^ 9 / 362880 - t ^ 11 / 39916800 + t ^ 13 / 6227020800 - t ^ 15 / 1307674368000 + t ^ 17 / 355687428096000 - t ^ 19 / 121645100408832000 + t ^ 21 / 51090942171709440000 - t ^ 23 / 25852016738884976640000 + t ^ 25 / 15511210043330985984000000) - Real.sin t)
    (f' := fun t => (1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720 + t ^ 8 / 40320 - t ^ 10 / 3628800 + t ^ 12 / 479001600 - t ^ 14 / 87178291200 + t ^ 16 / 20922789888000 - t ^ 18 / 6402373705728000 + t ^ 20 / 2432902008176640000 - t ^ 22 / 1124000727777607680000 + t ^ 24 / 620448401733239439360000) - Real.cos t)
    (by norm_num [Real.sin_zero])
    (fun t => by
      refine ((((((((((((((hasDerivAt_id t).sub ((hasDerivAt_pow 3 t).div_const 6)).add ((hasDerivAt_pow 5 t).div_const 120)).sub ((hasDerivAt_pow 7 t).div_const 5040)).add ((hasDerivAt_pow 9 t).div_const 362880)).sub ((hasDerivAt_pow 11 t).div_const 39916800)).add ((hasDerivAt_pow 13 t).div_const 6227020800)).sub ((hasDerivAt_pow 15 t).div_const 1307674368000)).add ((hasDerivAt_pow 17 t).div_const 355687428096000)).sub ((hasDerivAt_pow 19 t).div_const 121645100408832000)).add ((hasDerivAt_pow 21 t).div_const 51090942171709440000)).sub ((hasDerivAt_pow 23 t).div_const 25852016738884976640000)).add ((hasDerivAt_pow 25 t).div_const 15511210043330985984000000)).sub (Real.hasDerivAt_sin t)).congr_deriv ?_
      norm_num
      ring)
    (fun t _ => by linarith [taylor_degree_twenty_four_le_one_sub_cos t])
    hθ
  linarith

/-- Step 26 (`f_26`): degree-26 alternating Taylor upper bound for `1 - Real.cos θ` (`∀ θ : ℝ`). -/
theorem one_sub_cos_le_taylor_degree_twenty_six (θ : ℝ) :
    1 - Real.cos θ ≤ θ ^ 2 / 2 - θ ^ 4 / 24 + θ ^ 6 / 720 - θ ^ 8 / 40320 + θ ^ 10 / 3628800 - θ ^ 12 / 479001600 + θ ^ 14 / 87178291200 - θ ^ 16 / 20922789888000 + θ ^ 18 / 6402373705728000 - θ ^ 20 / 2432902008176640000 + θ ^ 22 / 1124000727777607680000 - θ ^ 24 / 620448401733239439360000 + θ ^ 26 / 403291461126605635584000000 := by
  suffices h : ∀ u : ℝ, 0 ≤ u → 0 ≤ Real.cos u - (1 - u ^ 2 / 2 + u ^ 4 / 24 - u ^ 6 / 720 + u ^ 8 / 40320 - u ^ 10 / 3628800 + u ^ 12 / 479001600 - u ^ 14 / 87178291200 + u ^ 16 / 20922789888000 - u ^ 18 / 6402373705728000 + u ^ 20 / 2432902008176640000 - u ^ 22 / 1124000727777607680000 + u ^ 24 / 620448401733239439360000 - u ^ 26 / 403291461126605635584000000) by
    rcases le_total 0 θ with hθ | hθ
    · linarith [h θ hθ]
    · have hneg := h (-θ) (by linarith)
      have hev : 1 - (-θ) ^ 2 / 2 + (-θ) ^ 4 / 24 - (-θ) ^ 6 / 720 + (-θ) ^ 8 / 40320 - (-θ) ^ 10 / 3628800 + (-θ) ^ 12 / 479001600 - (-θ) ^ 14 / 87178291200 + (-θ) ^ 16 / 20922789888000 - (-θ) ^ 18 / 6402373705728000 + (-θ) ^ 20 / 2432902008176640000 - (-θ) ^ 22 / 1124000727777607680000 + (-θ) ^ 24 / 620448401733239439360000 - (-θ) ^ 26 / 403291461126605635584000000 = 1 - θ ^ 2 / 2 + θ ^ 4 / 24 - θ ^ 6 / 720 + θ ^ 8 / 40320 - θ ^ 10 / 3628800 + θ ^ 12 / 479001600 - θ ^ 14 / 87178291200 + θ ^ 16 / 20922789888000 - θ ^ 18 / 6402373705728000 + θ ^ 20 / 2432902008176640000 - θ ^ 22 / 1124000727777607680000 + θ ^ 24 / 620448401733239439360000 - θ ^ 26 / 403291461126605635584000000 := by ring
      rw [Real.cos_neg, hev] at hneg
      linarith
  intro u hu
  refine nonneg_of_deriv_nonneg
    (f := fun t => Real.cos t - (1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720 + t ^ 8 / 40320 - t ^ 10 / 3628800 + t ^ 12 / 479001600 - t ^ 14 / 87178291200 + t ^ 16 / 20922789888000 - t ^ 18 / 6402373705728000 + t ^ 20 / 2432902008176640000 - t ^ 22 / 1124000727777607680000 + t ^ 24 / 620448401733239439360000 - t ^ 26 / 403291461126605635584000000))
    (f' := fun t => -Real.sin t + (t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040 + t ^ 9 / 362880 - t ^ 11 / 39916800 + t ^ 13 / 6227020800 - t ^ 15 / 1307674368000 + t ^ 17 / 355687428096000 - t ^ 19 / 121645100408832000 + t ^ 21 / 51090942171709440000 - t ^ 23 / 25852016738884976640000 + t ^ 25 / 15511210043330985984000000))
    (by norm_num)
    (fun t => by
      refine ((Real.hasDerivAt_cos t).sub ((((((((((((((hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_pow 2 t).div_const 2)).add ((hasDerivAt_pow 4 t).div_const 24)).sub ((hasDerivAt_pow 6 t).div_const 720)).add ((hasDerivAt_pow 8 t).div_const 40320)).sub ((hasDerivAt_pow 10 t).div_const 3628800)).add ((hasDerivAt_pow 12 t).div_const 479001600)).sub ((hasDerivAt_pow 14 t).div_const 87178291200)).add ((hasDerivAt_pow 16 t).div_const 20922789888000)).sub ((hasDerivAt_pow 18 t).div_const 6402373705728000)).add ((hasDerivAt_pow 20 t).div_const 2432902008176640000)).sub ((hasDerivAt_pow 22 t).div_const 1124000727777607680000)).add ((hasDerivAt_pow 24 t).div_const 620448401733239439360000)).sub ((hasDerivAt_pow 26 t).div_const 403291461126605635584000000))).congr_deriv ?_
      norm_num
      ring)
    (fun t ht => by linarith [sin_le_taylor_degree_twenty_five_of_nonneg ht])
    hu

/-- Step 27 (`f_27`): degree-27 alternating Taylor lower bound for `Real.sin θ` on `0 ≤ θ`. -/
theorem taylor_degree_twenty_seven_le_sin_of_nonneg {θ : ℝ} (hθ : 0 ≤ θ) :
    θ - θ ^ 3 / 6 + θ ^ 5 / 120 - θ ^ 7 / 5040 + θ ^ 9 / 362880 - θ ^ 11 / 39916800 + θ ^ 13 / 6227020800 - θ ^ 15 / 1307674368000 + θ ^ 17 / 355687428096000 - θ ^ 19 / 121645100408832000 + θ ^ 21 / 51090942171709440000 - θ ^ 23 / 25852016738884976640000 + θ ^ 25 / 15511210043330985984000000 - θ ^ 27 / 10888869450418352160768000000 ≤ Real.sin θ := by
  have h := nonneg_of_deriv_nonneg
    (f := fun t => Real.sin t - (t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040 + t ^ 9 / 362880 - t ^ 11 / 39916800 + t ^ 13 / 6227020800 - t ^ 15 / 1307674368000 + t ^ 17 / 355687428096000 - t ^ 19 / 121645100408832000 + t ^ 21 / 51090942171709440000 - t ^ 23 / 25852016738884976640000 + t ^ 25 / 15511210043330985984000000 - t ^ 27 / 10888869450418352160768000000))
    (f' := fun t => Real.cos t - (1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720 + t ^ 8 / 40320 - t ^ 10 / 3628800 + t ^ 12 / 479001600 - t ^ 14 / 87178291200 + t ^ 16 / 20922789888000 - t ^ 18 / 6402373705728000 + t ^ 20 / 2432902008176640000 - t ^ 22 / 1124000727777607680000 + t ^ 24 / 620448401733239439360000 - t ^ 26 / 403291461126605635584000000))
    (by norm_num [Real.sin_zero])
    (fun t => by
      refine ((Real.hasDerivAt_sin t).sub ((((((((((((((hasDerivAt_id t).sub ((hasDerivAt_pow 3 t).div_const 6)).add ((hasDerivAt_pow 5 t).div_const 120)).sub ((hasDerivAt_pow 7 t).div_const 5040)).add ((hasDerivAt_pow 9 t).div_const 362880)).sub ((hasDerivAt_pow 11 t).div_const 39916800)).add ((hasDerivAt_pow 13 t).div_const 6227020800)).sub ((hasDerivAt_pow 15 t).div_const 1307674368000)).add ((hasDerivAt_pow 17 t).div_const 355687428096000)).sub ((hasDerivAt_pow 19 t).div_const 121645100408832000)).add ((hasDerivAt_pow 21 t).div_const 51090942171709440000)).sub ((hasDerivAt_pow 23 t).div_const 25852016738884976640000)).add ((hasDerivAt_pow 25 t).div_const 15511210043330985984000000)).sub ((hasDerivAt_pow 27 t).div_const 10888869450418352160768000000))).congr_deriv ?_
      norm_num
      ring)
    (fun t _ => by linarith [one_sub_cos_le_taylor_degree_twenty_six t])
    hθ
  linarith

/-- Step 28 (`f_28`): degree-28 alternating Taylor lower bound for `1 - Real.cos θ` (`∀ θ : ℝ`). -/
theorem taylor_degree_twenty_eight_le_one_sub_cos (θ : ℝ) :
    θ ^ 2 / 2 - θ ^ 4 / 24 + θ ^ 6 / 720 - θ ^ 8 / 40320 + θ ^ 10 / 3628800 - θ ^ 12 / 479001600 + θ ^ 14 / 87178291200 - θ ^ 16 / 20922789888000 + θ ^ 18 / 6402373705728000 - θ ^ 20 / 2432902008176640000 + θ ^ 22 / 1124000727777607680000 - θ ^ 24 / 620448401733239439360000 + θ ^ 26 / 403291461126605635584000000 - θ ^ 28 / 304888344611713860501504000000 ≤ 1 - Real.cos θ := by
  suffices h : ∀ u : ℝ, 0 ≤ u → 0 ≤ (1 - u ^ 2 / 2 + u ^ 4 / 24 - u ^ 6 / 720 + u ^ 8 / 40320 - u ^ 10 / 3628800 + u ^ 12 / 479001600 - u ^ 14 / 87178291200 + u ^ 16 / 20922789888000 - u ^ 18 / 6402373705728000 + u ^ 20 / 2432902008176640000 - u ^ 22 / 1124000727777607680000 + u ^ 24 / 620448401733239439360000 - u ^ 26 / 403291461126605635584000000 + u ^ 28 / 304888344611713860501504000000) - Real.cos u by
    rcases le_total 0 θ with hθ | hθ
    · linarith [h θ hθ]
    · have hneg := h (-θ) (by linarith)
      have hev : 1 - (-θ) ^ 2 / 2 + (-θ) ^ 4 / 24 - (-θ) ^ 6 / 720 + (-θ) ^ 8 / 40320 - (-θ) ^ 10 / 3628800 + (-θ) ^ 12 / 479001600 - (-θ) ^ 14 / 87178291200 + (-θ) ^ 16 / 20922789888000 - (-θ) ^ 18 / 6402373705728000 + (-θ) ^ 20 / 2432902008176640000 - (-θ) ^ 22 / 1124000727777607680000 + (-θ) ^ 24 / 620448401733239439360000 - (-θ) ^ 26 / 403291461126605635584000000 + (-θ) ^ 28 / 304888344611713860501504000000 = 1 - θ ^ 2 / 2 + θ ^ 4 / 24 - θ ^ 6 / 720 + θ ^ 8 / 40320 - θ ^ 10 / 3628800 + θ ^ 12 / 479001600 - θ ^ 14 / 87178291200 + θ ^ 16 / 20922789888000 - θ ^ 18 / 6402373705728000 + θ ^ 20 / 2432902008176640000 - θ ^ 22 / 1124000727777607680000 + θ ^ 24 / 620448401733239439360000 - θ ^ 26 / 403291461126605635584000000 + θ ^ 28 / 304888344611713860501504000000 := by ring
      rw [Real.cos_neg, hev] at hneg
      linarith
  intro u hu
  refine nonneg_of_deriv_nonneg
    (f := fun t => (1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720 + t ^ 8 / 40320 - t ^ 10 / 3628800 + t ^ 12 / 479001600 - t ^ 14 / 87178291200 + t ^ 16 / 20922789888000 - t ^ 18 / 6402373705728000 + t ^ 20 / 2432902008176640000 - t ^ 22 / 1124000727777607680000 + t ^ 24 / 620448401733239439360000 - t ^ 26 / 403291461126605635584000000 + t ^ 28 / 304888344611713860501504000000) - Real.cos t)
    (f' := fun t => -(t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040 + t ^ 9 / 362880 - t ^ 11 / 39916800 + t ^ 13 / 6227020800 - t ^ 15 / 1307674368000 + t ^ 17 / 355687428096000 - t ^ 19 / 121645100408832000 + t ^ 21 / 51090942171709440000 - t ^ 23 / 25852016738884976640000 + t ^ 25 / 15511210043330985984000000 - t ^ 27 / 10888869450418352160768000000) + Real.sin t)
    (by norm_num)
    (fun t => by
      refine ((((((((((((((((hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_pow 2 t).div_const 2)).add ((hasDerivAt_pow 4 t).div_const 24)).sub ((hasDerivAt_pow 6 t).div_const 720)).add ((hasDerivAt_pow 8 t).div_const 40320)).sub ((hasDerivAt_pow 10 t).div_const 3628800)).add ((hasDerivAt_pow 12 t).div_const 479001600)).sub ((hasDerivAt_pow 14 t).div_const 87178291200)).add ((hasDerivAt_pow 16 t).div_const 20922789888000)).sub ((hasDerivAt_pow 18 t).div_const 6402373705728000)).add ((hasDerivAt_pow 20 t).div_const 2432902008176640000)).sub ((hasDerivAt_pow 22 t).div_const 1124000727777607680000)).add ((hasDerivAt_pow 24 t).div_const 620448401733239439360000)).sub ((hasDerivAt_pow 26 t).div_const 403291461126605635584000000)).add ((hasDerivAt_pow 28 t).div_const 304888344611713860501504000000)).sub (Real.hasDerivAt_cos t)).congr_deriv ?_
      norm_num
      ring)
    (fun t ht => by linarith [taylor_degree_twenty_seven_le_sin_of_nonneg ht])
    hu

/-- **Global Even-Degree-28 Lower Bound on `θ * Real.sin θ` (`∀ θ : ℝ`)**. -/
theorem mul_sin_ge_taylor_degree_twenty_eight (θ : ℝ) :
    θ ^ 2 - θ ^ 4 / 6 + θ ^ 6 / 120 - θ ^ 8 / 5040 + θ ^ 10 / 362880 - θ ^ 12 / 39916800 + θ ^ 14 / 6227020800 - θ ^ 16 / 1307674368000 + θ ^ 18 / 355687428096000 - θ ^ 20 / 121645100408832000 + θ ^ 22 / 51090942171709440000 - θ ^ 24 / 25852016738884976640000 + θ ^ 26 / 15511210043330985984000000 - θ ^ 28 / 10888869450418352160768000000 ≤ θ * Real.sin θ := by
  rcases le_total 0 θ with hθ | hθ
  · have h := mul_le_mul_of_nonneg_left (taylor_degree_twenty_seven_le_sin_of_nonneg hθ) hθ
    linarith [show θ * (θ - θ ^ 3 / 6 + θ ^ 5 / 120 - θ ^ 7 / 5040 + θ ^ 9 / 362880 - θ ^ 11 / 39916800 + θ ^ 13 / 6227020800 - θ ^ 15 / 1307674368000 + θ ^ 17 / 355687428096000 - θ ^ 19 / 121645100408832000 + θ ^ 21 / 51090942171709440000 - θ ^ 23 / 25852016738884976640000 + θ ^ 25 / 15511210043330985984000000 - θ ^ 27 / 10888869450418352160768000000) = θ ^ 2 - θ ^ 4 / 6 + θ ^ 6 / 120 - θ ^ 8 / 5040 + θ ^ 10 / 362880 - θ ^ 12 / 39916800 + θ ^ 14 / 6227020800 - θ ^ 16 / 1307674368000 + θ ^ 18 / 355687428096000 - θ ^ 20 / 121645100408832000 + θ ^ 22 / 51090942171709440000 - θ ^ 24 / 25852016738884976640000 + θ ^ 26 / 15511210043330985984000000 - θ ^ 28 / 10888869450418352160768000000 by ring]
  · have hθ_neg : 0 ≤ -θ := by linarith
    have h := mul_le_mul_of_nonneg_left (taylor_degree_twenty_seven_le_sin_of_nonneg hθ_neg) hθ_neg
    rw [Real.sin_neg] at h
    linarith [show (-θ) * ((-θ) - (-θ) ^ 3 / 6 + (-θ) ^ 5 / 120 - (-θ) ^ 7 / 5040 + (-θ) ^ 9 / 362880 - (-θ) ^ 11 / 39916800 + (-θ) ^ 13 / 6227020800 - (-θ) ^ 15 / 1307674368000 + (-θ) ^ 17 / 355687428096000 - (-θ) ^ 19 / 121645100408832000 + (-θ) ^ 21 / 51090942171709440000 - (-θ) ^ 23 / 25852016738884976640000 + (-θ) ^ 25 / 15511210043330985984000000 - (-θ) ^ 27 / 10888869450418352160768000000) = θ ^ 2 - θ ^ 4 / 6 + θ ^ 6 / 120 - θ ^ 8 / 5040 + θ ^ 10 / 362880 - θ ^ 12 / 39916800 + θ ^ 14 / 6227020800 - θ ^ 16 / 1307674368000 + θ ^ 18 / 355687428096000 - θ ^ 20 / 121645100408832000 + θ ^ 22 / 51090942171709440000 - θ ^ 24 / 25852016738884976640000 + θ ^ 26 / 15511210043330985984000000 - θ ^ 28 / 10888869450418352160768000000 by ring,
      show (-θ) * -Real.sin θ = θ * Real.sin θ by ring]

/-- **8th-Order Artanh / Padé Lower Bound for `Real.log b - Real.log a`**:
for `0 < a ≤ b` and `s = (b - a) / (b + a)`,
`2 * (s + s ^ 3 / 3 + s ^ 5 / 5 + s ^ 7 / 7) ≤ Real.log b - Real.log a`. -/
theorem artanh_degree_seven_le_log_sub_log {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    2 * (((b - a) / (b + a)) + ((b - a) / (b + a)) ^ 3 / 3 +
      ((b - a) / (b + a)) ^ 5 / 5 + ((b - a) / (b + a)) ^ 7 / 7) ≤
      Real.log b - Real.log a := by
  rcases eq_or_lt_of_le hab with rfl | hab_lt
  · norm_num
  have hb : 0 < b := ha.trans hab_lt
  let s : ℝ → ℝ := fun t => (t - a) * (t + a)⁻¹
  let s' : ℝ → ℝ := fun t => (1 - 0) * (t + a)⁻¹ + (t - a) * (-(1 + 0) / (t + a) ^ 2)
  let g : ℝ → ℝ := fun t =>
    Real.log t - Real.log a -
      2 * (s t + s t ^ 3 / 3 + s t ^ 5 / 5 + s t ^ 7 / 7)
  let g' : ℝ → ℝ := fun t =>
    t⁻¹ - 0 -
      2 * (s' t + ((3 : ℕ) * s t ^ (3 - 1) * s' t) / 3 +
        ((5 : ℕ) * s t ^ (5 - 1) * s' t) / 5 + ((7 : ℕ) * s t ^ (7 - 1) * s' t) / 7)
  have hd : ∀ t ∈ Icc a b, HasDerivAt g (g' t) t := by
    intro t ht
    have ht_pos : 0 < t := ha.trans_le ht.1
    have hta_pos : 0 < t + a := add_pos ht_pos ha
    have hs : HasDerivAt s (s' t) t :=
      ((hasDerivAt_id t).sub (hasDerivAt_const t a)).mul
        (((hasDerivAt_id t).add (hasDerivAt_const t a)).inv hta_pos.ne')
    have hH := (((hs.add ((hs.pow 3).div_const 3)).add
      ((hs.pow 5).div_const 5)).add ((hs.pow 7).div_const 7)).const_mul 2
    exact ((Real.hasDerivAt_log ht_pos.ne').sub (hasDerivAt_const t (Real.log a))).sub hH
  obtain ⟨c, hc, hc_slope⟩ := exists_hasDerivAt_eq_slope g g' hab_lt
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => hd t ⟨ht.1.le, ht.2.le⟩)
  have hc_pos : 0 < c := ha.trans hc.1
  have hca_pos : 0 < c + a := add_pos hc_pos ha
  have hba_pos : 0 < b - a := sub_pos.mpr hab_lt
  have hg'_nonneg : 0 ≤ g' c := by
    have hg'_eq : g' c = (c - a) ^ 8 / (c * (c + a) ^ 8) := by
      dsimp only [g', s, s']
      norm_num only
      simp only [← div_eq_mul_inv, div_pow]
      have hc0 : c ≠ 0 := hc_pos.ne'
      have hca0 : c + a ≠ 0 := hca_pos.ne'
      field_simp [hc0, hca0]
      ring
    rw [hg'_eq]
    positivity
  have hdiff_eq : g b - g a = g' c * (b - a) := ((eq_div_iff hba_pos.ne').mp hc_slope).symm
  have hdiff_nonneg : 0 ≤ g b - g a := by
    rw [hdiff_eq]
    exact mul_nonneg hg'_nonneg hba_pos.le
  have halg : g b - g a =
      (Real.log b - Real.log a) -
        2 * (((b - a) / (b + a)) + ((b - a) / (b + a)) ^ 3 / 3 +
          ((b - a) / (b + a)) ^ 5 / 5 + ((b - a) / (b + a)) ^ 7 / 7) := by
    dsimp only [g, s]
    simp only [← div_eq_mul_inv, div_pow]
    have hab0 : b + a ≠ 0 := (add_pos hb ha).ne'
    have haa0 : a + a ≠ 0 := (add_pos ha ha).ne'
    field_simp [hab0, haa0]
    ring
  linarith

/-- **8th-Order Artanh / Padé Upper Bound for `Real.log b - Real.log a`**:
for `0 < a ≤ b` and `s = (b - a) / (b + a)`,
`Real.log b - Real.log a ≤ 2 * (s + s ^ 3 / 3 + s ^ 5 / 5 + s ^ 7 / 7) + ((b + a) ^ 2 / (18 * a ^ 2)) * s ^ 9`. -/
theorem log_sub_log_le_artanh_degree_nine {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Real.log b - Real.log a ≤
      2 * (((b - a) / (b + a)) + ((b - a) / (b + a)) ^ 3 / 3 +
        ((b - a) / (b + a)) ^ 5 / 5 + ((b - a) / (b + a)) ^ 7 / 7) +
      ((b + a) ^ 2 / (18 * a ^ 2)) * ((b - a) / (b + a)) ^ 9 := by
  rcases eq_or_lt_of_le hab with rfl | hab_lt
  · norm_num
  have hb : 0 < b := ha.trans hab_lt
  let s : ℝ → ℝ := fun t => (t - a) * (t + a)⁻¹
  let s' : ℝ → ℝ := fun t => (1 - 0) * (t + a)⁻¹ + (t - a) * (-(1 + 0) / (t + a) ^ 2)
  let g : ℝ → ℝ := fun t =>
    2 * (s t + s t ^ 3 / 3 + s t ^ 5 / 5 + s t ^ 7 / 7) +
      ((b + a) ^ 2 / (18 * a ^ 2)) * s t ^ 9 -
      (Real.log t - Real.log a)
  let g' : ℝ → ℝ := fun t =>
    2 * (s' t + ((3 : ℕ) * s t ^ (3 - 1) * s' t) / 3 +
      ((5 : ℕ) * s t ^ (5 - 1) * s' t) / 5 + ((7 : ℕ) * s t ^ (7 - 1) * s' t) / 7) +
      ((b + a) ^ 2 / (18 * a ^ 2)) * ((9 : ℕ) * s t ^ (9 - 1) * s' t) -
      (t⁻¹ - 0)
  have hd : ∀ t ∈ Icc a b, HasDerivAt g (g' t) t := by
    intro t ht
    have ht_pos : 0 < t := ha.trans_le ht.1
    have hta_pos : 0 < t + a := add_pos ht_pos ha
    have hs : HasDerivAt s (s' t) t :=
      ((hasDerivAt_id t).sub (hasDerivAt_const t a)).mul
        (((hasDerivAt_id t).add (hasDerivAt_const t a)).inv hta_pos.ne')
    have hH := (((hs.add ((hs.pow 3).div_const 3)).add
      ((hs.pow 5).div_const 5)).add ((hs.pow 7).div_const 7)).const_mul 2
    have hR := (hs.pow 9).const_mul ((b + a) ^ 2 / (18 * a ^ 2))
    exact (hH.add hR).sub ((Real.hasDerivAt_log ht_pos.ne').sub (hasDerivAt_const t (Real.log a)))
  obtain ⟨c, hc, hc_slope⟩ := exists_hasDerivAt_eq_slope g g' hab_lt
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => hd t ⟨ht.1.le, ht.2.le⟩)
  have hc_pos : 0 < c := ha.trans hc.1
  have hca_pos : 0 < c + a := add_pos hc_pos ha
  have hba_pos : 0 < b - a := sub_pos.mpr hab_lt
  have hca_nn : 0 ≤ c - a := sub_nonneg.mpr hc.1.le
  have hbc_nn : 0 ≤ b - c := sub_nonneg.mpr hc.2.le
  have hg'_nonneg : 0 ≤ g' c := by
    have hg'_eq : g' c =
        (c - a) ^ 8 * ((c - a) * (b ^ 2 + a * b + a * (b - c)) + a * (b - c) * (b + c)) /
          (a * c * (c + a) ^ 10) := by
      dsimp only [g', s, s']
      norm_num only
      simp only [← div_eq_mul_inv, div_pow]
      have ha0 : a ≠ 0 := ha.ne'
      have hc0 : c ≠ 0 := hc_pos.ne'
      have hca0 : c + a ≠ 0 := hca_pos.ne'
      field_simp [ha0, hc0, hca0]
      ring
    rw [hg'_eq]
    positivity
  have hdiff_eq : g b - g a = g' c * (b - a) := ((eq_div_iff hba_pos.ne').mp hc_slope).symm
  have hdiff_nonneg : 0 ≤ g b - g a := by
    rw [hdiff_eq]
    exact mul_nonneg hg'_nonneg hba_pos.le
  have halg : g b - g a =
      2 * (((b - a) / (b + a)) + ((b - a) / (b + a)) ^ 3 / 3 +
        ((b - a) / (b + a)) ^ 5 / 5 + ((b - a) / (b + a)) ^ 7 / 7) +
      ((b + a) ^ 2 / (18 * a ^ 2)) * ((b - a) / (b + a)) ^ 9 -
      (Real.log b - Real.log a) := by
    dsimp only [g, s]
    simp only [← div_eq_mul_inv, div_pow]
    have hab0 : b + a ≠ 0 := (add_pos hb ha).ne'
    have haa0 : a + a ≠ 0 := (add_pos ha ha).ne'
    field_simp [hab0, haa0]
    ring
  linarith

/-- **Four-Panel 8th-Order Lower Bound `693147179 / 1000000000 ≤ Real.log 2`**. -/
theorem four_panel_artanh_log_two_lower :
    (693147179 / 1000000000 : ℝ) ≤ Real.log 2 := by
  have h1 := artanh_degree_seven_le_log_sub_log (a := 1) (b := 5 / 4) (by norm_num) (by norm_num)
  have h2 := artanh_degree_seven_le_log_sub_log (a := 5 / 4) (b := 3 / 2) (by norm_num) (by norm_num)
  have h3 := artanh_degree_seven_le_log_sub_log (a := 3 / 2) (b := 7 / 4) (by norm_num) (by norm_num)
  have h4 := artanh_degree_seven_le_log_sub_log (a := 7 / 4) (b := 2) (by norm_num) (by norm_num)
  rw [Real.log_one] at h1
  linarith

/-- **Four-Panel 8th-Order Upper Bound `Real.log 2 ≤ 693147181 / 1000000000`**. -/
theorem four_panel_artanh_log_two_upper :
    Real.log 2 ≤ 693147181 / 1000000000 := by
  have h1 := log_sub_log_le_artanh_degree_nine (a := 1) (b := 5 / 4) (by norm_num) (by norm_num)
  have h2 := log_sub_log_le_artanh_degree_nine (a := 5 / 4) (b := 3 / 2) (by norm_num) (by norm_num)
  have h3 := log_sub_log_le_artanh_degree_nine (a := 3 / 2) (b := 7 / 4) (by norm_num) (by norm_num)
  have h4 := log_sub_log_le_artanh_degree_nine (a := 7 / 4) (b := 2) (by norm_num) (by norm_num)
  rw [Real.log_one] at h1
  linarith

/-- **Eight-Panel 8th-Order Lower Bound `1098612287 / 1000000000 ≤ Real.log 3`**. -/
theorem four_panel_artanh_log_three_lower :
    (1098612287 / 1000000000 : ℝ) ≤ Real.log 3 := by
  have h0 := four_panel_artanh_log_two_lower
  have h1 := artanh_degree_seven_le_log_sub_log (a := 2) (b := 9 / 4) (by norm_num) (by norm_num)
  have h2 := artanh_degree_seven_le_log_sub_log (a := 9 / 4) (b := 5 / 2) (by norm_num) (by norm_num)
  have h3 := artanh_degree_seven_le_log_sub_log (a := 5 / 2) (b := 11 / 4) (by norm_num) (by norm_num)
  have h4 := artanh_degree_seven_le_log_sub_log (a := 11 / 4) (b := 3) (by norm_num) (by norm_num)
  linarith

/-- **Eight-Panel 8th-Order Upper Bound `Real.log 3 ≤ 1098612289 / 1000000000`**. -/
theorem four_panel_artanh_log_three_upper :
    Real.log 3 ≤ 1098612289 / 1000000000 := by
  have h1 := log_sub_log_le_artanh_degree_nine (a := 1) (b := 5 / 4) (by norm_num) (by norm_num)
  have h2 := log_sub_log_le_artanh_degree_nine (a := 5 / 4) (b := 3 / 2) (by norm_num) (by norm_num)
  have h3 := log_sub_log_le_artanh_degree_nine (a := 3 / 2) (b := 7 / 4) (by norm_num) (by norm_num)
  have h4 := log_sub_log_le_artanh_degree_nine (a := 7 / 4) (b := 2) (by norm_num) (by norm_num)
  have h5 := log_sub_log_le_artanh_degree_nine (a := 2) (b := 9 / 4) (by norm_num) (by norm_num)
  have h6 := log_sub_log_le_artanh_degree_nine (a := 9 / 4) (b := 5 / 2) (by norm_num) (by norm_num)
  have h7 := log_sub_log_le_artanh_degree_nine (a := 5 / 2) (b := 11 / 4) (by norm_num) (by norm_num)
  have h8 := log_sub_log_le_artanh_degree_nine (a := 11 / 4) (b := 3) (by norm_num) (by norm_num)
  rw [Real.log_one] at h1
  linarith

/-- Pell convergent lower bound `1607521 / 1136689 ≤ Real.sqrt 2`. -/
theorem pell_sqrt_two_lower_nine :
    (1607521 / 1136689 : ℝ) ≤ Real.sqrt 2 := by
  rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1607521 / 1136689)]
  exact Real.sqrt_le_sqrt (by norm_num)

/-- Pell convergent upper bound `Real.sqrt 2 ≤ 665857 / 470832`. -/
theorem pell_sqrt_two_upper_nine :
    Real.sqrt 2 ≤ 665857 / 470832 := by
  rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 665857 / 470832)]
  exact Real.sqrt_le_sqrt (by norm_num)

/-- Pell convergent lower bound `716035 / 413403 ≤ Real.sqrt 3`. -/
theorem pell_sqrt_three_lower_nine :
    (716035 / 413403 : ℝ) ≤ Real.sqrt 3 := by
  rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 716035 / 413403)]
  exact Real.sqrt_le_sqrt (by norm_num)

/-- Pell convergent upper bound `Real.sqrt 3 ≤ 978122 / 564719`. -/
theorem pell_sqrt_three_upper_nine :
    Real.sqrt 3 ≤ 978122 / 564719 := by
  rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 978122 / 564719)]
  exact Real.sqrt_le_sqrt (by norm_num)

/-- **Exact Closed Form of the Second-Cell (`n = 3`, `[2, 3]`) Cosine-Log Quadrature Integral $I_3(r)$**. -/
theorem neg_mul_integral_two_three_cosLogProfile_sub_cellSecant_div_sqrt_eq (r : ℝ) :
    -(1 / 4 + r ^ 2) *
        (∫ x in (2 : ℝ)..3,
          (cosLogProfile r x - cellSecant (cosLogProfile r) 3 x) / Real.sqrt x) =
      -(1 / 4 + r ^ 2) * (cosLogAntideriv r 3 - cosLogAntideriv r 2) +
        (1 / 4 + r ^ 2) *
          (((12 * Real.sqrt 3 - 14 * Real.sqrt 2) / 3) * Real.cos (r * Real.log 2) +
            ((8 * Real.sqrt 2 - 6 * Real.sqrt 3) / 3) * Real.cos (r * Real.log 3)) := by
  let F : ℝ → ℝ := fun x =>
    cosLogAntideriv r x -
      ((2 * cosLogProfile r 2 - cosLogProfile r 3) * (2 * Real.sqrt x) +
        (cosLogProfile r 3 - cosLogProfile r 2) *
          ((2 / 3) * x * Real.sqrt x - 2 * Real.sqrt x))
  have hderiv : ∀ x ∈ uIcc (2 : ℝ) 3,
      HasDerivAt F ((cosLogProfile r x - cellSecant (cosLogProfile r) 3 x) / Real.sqrt x) x := by
    intro x hx
    rw [uIcc_of_le (by norm_num : (2 : ℝ) ≤ 3)] at hx
    have hx_pos : 0 < x := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hx.1
    have hsqrt_ne : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr hx_pos).ne'
    have hd1 := hasDerivAt_cosLogAntideriv r hx_pos
    have hd2 : HasDerivAt
        (fun t => (2 * cosLogProfile r 2 - cosLogProfile r 3) * (2 * Real.sqrt t))
        ((2 * cosLogProfile r 2 - cosLogProfile r 3) * (2 * (1 / (2 * Real.sqrt x)))) x :=
      ((Real.hasDerivAt_sqrt hx_pos.ne').const_mul 2).const_mul
        (2 * cosLogProfile r 2 - cosLogProfile r 3)
    have hd3 := (hasDerivAt_two_thirds_mul_sqrt_sub_two_mul_sqrt hx_pos).const_mul
      (cosLogProfile r 3 - cosLogProfile r 2)
    refine (hd1.sub (hd2.add hd3)).congr_deriv ?_
    unfold cellSecant cosLogProfile
    norm_num
    field_simp [hsqrt_ne]
    ring
  have hint : IntervalIntegrable
      (fun x => (cosLogProfile r x - cellSecant (cosLogProfile r) 3 x) / Real.sqrt x)
      volume 2 3 := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le (by norm_num : (2 : ℝ) ≤ 3)]
    refine ContinuousOn.div ?_ (Real.continuous_sqrt.continuousOn) (fun x hx =>
      (Real.sqrt_pos.mpr (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hx.1)).ne')
    refine ContinuousOn.sub ?_ ?_
    · unfold cosLogProfile
      exact Real.continuous_cos.comp_continuousOn
        (continuousOn_const.mul (Real.continuousOn_log.mono fun x hx =>
          (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hx.1).ne'))
    · unfold cellSecant
      fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  dsimp [F, cosLogProfile]
  ring

/-- **Exact Two-Cell (`[1, 3]`) + Resolvent Telescoped Numerator Identity**:
summing `I_2(r) + I_3(r) + (1 / 2) / (1 / 4 + r ^ 2)` over `[1, 2] ∪ [2, 3]` cancels both
`cosLogAntideriv r 2` (including `√2 r sin(r log 2)`) and `cosLogAntideriv r 1 = (1 / 2) / (1 / 4 + r ^ 2)`
identically! -/
theorem neg_mul_integral_one_three_cosLogProfile_sub_half_eq (r : ℝ) :
    -(1 / 4 + r ^ 2) *
        ((∫ x in (1 : ℝ)..2,
          (cosLogProfile r x - cellSecant (cosLogProfile r) 2 x) / Real.sqrt x) +
         (∫ x in (2 : ℝ)..3,
          (cosLogProfile r x - cellSecant (cosLogProfile r) 3 x) / Real.sqrt x)) -
      1 / 2 =
    -1 / 2 + 2 * (Real.sqrt 3 - 1) * r ^ 2 -
      Real.sqrt 3 * r * Real.sin (r * Real.log 3) +
      ((Real.sqrt 3 - (2 / 3) * Real.sqrt 2) -
        ((8 * Real.sqrt 2 - 6 * Real.sqrt 3) / 3) * r ^ 2) *
        (1 - Real.cos (r * Real.log 3)) -
      (1 / 4 + r ^ 2) *
        ((4 + 12 * Real.sqrt 3 - 16 * Real.sqrt 2) / 3) *
        (1 - Real.cos (r * Real.log 2)) := by
  have h12 := neg_mul_integral_one_two_cosLogProfile_sub_cellSecant_div_sqrt_eq r
  have h23 := neg_mul_integral_two_three_cosLogProfile_sub_cellSecant_div_sqrt_eq r
  have hden_ne : (1 / 4 + r ^ 2 : ℝ) ≠ 0 := by positivity
  have hanti :
      -(1 / 4 + r ^ 2) * (cosLogAntideriv r 3 - cosLogAntideriv r 2) =
        -(Real.sqrt 3 * ((1 / 2) * Real.cos (r * Real.log 3) + r * Real.sin (r * Real.log 3))) +
          Real.sqrt 2 * ((1 / 2) * Real.cos (r * Real.log 2) + r * Real.sin (r * Real.log 2)) := by
    unfold cosLogAntideriv
    field_simp [hden_ne]
    ring
  rw [mul_add, h12, h23, hanti]
  ring

/-! ## Section 2: The Global Two-Cell + Resolvent Envelope `-(41 / 2880) r² + 19 / 144 - (1 / 2) / (1 / 4 + r²) ≤ I_2(r) + I_3(r)` and the `41 / 2880 + 31 / 2880 = 1 / 40` Resolvent + Secant Numerator Law -/


private lemma two_cell_coeff_bound_0 {ℓ2 ℓ3 s3 C3 w2 : ℝ}
    (hℓ2_1 : 693147179 / 1000000000 ≤ ℓ2)
    (hℓ3_1 : 1098612287 / 1000000000 ≤ ℓ3)
    (hℓ3_2 : ℓ3 ≤ 1098612289 / 1000000000)
    (hs3_1 : 191861 / 110771 ≤ s3)
    (hs3_2 : s3 ≤ 262087 / 151316)
    (hC3_2 : C3 ≤ 21085900441 / 26716655592)
    (hw2_1 : 90538942856 / 125912177219 ≤ w2) :
    2 * (s3 - 1) + -(s3 * ℓ3 ^ 1 / 1) + C3 * ℓ3 ^ 2 / 2 + -(w2 * ℓ2 ^ 2 / 8) ≤ -56479903 / 10000000000 := by
  have hℓ3_0 : 0 ≤ ℓ3 := by linarith only [hℓ3_1]
  have hs3_0 : 0 ≤ s3 := by linarith only [hs3_1]
  have hp_s3 : (1098612287 / 1000000000 : ℝ) ≤ ℓ3 ^ 1 := le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hℓ3_1 1)
  have hm_s3 := mul_le_mul hs3_1 hp_s3 (by norm_num) hs3_0
  have hp_C3 : ℓ3 ^ 2 ≤ 1206948962 / 1000000000 := le_trans (pow_le_pow_left₀ hℓ3_0 hℓ3_2 2) (by norm_num)
  have hm_C3 := mul_le_mul hC3_2 hp_C3 (by positivity) (by norm_num)
  have hw2_0 : 0 ≤ w2 := by linarith only [hw2_1]
  have hp_w2a : (480453011 / 1000000000 : ℝ) ≤ ℓ2 ^ 2 := le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hℓ2_1 2)
  have hm_w2a := mul_le_mul hw2_1 hp_w2a (by norm_num) hw2_0
  linarith only [hm_s3, hm_C3, hm_w2a, hs3_2]

private lemma two_cell_coeff_bound_1 {ℓ2 ℓ3 s3 C3 B3 w2 : ℝ}
    (hℓ2_1 : 693147179 / 1000000000 ≤ ℓ2)
    (hℓ2_2 : ℓ2 ≤ 693147181 / 1000000000)
    (hℓ3_1 : 1098612287 / 1000000000 ≤ ℓ3)
    (hℓ3_2 : ℓ3 ≤ 1098612289 / 1000000000)
    (hs3_2 : s3 ≤ 262087 / 151316)
    (hC3_1 : 298125447305 / 377736531657 ≤ C3)
    (hB3_1 : 1025701003 / 3339581949 ≤ B3)
    (hw2_1 : 90538942856 / 125912177219 ≤ w2)
    (hw2_2 : w2 ≤ 2401373926 / 3339581949) :
    s3 * ℓ3 ^ 3 / 6 + -(C3 * ℓ3 ^ 4 / 24) + -(B3 * ℓ3 ^ 2 / 2) + w2 * ℓ2 ^ 4 / 96 + -(w2 * ℓ2 ^ 2 / 2) ≤ -21487403336 / 1000000000000 := by
  have hℓ2_0 : 0 ≤ ℓ2 := by linarith only [hℓ2_1]
  have hℓ3_0 : 0 ≤ ℓ3 := by linarith only [hℓ3_1]
  have hp_s3 : ℓ3 ^ 3 ≤ 1325968962 / 1000000000 := le_trans (pow_le_pow_left₀ hℓ3_0 hℓ3_2 3) (by norm_num)
  have hm_s3 := mul_le_mul hs3_2 hp_s3 (by positivity) (by norm_num)
  have hC3_0 : 0 ≤ C3 := by linarith only [hC3_1]
  have hp_C3 : (1456725784 / 1000000000 : ℝ) ≤ ℓ3 ^ 4 := le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hℓ3_1 4)
  have hm_C3 := mul_le_mul hC3_1 hp_C3 (by norm_num) hC3_0
  have hB3_0 : 0 ≤ B3 := by linarith only [hB3_1]
  have hp_B3 : (1206948957 / 1000000000 : ℝ) ≤ ℓ3 ^ 2 := le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hℓ3_1 2)
  have hm_B3 := mul_le_mul hB3_1 hp_B3 (by norm_num) hB3_0
  have hp_w2a : ℓ2 ^ 4 ≤ 230835100 / 1000000000 := le_trans (pow_le_pow_left₀ hℓ2_0 hℓ2_2 4) (by norm_num)
  have hm_w2a := mul_le_mul hw2_2 hp_w2a (by positivity) (by norm_num)
  have hw2_0 : 0 ≤ w2 := by linarith only [hw2_1]
  have hp_w2b : (480453011 / 1000000000 : ℝ) ≤ ℓ2 ^ 2 := le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hℓ2_1 2)
  have hm_w2b := mul_le_mul hw2_1 hp_w2b (by norm_num) hw2_0
  linarith only [hm_s3, hm_C3, hm_B3, hm_w2a, hm_w2b]

private lemma two_cell_coeff_bound_2 {ℓ2 ℓ3 s3 C3 B3 w2 : ℝ}
    (hℓ2_1 : 693147179 / 1000000000 ≤ ℓ2)
    (hℓ2_2 : ℓ2 ≤ 693147181 / 1000000000)
    (hℓ3_1 : 1098612287 / 1000000000 ≤ ℓ3)
    (hℓ3_2 : ℓ3 ≤ 1098612289 / 1000000000)
    (hs3_1 : 191861 / 110771 ≤ s3)
    (hC3_2 : C3 ≤ 21085900441 / 26716655592)
    (hB3_2 : B3 ≤ 116015940154 / 377736531657)
    (hw2_1 : 90538942856 / 125912177219 ≤ w2)
    (hw2_2 : w2 ≤ 2401373926 / 3339581949) :
    -(s3 * ℓ3 ^ 5 / 120) + C3 * ℓ3 ^ 6 / 720 + B3 * ℓ3 ^ 4 / 24 + -(w2 * ℓ2 ^ 6 / 2880) + w2 * ℓ2 ^ 4 / 24 ≤ 435830757297 / 100000000000000 := by
  have hℓ2_0 : 0 ≤ ℓ2 := by linarith only [hℓ2_1]
  have hℓ3_0 : 0 ≤ ℓ3 := by linarith only [hℓ3_1]
  have hs3_0 : 0 ≤ s3 := by linarith only [hs3_1]
  have hp_s3 : (1600376845 / 1000000000 : ℝ) ≤ ℓ3 ^ 5 := le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hℓ3_1 5)
  have hm_s3 := mul_le_mul hs3_1 hp_s3 (by norm_num) hs3_0
  have hp_C3 : ℓ3 ^ 6 ≤ 1758193689 / 1000000000 := le_trans (pow_le_pow_left₀ hℓ3_0 hℓ3_2 6) (by norm_num)
  have hm_C3 := mul_le_mul hC3_2 hp_C3 (by positivity) (by norm_num)
  have hp_B3 : ℓ3 ^ 4 ≤ 1456725797 / 1000000000 := le_trans (pow_le_pow_left₀ hℓ3_0 hℓ3_2 4) (by norm_num)
  have hm_B3 := mul_le_mul hB3_2 hp_B3 (by positivity) (by norm_num)
  have hw2_0 : 0 ≤ w2 := by linarith only [hw2_1]
  have hp_w2a : (110905416 / 1000000000 : ℝ) ≤ ℓ2 ^ 6 := le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hℓ2_1 6)
  have hm_w2a := mul_le_mul hw2_1 hp_w2a (by norm_num) hw2_0
  have hp_w2b : ℓ2 ^ 4 ≤ 230835100 / 1000000000 := le_trans (pow_le_pow_left₀ hℓ2_0 hℓ2_2 4) (by norm_num)
  have hm_w2b := mul_le_mul hw2_2 hp_w2b (by positivity) (by norm_num)
  linarith only [hm_s3, hm_C3, hm_B3, hm_w2a, hm_w2b]

private lemma two_cell_coeff_bound_3 {ℓ2 ℓ3 s3 C3 B3 w2 : ℝ}
    (hℓ2_1 : 693147179 / 1000000000 ≤ ℓ2)
    (hℓ2_2 : ℓ2 ≤ 693147181 / 1000000000)
    (hℓ3_1 : 1098612287 / 1000000000 ≤ ℓ3)
    (hℓ3_2 : ℓ3 ≤ 1098612289 / 1000000000)
    (hs3_2 : s3 ≤ 262087 / 151316)
    (hC3_1 : 298125447305 / 377736531657 ≤ C3)
    (hB3_1 : 1025701003 / 3339581949 ≤ B3)
    (hw2_1 : 90538942856 / 125912177219 ≤ w2)
    (hw2_2 : w2 ≤ 2401373926 / 3339581949) :
    s3 * ℓ3 ^ 7 / 5040 + -(C3 * ℓ3 ^ 8 / 40320) + -(B3 * ℓ3 ^ 6 / 720) + w2 * ℓ2 ^ 8 / 161280 + -(w2 * ℓ2 ^ 6 / 720) ≤ -2382583391645 / 10000000000000000 := by
  have hℓ2_0 : 0 ≤ ℓ2 := by linarith only [hℓ2_1]
  have hℓ3_0 : 0 ≤ ℓ3 := by linarith only [hℓ3_1]
  have hp_s3 : ℓ3 ^ 7 ≤ 1931573194 / 1000000000 := le_trans (pow_le_pow_left₀ hℓ3_0 hℓ3_2 7) (by norm_num)
  have hm_s3 := mul_le_mul hs3_2 hp_s3 (by positivity) (by norm_num)
  have hC3_0 : 0 ≤ C3 := by linarith only [hC3_1]
  have hp_C3 : (2122050009 / 1000000000 : ℝ) ≤ ℓ3 ^ 8 := le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hℓ3_1 8)
  have hm_C3 := mul_le_mul hC3_1 hp_C3 (by norm_num) hC3_0
  have hB3_0 : 0 ≤ B3 := by linarith only [hB3_1]
  have hp_B3 : (1758193665 / 1000000000 : ℝ) ≤ ℓ3 ^ 6 := le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hℓ3_1 6)
  have hm_B3 := mul_le_mul hB3_1 hp_B3 (by norm_num) hB3_0
  have hp_w2a : ℓ2 ^ 8 ≤ 53284844 / 1000000000 := le_trans (pow_le_pow_left₀ hℓ2_0 hℓ2_2 8) (by norm_num)
  have hm_w2a := mul_le_mul hw2_2 hp_w2a (by positivity) (by norm_num)
  have hw2_0 : 0 ≤ w2 := by linarith only [hw2_1]
  have hp_w2b : (110905416 / 1000000000 : ℝ) ≤ ℓ2 ^ 6 := le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hℓ2_1 6)
  have hm_w2b := mul_le_mul hw2_1 hp_w2b (by norm_num) hw2_0
  linarith only [hm_s3, hm_C3, hm_B3, hm_w2a, hm_w2b]

private lemma two_cell_coeff_bound_4 {ℓ2 ℓ3 s3 C3 B3 w2 : ℝ}
    (hℓ2_1 : 693147179 / 1000000000 ≤ ℓ2)
    (hℓ2_2 : ℓ2 ≤ 693147181 / 1000000000)
    (hℓ3_1 : 1098612287 / 1000000000 ≤ ℓ3)
    (hℓ3_2 : ℓ3 ≤ 1098612289 / 1000000000)
    (hs3_1 : 191861 / 110771 ≤ s3)
    (hC3_2 : C3 ≤ 21085900441 / 26716655592)
    (hB3_2 : B3 ≤ 116015940154 / 377736531657)
    (hw2_1 : 90538942856 / 125912177219 ≤ w2)
    (hw2_2 : w2 ≤ 2401373926 / 3339581949) :
    -(s3 * ℓ3 ^ 9 / 362880) + C3 * ℓ3 ^ 10 / 3628800 + B3 * ℓ3 ^ 8 / 40320 + -(w2 * ℓ2 ^ 10 / 14515200) + w2 * ℓ2 ^ 8 / 40320 ≤ 6543111114386 / 1000000000000000000 := by
  have hℓ2_0 : 0 ≤ ℓ2 := by linarith only [hℓ2_1]
  have hℓ3_0 : 0 ≤ ℓ3 := by linarith only [hℓ3_1]
  have hs3_0 : 0 ≤ s3 := by linarith only [hs3_1]
  have hp_s3 : (2331310213 / 1000000000 : ℝ) ≤ ℓ3 ^ 9 := le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hℓ3_1 9)
  have hm_s3 := mul_le_mul hs3_1 hp_s3 (by norm_num) hs3_0
  have hp_C3 : ℓ3 ^ 10 ≤ 2561206103 / 1000000000 := le_trans (pow_le_pow_left₀ hℓ3_0 hℓ3_2 10) (by norm_num)
  have hm_C3 := mul_le_mul hC3_2 hp_C3 (by positivity) (by norm_num)
  have hp_B3 : ℓ3 ^ 8 ≤ 2122050048 / 1000000000 := le_trans (pow_le_pow_left₀ hℓ3_0 hℓ3_2 8) (by norm_num)
  have hm_B3 := mul_le_mul hB3_2 hp_B3 (by positivity) (by norm_num)
  have hw2_0 : 0 ≤ w2 := by linarith only [hw2_1]
  have hp_w2a : (25600862 / 1000000000 : ℝ) ≤ ℓ2 ^ 10 := le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hℓ2_1 10)
  have hm_w2a := mul_le_mul hw2_1 hp_w2a (by norm_num) hw2_0
  have hp_w2b : ℓ2 ^ 8 ≤ 53284844 / 1000000000 := le_trans (pow_le_pow_left₀ hℓ2_0 hℓ2_2 8) (by norm_num)
  have hm_w2b := mul_le_mul hw2_2 hp_w2b (by positivity) (by norm_num)
  linarith only [hm_s3, hm_C3, hm_B3, hm_w2a, hm_w2b]

private lemma two_cell_coeff_bound_5 {ℓ2 ℓ3 s3 C3 B3 w2 : ℝ}
    (hℓ2_1 : 693147179 / 1000000000 ≤ ℓ2)
    (hℓ2_2 : ℓ2 ≤ 693147181 / 1000000000)
    (hℓ3_1 : 1098612287 / 1000000000 ≤ ℓ3)
    (hℓ3_2 : ℓ3 ≤ 1098612289 / 1000000000)
    (hs3_2 : s3 ≤ 262087 / 151316)
    (hC3_1 : 298125447305 / 377736531657 ≤ C3)
    (hB3_1 : 1025701003 / 3339581949 ≤ B3)
    (hw2_1 : 90538942856 / 125912177219 ≤ w2)
    (hw2_2 : w2 ≤ 2401373926 / 3339581949) :
    s3 * ℓ3 ^ 11 / 39916800 + -(C3 * ℓ3 ^ 12 / 479001600) + -(B3 * ℓ3 ^ 10 / 3628800) + w2 * ℓ2 ^ 12 / 1916006400 + -(w2 * ℓ2 ^ 10 / 3628800) ≤ -10484330683375 / 100000000000000000000 := by
  have hℓ2_0 : 0 ≤ ℓ2 := by linarith only [hℓ2_1]
  have hℓ3_0 : 0 ≤ ℓ3 := by linarith only [hℓ3_1]
  have hp_s3 : ℓ3 ^ 11 ≤ 2813772500 / 1000000000 := le_trans (pow_le_pow_left₀ hℓ3_0 hℓ3_2 11) (by norm_num)
  have hm_s3 := mul_le_mul hs3_2 hp_s3 (by positivity) (by norm_num)
  have hC3_0 : 0 ≤ C3 := by linarith only [hC3_1]
  have hp_C3 : (3091244963 / 1000000000 : ℝ) ≤ ℓ3 ^ 12 := le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hℓ3_1 12)
  have hm_C3 := mul_le_mul hC3_1 hp_C3 (by norm_num) hC3_0
  have hB3_0 : 0 ≤ B3 := by linarith only [hB3_1]
  have hp_B3 : (2561206045 / 1000000000 : ℝ) ≤ ℓ3 ^ 10 := le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hℓ3_1 10)
  have hm_B3 := mul_le_mul hB3_1 hp_B3 (by norm_num) hB3_0
  have hp_w2a : ℓ2 ^ 12 ≤ 12300013 / 1000000000 := le_trans (pow_le_pow_left₀ hℓ2_0 hℓ2_2 12) (by norm_num)
  have hm_w2a := mul_le_mul hw2_2 hp_w2a (by positivity) (by norm_num)
  have hw2_0 : 0 ≤ w2 := by linarith only [hw2_1]
  have hp_w2b : (25600862 / 1000000000 : ℝ) ≤ ℓ2 ^ 10 := le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hℓ2_1 10)
  have hm_w2b := mul_le_mul hw2_1 hp_w2b (by norm_num) hw2_0
  linarith only [hm_s3, hm_C3, hm_B3, hm_w2a, hm_w2b]

private lemma two_cell_coeff_bound_6 {ℓ2 ℓ3 s3 C3 B3 w2 : ℝ}
    (hℓ2_1 : 693147179 / 1000000000 ≤ ℓ2)
    (hℓ2_2 : ℓ2 ≤ 693147181 / 1000000000)
    (hℓ3_1 : 1098612287 / 1000000000 ≤ ℓ3)
    (hℓ3_2 : ℓ3 ≤ 1098612289 / 1000000000)
    (hs3_1 : 191861 / 110771 ≤ s3)
    (hC3_2 : C3 ≤ 21085900441 / 26716655592)
    (hB3_2 : B3 ≤ 116015940154 / 377736531657)
    (hw2_1 : 90538942856 / 125912177219 ≤ w2)
    (hw2_2 : w2 ≤ 2401373926 / 3339581949) :
    -(s3 * ℓ3 ^ 13 / 6227020800) + C3 * ℓ3 ^ 14 / 87178291200 + B3 * ℓ3 ^ 12 / 479001600 + -(w2 * ℓ2 ^ 14 / 348713164800) + w2 * ℓ2 ^ 12 / 479001600 ≤ 10897053117410 / 10000000000000000000000 := by
  have hℓ2_0 : 0 ≤ ℓ2 := by linarith only [hℓ2_1]
  have hℓ3_0 : 0 ≤ ℓ3 := by linarith only [hℓ3_1]
  have hs3_0 : 0 ≤ s3 := by linarith only [hs3_1]
  have hp_s3 : (3396079698 / 1000000000 : ℝ) ≤ ℓ3 ^ 13 := le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hℓ3_1 13)
  have hm_s3 := mul_le_mul hs3_1 hp_s3 (by norm_num) hs3_0
  have hp_C3 : ℓ3 ^ 14 ≤ 3730975003 / 1000000000 := le_trans (pow_le_pow_left₀ hℓ3_0 hℓ3_2 14) (by norm_num)
  have hm_C3 := mul_le_mul hC3_2 hp_C3 (by positivity) (by norm_num)
  have hp_B3 : ℓ3 ^ 12 ≤ 3091245049 / 1000000000 := le_trans (pow_le_pow_left₀ hℓ3_0 hℓ3_2 12) (by norm_num)
  have hm_B3 := mul_le_mul hB3_2 hp_B3 (by positivity) (by norm_num)
  have hw2_0 : 0 ≤ w2 := by linarith only [hw2_1]
  have hp_w2a : (5909577 / 1000000000 : ℝ) ≤ ℓ2 ^ 14 := le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hℓ2_1 14)
  have hm_w2a := mul_le_mul hw2_1 hp_w2a (by norm_num) hw2_0
  have hp_w2b : ℓ2 ^ 12 ≤ 12300013 / 1000000000 := le_trans (pow_le_pow_left₀ hℓ2_0 hℓ2_2 12) (by norm_num)
  have hm_w2b := mul_le_mul hw2_2 hp_w2b (by positivity) (by norm_num)
  linarith only [hm_s3, hm_C3, hm_B3, hm_w2a, hm_w2b]

private lemma two_cell_coeff_bound_7 {ℓ2 ℓ3 s3 C3 B3 w2 : ℝ}
    (hℓ2_1 : 693147179 / 1000000000 ≤ ℓ2)
    (hℓ2_2 : ℓ2 ≤ 693147181 / 1000000000)
    (hℓ3_1 : 1098612287 / 1000000000 ≤ ℓ3)
    (hℓ3_2 : ℓ3 ≤ 1098612289 / 1000000000)
    (hs3_2 : s3 ≤ 262087 / 151316)
    (hC3_1 : 298125447305 / 377736531657 ≤ C3)
    (hB3_1 : 1025701003 / 3339581949 ≤ B3)
    (hw2_1 : 90538942856 / 125912177219 ≤ w2)
    (hw2_2 : w2 ≤ 2401373926 / 3339581949) :
    s3 * ℓ3 ^ 15 / 1307674368000 + -(C3 * ℓ3 ^ 16 / 20922789888000) + -(B3 * ℓ3 ^ 14 / 87178291200) + w2 * ℓ2 ^ 16 / 83691159552000 + -(w2 * ℓ2 ^ 14 / 87178291200) ≤ -7933940492503 / 1000000000000000000000000 := by
  have hℓ2_0 : 0 ≤ ℓ2 := by linarith only [hℓ2_1]
  have hℓ3_0 : 0 ≤ ℓ3 := by linarith only [hℓ3_1]
  have hp_s3 : ℓ3 ^ 15 ≤ 4098894989 / 1000000000 := le_trans (pow_le_pow_left₀ hℓ3_0 hℓ3_2 15) (by norm_num)
  have hm_s3 := mul_le_mul hs3_2 hp_s3 (by positivity) (by norm_num)
  have hC3_0 : 0 ≤ C3 := by linarith only [hC3_1]
  have hp_C3 : (4503096240 / 1000000000 : ℝ) ≤ ℓ3 ^ 16 := le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hℓ3_1 16)
  have hm_C3 := mul_le_mul hC3_1 hp_C3 (by norm_num) hC3_0
  have hB3_0 : 0 ≤ B3 := by linarith only [hB3_1]
  have hp_B3 : (3730974882 / 1000000000 : ℝ) ≤ ℓ3 ^ 14 := le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hℓ3_1 14)
  have hm_B3 := mul_le_mul hB3_1 hp_B3 (by norm_num) hB3_0
  have hp_w2a : ℓ2 ^ 16 ≤ 2839275 / 1000000000 := le_trans (pow_le_pow_left₀ hℓ2_0 hℓ2_2 16) (by norm_num)
  have hm_w2a := mul_le_mul hw2_2 hp_w2a (by positivity) (by norm_num)
  have hw2_0 : 0 ≤ w2 := by linarith only [hw2_1]
  have hp_w2b : (5909577 / 1000000000 : ℝ) ≤ ℓ2 ^ 14 := le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hℓ2_1 14)
  have hm_w2b := mul_le_mul hw2_1 hp_w2b (by norm_num) hw2_0
  linarith only [hm_s3, hm_C3, hm_B3, hm_w2a, hm_w2b]

private lemma two_cell_coeff_bound_8 {ℓ2 ℓ3 s3 C3 B3 w2 : ℝ}
    (hℓ2_1 : 693147179 / 1000000000 ≤ ℓ2)
    (hℓ2_2 : ℓ2 ≤ 693147181 / 1000000000)
    (hℓ3_1 : 1098612287 / 1000000000 ≤ ℓ3)
    (hℓ3_2 : ℓ3 ≤ 1098612289 / 1000000000)
    (hs3_1 : 191861 / 110771 ≤ s3)
    (hC3_2 : C3 ≤ 21085900441 / 26716655592)
    (hB3_2 : B3 ≤ 116015940154 / 377736531657)
    (hw2_1 : 90538942856 / 125912177219 ≤ w2)
    (hw2_2 : w2 ≤ 2401373926 / 3339581949) :
    -(s3 * ℓ3 ^ 17 / 355687428096000) + C3 * ℓ3 ^ 18 / 6402373705728000 + B3 * ℓ3 ^ 16 / 20922789888000 + -(w2 * ℓ2 ^ 18 / 25609494822912000) + w2 * ℓ2 ^ 16 / 20922789888000 ≤ 4277979372642 / 100000000000000000000000000 := by
  have hℓ2_0 : 0 ≤ ℓ2 := by linarith only [hℓ2_1]
  have hℓ3_0 : 0 ≤ ℓ3 := by linarith only [hℓ3_1]
  have hs3_0 : 0 ≤ s3 := by linarith only [hs3_1]
  have hp_s3 : (4947156858 / 1000000000 : ℝ) ≤ ℓ3 ^ 17 := le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hℓ3_1 17)
  have hm_s3 := mul_le_mul hs3_1 hp_s3 (by norm_num) hs3_0
  have hp_C3 : ℓ3 ^ 18 ≤ 5435007534 / 1000000000 := le_trans (pow_le_pow_left₀ hℓ3_0 hℓ3_2 18) (by norm_num)
  have hm_C3 := mul_le_mul hC3_2 hp_C3 (by positivity) (by norm_num)
  have hp_B3 : ℓ3 ^ 16 ≤ 4503096407 / 1000000000 := le_trans (pow_le_pow_left₀ hℓ3_0 hℓ3_2 16) (by norm_num)
  have hm_B3 := mul_le_mul hB3_2 hp_B3 (by positivity) (by norm_num)
  have hw2_0 : 0 ≤ w2 := by linarith only [hw2_1]
  have hp_w2a : (1364137 / 1000000000 : ℝ) ≤ ℓ2 ^ 18 := le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hℓ2_1 18)
  have hm_w2a := mul_le_mul hw2_1 hp_w2a (by norm_num) hw2_0
  have hp_w2b : ℓ2 ^ 16 ≤ 2839275 / 1000000000 := le_trans (pow_le_pow_left₀ hℓ2_0 hℓ2_2 16) (by norm_num)
  have hm_w2b := mul_le_mul hw2_2 hp_w2b (by positivity) (by norm_num)
  linarith only [hm_s3, hm_C3, hm_B3, hm_w2a, hm_w2b]

private lemma two_cell_coeff_bound_9 {ℓ2 ℓ3 s3 C3 B3 w2 : ℝ}
    (hℓ2_1 : 693147179 / 1000000000 ≤ ℓ2)
    (hℓ2_2 : ℓ2 ≤ 693147181 / 1000000000)
    (hℓ3_1 : 1098612287 / 1000000000 ≤ ℓ3)
    (hℓ3_2 : ℓ3 ≤ 1098612289 / 1000000000)
    (hs3_2 : s3 ≤ 262087 / 151316)
    (hC3_1 : 298125447305 / 377736531657 ≤ C3)
    (hB3_1 : 1025701003 / 3339581949 ≤ B3)
    (hw2_1 : 90538942856 / 125912177219 ≤ w2)
    (hw2_2 : w2 ≤ 2401373926 / 3339581949) :
    s3 * ℓ3 ^ 19 / 121645100408832000 + -(C3 * ℓ3 ^ 20 / 2432902008176640000) + -(B3 * ℓ3 ^ 18 / 6402373705728000) + w2 * ℓ2 ^ 20 / 9731608032706560000 + -(w2 * ℓ2 ^ 18 / 6402373705728000) ≤ -1779912971139 / 10000000000000000000000000000 := by
  have hℓ2_0 : 0 ≤ ℓ2 := by linarith only [hℓ2_1]
  have hℓ3_0 : 0 ≤ ℓ3 := by linarith only [hℓ3_1]
  have hp_s3 : ℓ3 ^ 19 ≤ 5970966068 / 1000000000 := le_trans (pow_le_pow_left₀ hℓ3_0 hℓ3_2 19) (by norm_num)
  have hm_s3 := mul_le_mul hs3_2 hp_s3 (by positivity) (by norm_num)
  have hC3_0 : 0 ≤ C3 := by linarith only [hC3_1]
  have hp_C3 : (6559776404 / 1000000000 : ℝ) ≤ ℓ3 ^ 20 := le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hℓ3_1 20)
  have hm_C3 := mul_le_mul hC3_1 hp_C3 (by norm_num) hC3_0
  have hB3_0 : 0 ≤ B3 := by linarith only [hB3_1]
  have hp_B3 : (5435007310 / 1000000000 : ℝ) ≤ ℓ3 ^ 18 := le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hℓ3_1 18)
  have hm_B3 := mul_le_mul hB3_1 hp_B3 (by norm_num) hB3_0
  have hp_w2a : ℓ2 ^ 20 ≤ 655405 / 1000000000 := le_trans (pow_le_pow_left₀ hℓ2_0 hℓ2_2 20) (by norm_num)
  have hm_w2a := mul_le_mul hw2_2 hp_w2a (by positivity) (by norm_num)
  have hw2_0 : 0 ≤ w2 := by linarith only [hw2_1]
  have hp_w2b : (1364137 / 1000000000 : ℝ) ≤ ℓ2 ^ 18 := le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hℓ2_1 18)
  have hm_w2b := mul_le_mul hw2_1 hp_w2b (by norm_num) hw2_0
  linarith only [hm_s3, hm_C3, hm_B3, hm_w2a, hm_w2b]

private lemma two_cell_coeff_bound_10 {ℓ2 ℓ3 s3 C3 B3 w2 : ℝ}
    (hℓ2_1 : 693147179 / 1000000000 ≤ ℓ2)
    (hℓ2_2 : ℓ2 ≤ 693147181 / 1000000000)
    (hℓ3_1 : 1098612287 / 1000000000 ≤ ℓ3)
    (hℓ3_2 : ℓ3 ≤ 1098612289 / 1000000000)
    (hs3_1 : 191861 / 110771 ≤ s3)
    (hC3_2 : C3 ≤ 21085900441 / 26716655592)
    (hB3_2 : B3 ≤ 116015940154 / 377736531657)
    (hw2_2 : w2 ≤ 2401373926 / 3339581949) :
    -(s3 * ℓ3 ^ 21 / 51090942171709440000) + C3 * ℓ3 ^ 22 / 1124000727777607680000 + B3 * ℓ3 ^ 20 / 2432902008176640000 + w2 * ℓ2 ^ 20 / 2432902008176640000 ≤ 589557683797 / 1000000000000000000000000000000 := by
  have hℓ2_0 : 0 ≤ ℓ2 := by linarith only [hℓ2_1]
  have hℓ3_0 : 0 ≤ ℓ3 := by linarith only [hℓ3_1]
  have hs3_0 : 0 ≤ s3 := by linarith only [hs3_1]
  have hp_s3 : (7206650957 / 1000000000 : ℝ) ≤ ℓ3 ^ 21 := le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hℓ3_1 21)
  have hm_s3 := mul_le_mul hs3_1 hp_s3 (by norm_num) hs3_0
  have hp_C3 : ℓ3 ^ 22 ≤ 7917315686 / 1000000000 := le_trans (pow_le_pow_left₀ hℓ3_0 hℓ3_2 22) (by norm_num)
  have hm_C3 := mul_le_mul hC3_2 hp_C3 (by positivity) (by norm_num)
  have hp_B3 : ℓ3 ^ 20 ≤ 6559776703 / 1000000000 := le_trans (pow_le_pow_left₀ hℓ3_0 hℓ3_2 20) (by norm_num)
  have hm_B3 := mul_le_mul hB3_2 hp_B3 (by positivity) (by norm_num)
  have hp_w2b : ℓ2 ^ 20 ≤ 655405 / 1000000000 := le_trans (pow_le_pow_left₀ hℓ2_0 hℓ2_2 20) (by norm_num)
  have hm_w2b := mul_le_mul hw2_2 hp_w2b (by positivity) (by norm_num)
  linarith only [hm_s3, hm_C3, hm_B3, hm_w2b]

private lemma two_cell_coeff_bound_11 {ℓ3 s3 C3 B3 : ℝ}
    (hℓ3_1 : 1098612287 / 1000000000 ≤ ℓ3)
    (hℓ3_2 : ℓ3 ≤ 1098612289 / 1000000000)
    (hs3_2 : s3 ≤ 262087 / 151316)
    (hC3_1 : 298125447305 / 377736531657 ≤ C3)
    (hB3_1 : 1025701003 / 3339581949 ≤ B3) :
    s3 * ℓ3 ^ 23 / 25852016738884976640000 + -(C3 * ℓ3 ^ 24 / 620448401733239439360000) + -(B3 * ℓ3 ^ 22 / 1124000727777607680000) ≤ -159281288685 / 100000000000000000000000000000000 := by
  have hℓ3_0 : 0 ≤ ℓ3 := by linarith only [hℓ3_1]
  have hp_s3 : ℓ3 ^ 23 ≤ 8698060309 / 1000000000 := le_trans (pow_le_pow_left₀ hℓ3_0 hℓ3_2 23) (by norm_num)
  have hm_s3 := mul_le_mul hs3_2 hp_s3 (by positivity) (by norm_num)
  have hC3_0 : 0 ≤ C3 := by linarith only [hC3_1]
  have hp_C3 : (9555795421 / 1000000000 : ℝ) ≤ ℓ3 ^ 24 := le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hℓ3_1 24)
  have hm_C3 := mul_le_mul hC3_1 hp_C3 (by norm_num) hC3_0
  have hB3_0 : 0 ≤ B3 := by linarith only [hB3_1]
  have hp_B3 : (7917315285 / 1000000000 : ℝ) ≤ ℓ3 ^ 22 := le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hℓ3_1 22)
  have hm_B3 := mul_le_mul hB3_1 hp_B3 (by norm_num) hB3_0
  linarith only [hm_s3, hm_C3, hm_B3]

private lemma two_cell_coeff_bound_12 {ℓ3 s3 C3 B3 : ℝ}
    (hℓ3_1 : 1098612287 / 1000000000 ≤ ℓ3)
    (hℓ3_2 : ℓ3 ≤ 1098612289 / 1000000000)
    (hs3_1 : 191861 / 110771 ≤ s3)
    (hC3_2 : C3 ≤ 21085900441 / 26716655592)
    (hB3_2 : B3 ≤ 116015940154 / 377736531657) :
    -(s3 * ℓ3 ^ 25 / 15511210043330985984000000) + C3 * ℓ3 ^ 26 / 403291461126605635584000000 + B3 * ℓ3 ^ 24 / 620448401733239439360000 ≤ 35806175289 / 10000000000000000000000000000000000 := by
  have hℓ3_0 : 0 ≤ ℓ3 := by linarith only [hℓ3_1]
  have hs3_0 : 0 ≤ s3 := by linarith only [hs3_1]
  have hp_s3 : (10498114261 / 1000000000 : ℝ) ≤ ℓ3 ^ 25 := le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hℓ3_1 25)
  have hm_s3 := mul_le_mul hs3_1 hp_s3 (by norm_num) hs3_0
  have hp_C3 : ℓ3 ^ 26 ≤ 11533358006 / 1000000000 := le_trans (pow_le_pow_left₀ hℓ3_0 hℓ3_2 26) (by norm_num)
  have hm_C3 := mul_le_mul hC3_2 hp_C3 (by positivity) (by norm_num)
  have hp_B3 : ℓ3 ^ 24 ≤ 9555795953 / 1000000000 := le_trans (pow_le_pow_left₀ hℓ3_0 hℓ3_2 24) (by norm_num)
  have hm_B3 := mul_le_mul hB3_2 hp_B3 (by positivity) (by norm_num)
  linarith only [hm_s3, hm_C3, hm_B3]

private lemma two_cell_coeff_bound_13 {ℓ3 s3 B3 : ℝ}
    (hℓ3_1 : 1098612287 / 1000000000 ≤ ℓ3)
    (hℓ3_2 : ℓ3 ≤ 1098612289 / 1000000000)
    (hs3_2 : s3 ≤ 262087 / 151316)
    (hB3_1 : 1025701003 / 3339581949 ≤ B3) :
    s3 * ℓ3 ^ 27 / 10888869450418352160768000000 + -(B3 * ℓ3 ^ 26 / 403291461126605635584000000) ≤ -6767977296 / 1000000000000000000000000000000000000 := by
  have hℓ3_0 : 0 ≤ ℓ3 := by linarith only [hℓ3_1]
  have hp_s3 : ℓ3 ^ 27 ≤ 12670688839 / 1000000000 := le_trans (pow_le_pow_left₀ hℓ3_0 hℓ3_2 27) (by norm_num)
  have hm_s3 := mul_le_mul hs3_2 hp_s3 (by positivity) (by norm_num)
  have hB3_0 : 0 ≤ B3 := by linarith only [hB3_1]
  have hp_B3 : (11533357311 / 1000000000 : ℝ) ≤ ℓ3 ^ 26 := le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hℓ3_1 26)
  have hm_B3 := mul_le_mul hB3_1 hp_B3 (by norm_num) hB3_0
  linarith only [hm_s3, hm_B3]

private lemma two_cell_coeff_bound_14 {ℓ3 B3 : ℝ}
    (hℓ3_1 : 1098612287 / 1000000000 ≤ ℓ3)
    (hℓ3_2 : ℓ3 ≤ 1098612289 / 1000000000)
    (hB3_2 : B3 ≤ 116015940154 / 377736531657) :
    B3 * ℓ3 ^ 28 / 304888344611713860501504000000 ≤ 1402272872 / 100000000000000000000000000000000000000 := by
  have hℓ3_0 : 0 ≤ ℓ3 := by linarith only [hℓ3_1]
  have hp_B3 : ℓ3 ^ 28 ≤ 13920174474 / 1000000000 := le_trans (pow_le_pow_left₀ hℓ3_0 hℓ3_2 28) (by norm_num)
  have hm_B3 := mul_le_mul hB3_2 hp_B3 (by positivity) (by norm_num)
  linarith only [hm_B3]

private lemma two_cell_poly_mono_of_coeffs {c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 u : ℝ}
    (hc0 : c0 ≤ -56479903 / 10000000000)
    (hc1 : c1 ≤ -21487403336 / 1000000000000)
    (hc2 : c2 ≤ 435830757297 / 100000000000000)
    (hc3 : c3 ≤ -2382583391645 / 10000000000000000)
    (hc4 : c4 ≤ 6543111114386 / 1000000000000000000)
    (hc5 : c5 ≤ -10484330683375 / 100000000000000000000)
    (hc6 : c6 ≤ 10897053117410 / 10000000000000000000000)
    (hc7 : c7 ≤ -7933940492503 / 1000000000000000000000000)
    (hc8 : c8 ≤ 4277979372642 / 100000000000000000000000000)
    (hc9 : c9 ≤ -1779912971139 / 10000000000000000000000000000)
    (hc10 : c10 ≤ 589557683797 / 1000000000000000000000000000000)
    (hc11 : c11 ≤ -159281288685 / 100000000000000000000000000000000)
    (hc12 : c12 ≤ 35806175289 / 10000000000000000000000000000000000)
    (hc13 : c13 ≤ -6767977296 / 1000000000000000000000000000000000000)
    (hc14 : c14 ≤ 1402272872 / 100000000000000000000000000000000000000)
    (hu_nonneg : 0 ≤ u) :
    u * (c0 + c1 * u ^ 1 + c2 * u ^ 2 + c3 * u ^ 3 + c4 * u ^ 4 + c5 * u ^ 5 + c6 * u ^ 6 + c7 * u ^ 7 + c8 * u ^ 8 + c9 * u ^ 9 + c10 * u ^ 10 + c11 * u ^ 11 + c12 * u ^ 12 + c13 * u ^ 13 + c14 * u ^ 14) - 1 / 2 ≤ u * ((-56479903 / 10000000000) + (-21487403336 / 1000000000000) * u ^ 1 + (435830757297 / 100000000000000) * u ^ 2 + (-2382583391645 / 10000000000000000) * u ^ 3 + (6543111114386 / 1000000000000000000) * u ^ 4 + (-10484330683375 / 100000000000000000000) * u ^ 5 + (10897053117410 / 10000000000000000000000) * u ^ 6 + (-7933940492503 / 1000000000000000000000000) * u ^ 7 + (4277979372642 / 100000000000000000000000000) * u ^ 8 + (-1779912971139 / 10000000000000000000000000000) * u ^ 9 + (589557683797 / 1000000000000000000000000000000) * u ^ 10 + (-159281288685 / 100000000000000000000000000000000) * u ^ 11 + (35806175289 / 10000000000000000000000000000000000) * u ^ 12 + (-6767977296 / 1000000000000000000000000000000000000) * u ^ 13 + (1402272872 / 100000000000000000000000000000000000000) * u ^ 14) - 1 / 2 := by
  have hm0 := mul_le_mul_of_nonneg_right hc0 hu_nonneg
  have hm1 := mul_le_mul_of_nonneg_right hc1 (sq_nonneg u)
  have hm2 := mul_le_mul_of_nonneg_right hc2 (by positivity : 0 ≤ u ^ 3)
  have hm3 := mul_le_mul_of_nonneg_right hc3 (by positivity : 0 ≤ u ^ 4)
  have hm4 := mul_le_mul_of_nonneg_right hc4 (by positivity : 0 ≤ u ^ 5)
  have hm5 := mul_le_mul_of_nonneg_right hc5 (by positivity : 0 ≤ u ^ 6)
  have hm6 := mul_le_mul_of_nonneg_right hc6 (by positivity : 0 ≤ u ^ 7)
  have hm7 := mul_le_mul_of_nonneg_right hc7 (by positivity : 0 ≤ u ^ 8)
  have hm8 := mul_le_mul_of_nonneg_right hc8 (by positivity : 0 ≤ u ^ 9)
  have hm9 := mul_le_mul_of_nonneg_right hc9 (by positivity : 0 ≤ u ^ 10)
  have hm10 := mul_le_mul_of_nonneg_right hc10 (by positivity : 0 ≤ u ^ 11)
  have hm11 := mul_le_mul_of_nonneg_right hc11 (by positivity : 0 ≤ u ^ 12)
  have hm12 := mul_le_mul_of_nonneg_right hc12 (by positivity : 0 ≤ u ^ 13)
  have hm13 := mul_le_mul_of_nonneg_right hc13 (by positivity : 0 ≤ u ^ 14)
  have hm14 := mul_le_mul_of_nonneg_right hc14 (by positivity : 0 ≤ u ^ 15)
  have hexp1 : u * (c0 + c1 * u ^ 1 + c2 * u ^ 2 + c3 * u ^ 3 + c4 * u ^ 4 + c5 * u ^ 5 + c6 * u ^ 6 + c7 * u ^ 7 + c8 * u ^ 8 + c9 * u ^ 9 + c10 * u ^ 10 + c11 * u ^ 11 + c12 * u ^ 12 + c13 * u ^ 13 + c14 * u ^ 14) - 1 / 2 = c0 * u + c1 * u ^ 2 + c2 * u ^ 3 + c3 * u ^ 4 + c4 * u ^ 5 + c5 * u ^ 6 + c6 * u ^ 7 + c7 * u ^ 8 + c8 * u ^ 9 + c9 * u ^ 10 + c10 * u ^ 11 + c11 * u ^ 12 + c12 * u ^ 13 + c13 * u ^ 14 + c14 * u ^ 15 - 1 / 2 := by ring
  have hexp2 : u * ((-56479903 / 10000000000) + (-21487403336 / 1000000000000) * u ^ 1 + (435830757297 / 100000000000000) * u ^ 2 + (-2382583391645 / 10000000000000000) * u ^ 3 + (6543111114386 / 1000000000000000000) * u ^ 4 + (-10484330683375 / 100000000000000000000) * u ^ 5 + (10897053117410 / 10000000000000000000000) * u ^ 6 + (-7933940492503 / 1000000000000000000000000) * u ^ 7 + (4277979372642 / 100000000000000000000000000) * u ^ 8 + (-1779912971139 / 10000000000000000000000000000) * u ^ 9 + (589557683797 / 1000000000000000000000000000000) * u ^ 10 + (-159281288685 / 100000000000000000000000000000000) * u ^ 11 + (35806175289 / 10000000000000000000000000000000000) * u ^ 12 + (-6767977296 / 1000000000000000000000000000000000000) * u ^ 13 + (1402272872 / 100000000000000000000000000000000000000) * u ^ 14) - 1 / 2 = (-56479903 / 10000000000) * u + (-21487403336 / 1000000000000) * u ^ 2 + (435830757297 / 100000000000000) * u ^ 3 + (-2382583391645 / 10000000000000000) * u ^ 4 + (6543111114386 / 1000000000000000000) * u ^ 5 + (-10484330683375 / 100000000000000000000) * u ^ 6 + (10897053117410 / 10000000000000000000000) * u ^ 7 + (-7933940492503 / 1000000000000000000000000) * u ^ 8 + (4277979372642 / 100000000000000000000000000) * u ^ 9 + (-1779912971139 / 10000000000000000000000000000) * u ^ 10 + (589557683797 / 1000000000000000000000000000000) * u ^ 11 + (-159281288685 / 100000000000000000000000000000000) * u ^ 12 + (35806175289 / 10000000000000000000000000000000000) * u ^ 13 + (-6767977296 / 1000000000000000000000000000000000000) * u ^ 14 + (1402272872 / 100000000000000000000000000000000000000) * u ^ 15 - 1 / 2 := by ring
  linarith only [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hexp1, hexp2]


/-- Degree-15 Bernstein positivity certificate on `[0, 18]`. -/
lemma two_cell_bernstein_iv0 {u : ℝ} (hA : (0 : ℝ) ≤ u) (hB : u ≤ 18) :
    u * ((-56479903 / 10000000000) + (-21487403336 / 1000000000000) * u ^ 1 + (435830757297 / 100000000000000) * u ^ 2 + (-2382583391645 / 10000000000000000) * u ^ 3 + (6543111114386 / 1000000000000000000) * u ^ 4 + (-10484330683375 / 100000000000000000000) * u ^ 5 + (10897053117410 / 10000000000000000000000) * u ^ 6 + (-7933940492503 / 1000000000000000000000000) * u ^ 7 + (4277979372642 / 100000000000000000000000000) * u ^ 8 + (-1779912971139 / 10000000000000000000000000000) * u ^ 9 + (589557683797 / 1000000000000000000000000000000) * u ^ 10 + (-159281288685 / 100000000000000000000000000000000) * u ^ 11 + (35806175289 / 10000000000000000000000000000000000) * u ^ 12 + (-6767977296 / 1000000000000000000000000000000000000) * u ^ 13 + (1402272872 / 100000000000000000000000000000000000000) * u ^ 14) - 1 / 2 ≤ ((41 / 2880) * u - 19 / 144) * (1 / 4 + u) := by
  have h1 : 0 ≤ u - 0 := by linarith
  have h2 : 0 ≤ 18 - u := by linarith
  have hpos : (0 : ℝ) ≤ (269 / 3886064995091016056832) * 1 * (18 - u) ^ 15 +
      (71939019881 / 101199609247161876480000000000) * (u - 0) * (18 - u) ^ 14 +
      (5565196044337 / 1264995115589523456000000000000) * (u - 0) ^ 2 * (18 - u) ^ 13 +
      (15355935915920483 / 758997069353714073600000000000000) * (u - 0) ^ 3 * (18 - u) ^ 12 +
      (171038478041897027 / 2529990231179046912000000000000000) * (u - 0) ^ 4 * (18 - u) ^ 11 +
      (25463447962736218127 / 158124389448690432000000000000000000) * (u - 0) ^ 5 * (18 - u) ^ 10 +
      (208554958531840436119 / 758997069353714073600000000000000000) * (u - 0) ^ 6 * (18 - u) ^ 9 +
      (8934648461759398908923 / 26354064908115072000000000000000000000) * (u - 0) ^ 7 * (18 - u) ^ 8 +
      (7996803389166322229366663 / 26354064908115072000000000000000000000000) * (u - 0) ^ 8 * (18 - u) ^ 7 +
      (18115308760867035703093211 / 92651009442592050000000000000000000000000) * (u - 0) ^ 9 * (18 - u) ^ 6 +
      (17529515617611084156151386517 / 197655486810863040000000000000000000000000000) * (u - 0) ^ 10 * (18 - u) ^ 5 +
      (267930733727832764123894538131 / 9882774340543152000000000000000000000000000000) * (u - 0) ^ 11 * (18 - u) ^ 4 +
      (1539722671112890344050114602193 / 296483230216294560000000000000000000000000000000) * (u - 0) ^ 12 * (18 - u) ^ 3 +
      (14299387837929861292125469447007 / 24706935851357880000000000000000000000000000000000) * (u - 0) ^ 13 * (18 - u) ^ 2 +
      (7795257012174905587408237904321 / 154418349070986750000000000000000000000000000000000) * (u - 0) ^ 14 * (18 - u) +
      (278936761410465158614462755737587 / 46325504721296025000000000000000000000000000000000000) * (u - 0) ^ 15 * 1 := by positivity
  have hid : ((41 / 2880) * u - 19 / 144) * (1 / 4 + u) - (u * ((-56479903 / 10000000000) + (-21487403336 / 1000000000000) * u ^ 1 + (435830757297 / 100000000000000) * u ^ 2 + (-2382583391645 / 10000000000000000) * u ^ 3 + (6543111114386 / 1000000000000000000) * u ^ 4 + (-10484330683375 / 100000000000000000000) * u ^ 5 + (10897053117410 / 10000000000000000000000) * u ^ 6 + (-7933940492503 / 1000000000000000000000000) * u ^ 7 + (4277979372642 / 100000000000000000000000000) * u ^ 8 + (-1779912971139 / 10000000000000000000000000000) * u ^ 9 + (589557683797 / 1000000000000000000000000000000) * u ^ 10 + (-159281288685 / 100000000000000000000000000000000) * u ^ 11 + (35806175289 / 10000000000000000000000000000000000) * u ^ 12 + (-6767977296 / 1000000000000000000000000000000000000) * u ^ 13 + (1402272872 / 100000000000000000000000000000000000000) * u ^ 14) - 1 / 2) = (269 / 3886064995091016056832) * 1 * (18 - u) ^ 15 +
      (71939019881 / 101199609247161876480000000000) * (u - 0) * (18 - u) ^ 14 +
      (5565196044337 / 1264995115589523456000000000000) * (u - 0) ^ 2 * (18 - u) ^ 13 +
      (15355935915920483 / 758997069353714073600000000000000) * (u - 0) ^ 3 * (18 - u) ^ 12 +
      (171038478041897027 / 2529990231179046912000000000000000) * (u - 0) ^ 4 * (18 - u) ^ 11 +
      (25463447962736218127 / 158124389448690432000000000000000000) * (u - 0) ^ 5 * (18 - u) ^ 10 +
      (208554958531840436119 / 758997069353714073600000000000000000) * (u - 0) ^ 6 * (18 - u) ^ 9 +
      (8934648461759398908923 / 26354064908115072000000000000000000000) * (u - 0) ^ 7 * (18 - u) ^ 8 +
      (7996803389166322229366663 / 26354064908115072000000000000000000000000) * (u - 0) ^ 8 * (18 - u) ^ 7 +
      (18115308760867035703093211 / 92651009442592050000000000000000000000000) * (u - 0) ^ 9 * (18 - u) ^ 6 +
      (17529515617611084156151386517 / 197655486810863040000000000000000000000000000) * (u - 0) ^ 10 * (18 - u) ^ 5 +
      (267930733727832764123894538131 / 9882774340543152000000000000000000000000000000) * (u - 0) ^ 11 * (18 - u) ^ 4 +
      (1539722671112890344050114602193 / 296483230216294560000000000000000000000000000000) * (u - 0) ^ 12 * (18 - u) ^ 3 +
      (14299387837929861292125469447007 / 24706935851357880000000000000000000000000000000000) * (u - 0) ^ 13 * (18 - u) ^ 2 +
      (7795257012174905587408237904321 / 154418349070986750000000000000000000000000000000000) * (u - 0) ^ 14 * (18 - u) +
      (278936761410465158614462755737587 / 46325504721296025000000000000000000000000000000000000) * (u - 0) ^ 15 * 1 := by ring
  linarith

/-- Degree-15 Bernstein positivity certificate on `[18, 90]`. -/
lemma two_cell_bernstein_iv1 {u : ℝ} (hA : (18 : ℝ) ≤ u) (hB : u ≤ 90) :
    u * ((-56479903 / 10000000000) + (-21487403336 / 1000000000000) * u ^ 1 + (435830757297 / 100000000000000) * u ^ 2 + (-2382583391645 / 10000000000000000) * u ^ 3 + (6543111114386 / 1000000000000000000) * u ^ 4 + (-10484330683375 / 100000000000000000000) * u ^ 5 + (10897053117410 / 10000000000000000000000) * u ^ 6 + (-7933940492503 / 1000000000000000000000000) * u ^ 7 + (4277979372642 / 100000000000000000000000000) * u ^ 8 + (-1779912971139 / 10000000000000000000000000000) * u ^ 9 + (589557683797 / 1000000000000000000000000000000) * u ^ 10 + (-159281288685 / 100000000000000000000000000000000) * u ^ 11 + (35806175289 / 10000000000000000000000000000000000) * u ^ 12 + (-6767977296 / 1000000000000000000000000000000000000) * u ^ 13 + (1402272872 / 100000000000000000000000000000000000000) * u ^ 14) - 1 / 2 ≤ ((41 / 2880) * u - 19 / 144) * (1 / 4 + u) := by
  have h1 : 0 ≤ u - 18 := by linarith
  have h2 : 0 ≤ 90 - u := by linarith
  have hpos : (0 : ℝ) ≤ (278936761410465158614462755737587 / 49741631937165005527449600000000000000000000000000000000000000) * 1 * (90 - u) ^ 15 +
      (154212649215666669215930949268451 / 663221759162200073699328000000000000000000000000000000000000) * (u - 18) * (90 - u) ^ 14 +
      (270074157236093232418366311071153 / 26528870366488002947973120000000000000000000000000000000000) * (u - 18) ^ 2 * (90 - u) ^ 13 +
      (11312089975707263554746558645620129 / 79586611099464008843919360000000000000000000000000000000000) * (u - 18) ^ 3 * (90 - u) ^ 12 +
      (4964731524065625544364628907094593 / 5305774073297600589594624000000000000000000000000000000000) * (u - 18) ^ 4 * (90 - u) ^ 11 +
      (18386349770497215659119585600259707 / 5305774073297600589594624000000000000000000000000000000000) * (u - 18) ^ 5 * (90 - u) ^ 10 +
      (5119278448944355764788692980654971 / 636692888795712070751354880000000000000000000000000000000) * (u - 18) ^ 6 * (90 - u) ^ 9 +
      (35172644269254369513825673070009 / 2829746172425386981117132800000000000000000000000000000) * (u - 18) ^ 7 * (90 - u) ^ 8 +
      (37376638776763806089875865559677 / 2829746172425386981117132800000000000000000000000000000) * (u - 18) ^ 8 * (90 - u) ^ 7 +
      (49574480204838011114276389777243 / 5093543110365696566010839040000000000000000000000000000) * (u - 18) ^ 9 * (90 - u) ^ 6 +
      (8340262601562031401420267996827 / 1697847703455232188670279680000000000000000000000000000) * (u - 18) ^ 10 * (90 - u) ^ 5 +
      (111122535588917071512903635681 / 67913908138209287546811187200000000000000000000000000) * (u - 18) ^ 11 * (90 - u) ^ 4 +
      (2729967068694846383343676877 / 8149668976585114505617342464000000000000000000000000) * (u - 18) ^ 12 * (90 - u) ^ 3 +
      (103935413996386424001099413 / 2716556325528371501872447488000000000000000000000000) * (u - 18) ^ 13 * (90 - u) ^ 2 +
      (1545530453168972178952963 / 543311265105674300374489497600000000000000000000000) * (u - 18) ^ 14 * (90 - u) +
      (407919428965949397588947 / 1629933795317022901123468492800000000000000000000000) * (u - 18) ^ 15 * 1 := by positivity
  have hid : ((41 / 2880) * u - 19 / 144) * (1 / 4 + u) - (u * ((-56479903 / 10000000000) + (-21487403336 / 1000000000000) * u ^ 1 + (435830757297 / 100000000000000) * u ^ 2 + (-2382583391645 / 10000000000000000) * u ^ 3 + (6543111114386 / 1000000000000000000) * u ^ 4 + (-10484330683375 / 100000000000000000000) * u ^ 5 + (10897053117410 / 10000000000000000000000) * u ^ 6 + (-7933940492503 / 1000000000000000000000000) * u ^ 7 + (4277979372642 / 100000000000000000000000000) * u ^ 8 + (-1779912971139 / 10000000000000000000000000000) * u ^ 9 + (589557683797 / 1000000000000000000000000000000) * u ^ 10 + (-159281288685 / 100000000000000000000000000000000) * u ^ 11 + (35806175289 / 10000000000000000000000000000000000) * u ^ 12 + (-6767977296 / 1000000000000000000000000000000000000) * u ^ 13 + (1402272872 / 100000000000000000000000000000000000000) * u ^ 14) - 1 / 2) = (278936761410465158614462755737587 / 49741631937165005527449600000000000000000000000000000000000000) * 1 * (90 - u) ^ 15 +
      (154212649215666669215930949268451 / 663221759162200073699328000000000000000000000000000000000000) * (u - 18) * (90 - u) ^ 14 +
      (270074157236093232418366311071153 / 26528870366488002947973120000000000000000000000000000000000) * (u - 18) ^ 2 * (90 - u) ^ 13 +
      (11312089975707263554746558645620129 / 79586611099464008843919360000000000000000000000000000000000) * (u - 18) ^ 3 * (90 - u) ^ 12 +
      (4964731524065625544364628907094593 / 5305774073297600589594624000000000000000000000000000000000) * (u - 18) ^ 4 * (90 - u) ^ 11 +
      (18386349770497215659119585600259707 / 5305774073297600589594624000000000000000000000000000000000) * (u - 18) ^ 5 * (90 - u) ^ 10 +
      (5119278448944355764788692980654971 / 636692888795712070751354880000000000000000000000000000000) * (u - 18) ^ 6 * (90 - u) ^ 9 +
      (35172644269254369513825673070009 / 2829746172425386981117132800000000000000000000000000000) * (u - 18) ^ 7 * (90 - u) ^ 8 +
      (37376638776763806089875865559677 / 2829746172425386981117132800000000000000000000000000000) * (u - 18) ^ 8 * (90 - u) ^ 7 +
      (49574480204838011114276389777243 / 5093543110365696566010839040000000000000000000000000000) * (u - 18) ^ 9 * (90 - u) ^ 6 +
      (8340262601562031401420267996827 / 1697847703455232188670279680000000000000000000000000000) * (u - 18) ^ 10 * (90 - u) ^ 5 +
      (111122535588917071512903635681 / 67913908138209287546811187200000000000000000000000000) * (u - 18) ^ 11 * (90 - u) ^ 4 +
      (2729967068694846383343676877 / 8149668976585114505617342464000000000000000000000000) * (u - 18) ^ 12 * (90 - u) ^ 3 +
      (103935413996386424001099413 / 2716556325528371501872447488000000000000000000000000) * (u - 18) ^ 13 * (90 - u) ^ 2 +
      (1545530453168972178952963 / 543311265105674300374489497600000000000000000000000) * (u - 18) ^ 14 * (90 - u) +
      (407919428965949397588947 / 1629933795317022901123468492800000000000000000000000) * (u - 18) ^ 15 * 1 := by ring
  linarith

/-- Degree-15 Bernstein positivity certificate on `[90, 116]`. -/
lemma two_cell_bernstein_iv2 {u : ℝ} (hA : (90 : ℝ) ≤ u) (hB : u ≤ 116) :
    u * ((-56479903 / 10000000000) + (-21487403336 / 1000000000000) * u ^ 1 + (435830757297 / 100000000000000) * u ^ 2 + (-2382583391645 / 10000000000000000) * u ^ 3 + (6543111114386 / 1000000000000000000) * u ^ 4 + (-10484330683375 / 100000000000000000000) * u ^ 5 + (10897053117410 / 10000000000000000000000) * u ^ 6 + (-7933940492503 / 1000000000000000000000000) * u ^ 7 + (4277979372642 / 100000000000000000000000000) * u ^ 8 + (-1779912971139 / 10000000000000000000000000000) * u ^ 9 + (589557683797 / 1000000000000000000000000000000) * u ^ 10 + (-159281288685 / 100000000000000000000000000000000) * u ^ 11 + (35806175289 / 10000000000000000000000000000000000) * u ^ 12 + (-6767977296 / 1000000000000000000000000000000000000) * u ^ 13 + (1402272872 / 100000000000000000000000000000000000000) * u ^ 14) - 1 / 2 ≤ ((41 / 2880) * u - 19 / 144) * (1 / 4 + u) := by
  have h1 : 0 ≤ u - 90 := by linarith
  have h2 : 0 ≤ 116 - u := by linarith
  have hpos : (0 : ℝ) ≤ (407919428965949397588947 / 377383352014288333209600000000000000000000000) * 1 * (116 - u) ^ 15 +
      (369668352803060018902331 / 20965741778571574067200000000000000000000000) * (u - 90) * (116 - u) ^ 14 +
      (277887565102668111871780061 / 1886916760071441666048000000000000000000000000) * (u - 90) ^ 2 * (116 - u) ^ 13 +
      (14612041856554601781831137 / 18143430385302323712000000000000000000000000) * (u - 90) ^ 3 * (116 - u) ^ 12 +
      (941343650129470348006214413 / 302390506421705395200000000000000000000000000) * (u - 90) ^ 4 * (116 - u) ^ 11 +
      (3118483208982044393796380489 / 354363874712936010000000000000000000000000000) * (u - 90) ^ 5 * (116 - u) ^ 10 +
      (182652579046635067944566059 / 9843440964248222500000000000000000000000000) * (u - 90) ^ 6 * (116 - u) ^ 9 +
      (46502963299193202233109797471 / 1574950554279715600000000000000000000000000000) * (u - 90) ^ 7 * (116 - u) ^ 8 +
      (42084931814579913468814280017 / 1181212915709786700000000000000000000000000000) * (u - 90) ^ 8 * (116 - u) ^ 7 +
      (2881188585439620189591060584233 / 88590968678234002500000000000000000000000000000) * (u - 90) ^ 9 * (116 - u) ^ 6 +
      (2732804124553215970995087433627 / 123043012053102781250000000000000000000000000000) * (u - 90) ^ 10 * (116 - u) ^ 5 +
      (1535440480606419462480032398463 / 138423388559740628906250000000000000000000000000) * (u - 90) ^ 11 * (116 - u) ^ 4 +
      (2692028790408134227560814433621 / 692116942798703144531250000000000000000000000000) * (u - 90) ^ 12 * (116 - u) ^ 3 +
      (1334676745798176563152511049037 / 1499586709397190146484375000000000000000000000000) * (u - 90) ^ 13 * (116 - u) ^ 2 +
      (3232921261974152097673789345343 / 28117250801197315246582031250000000000000000000000) * (u - 90) ^ 14 * (116 - u) +
      (2715490651669403233426630450991 / 468620846686621920776367187500000000000000000000000) * (u - 90) ^ 15 * 1 := by positivity
  have hid : ((41 / 2880) * u - 19 / 144) * (1 / 4 + u) - (u * ((-56479903 / 10000000000) + (-21487403336 / 1000000000000) * u ^ 1 + (435830757297 / 100000000000000) * u ^ 2 + (-2382583391645 / 10000000000000000) * u ^ 3 + (6543111114386 / 1000000000000000000) * u ^ 4 + (-10484330683375 / 100000000000000000000) * u ^ 5 + (10897053117410 / 10000000000000000000000) * u ^ 6 + (-7933940492503 / 1000000000000000000000000) * u ^ 7 + (4277979372642 / 100000000000000000000000000) * u ^ 8 + (-1779912971139 / 10000000000000000000000000000) * u ^ 9 + (589557683797 / 1000000000000000000000000000000) * u ^ 10 + (-159281288685 / 100000000000000000000000000000000) * u ^ 11 + (35806175289 / 10000000000000000000000000000000000) * u ^ 12 + (-6767977296 / 1000000000000000000000000000000000000) * u ^ 13 + (1402272872 / 100000000000000000000000000000000000000) * u ^ 14) - 1 / 2) = (407919428965949397588947 / 377383352014288333209600000000000000000000000) * 1 * (116 - u) ^ 15 +
      (369668352803060018902331 / 20965741778571574067200000000000000000000000) * (u - 90) * (116 - u) ^ 14 +
      (277887565102668111871780061 / 1886916760071441666048000000000000000000000000) * (u - 90) ^ 2 * (116 - u) ^ 13 +
      (14612041856554601781831137 / 18143430385302323712000000000000000000000000) * (u - 90) ^ 3 * (116 - u) ^ 12 +
      (941343650129470348006214413 / 302390506421705395200000000000000000000000000) * (u - 90) ^ 4 * (116 - u) ^ 11 +
      (3118483208982044393796380489 / 354363874712936010000000000000000000000000000) * (u - 90) ^ 5 * (116 - u) ^ 10 +
      (182652579046635067944566059 / 9843440964248222500000000000000000000000000) * (u - 90) ^ 6 * (116 - u) ^ 9 +
      (46502963299193202233109797471 / 1574950554279715600000000000000000000000000000) * (u - 90) ^ 7 * (116 - u) ^ 8 +
      (42084931814579913468814280017 / 1181212915709786700000000000000000000000000000) * (u - 90) ^ 8 * (116 - u) ^ 7 +
      (2881188585439620189591060584233 / 88590968678234002500000000000000000000000000000) * (u - 90) ^ 9 * (116 - u) ^ 6 +
      (2732804124553215970995087433627 / 123043012053102781250000000000000000000000000000) * (u - 90) ^ 10 * (116 - u) ^ 5 +
      (1535440480606419462480032398463 / 138423388559740628906250000000000000000000000000) * (u - 90) ^ 11 * (116 - u) ^ 4 +
      (2692028790408134227560814433621 / 692116942798703144531250000000000000000000000000) * (u - 90) ^ 12 * (116 - u) ^ 3 +
      (1334676745798176563152511049037 / 1499586709397190146484375000000000000000000000000) * (u - 90) ^ 13 * (116 - u) ^ 2 +
      (3232921261974152097673789345343 / 28117250801197315246582031250000000000000000000000) * (u - 90) ^ 14 * (116 - u) +
      (2715490651669403233426630450991 / 468620846686621920776367187500000000000000000000000) * (u - 90) ^ 15 * 1 := by ring
  linarith

/-- **Degree-28 Polynomial Taylor Bound for the Two-Cell + Resolvent Envelope (`0 ≤ u ≤ 116`)**. -/
theorem two_cell_taylor_poly_le_joint_resolvent {ℓ2 ℓ3 s2 s3 C3 B3 w2 u : ℝ}
    (hℓ2_1 : 693147179 / 1000000000 ≤ ℓ2) (hℓ2_2 : ℓ2 ≤ 693147181 / 1000000000)
    (hℓ3_1 : 1098612287 / 1000000000 ≤ ℓ3) (hℓ3_2 : ℓ3 ≤ 1098612289 / 1000000000)
    (hs2_1 : 1607521 / 1136689 ≤ s2) (hs2_2 : s2 ≤ 665857 / 470832)
    (hs3_low : 716035 / 413403 ≤ s3) (hs3_high : s3 ≤ 978122 / 564719)
    (hC3_def : C3 = s3 - (2 / 3) * s2)
    (hB3_def : B3 = (8 / 3) * s2 - 2 * s3)
    (hw2_def : w2 = 4 / 3 + 4 * s3 - (16 / 3) * s2)
    (hu_nonneg : 0 ≤ u) (hr : u ≤ 116) :
    u * ((2 * (s3 - 1) + -(s3 * ℓ3 ^ 1 / 1) + C3 * ℓ3 ^ 2 / 2 + -(w2 * ℓ2 ^ 2 / 8)) +
      (s3 * ℓ3 ^ 3 / 6 + -(C3 * ℓ3 ^ 4 / 24) + -(B3 * ℓ3 ^ 2 / 2) + w2 * ℓ2 ^ 4 / 96 + -(w2 * ℓ2 ^ 2 / 2)) * u ^ 1 +
      (-(s3 * ℓ3 ^ 5 / 120) + C3 * ℓ3 ^ 6 / 720 + B3 * ℓ3 ^ 4 / 24 + -(w2 * ℓ2 ^ 6 / 2880) + w2 * ℓ2 ^ 4 / 24) * u ^ 2 +
      (s3 * ℓ3 ^ 7 / 5040 + -(C3 * ℓ3 ^ 8 / 40320) + -(B3 * ℓ3 ^ 6 / 720) + w2 * ℓ2 ^ 8 / 161280 + -(w2 * ℓ2 ^ 6 / 720)) * u ^ 3 +
      (-(s3 * ℓ3 ^ 9 / 362880) + C3 * ℓ3 ^ 10 / 3628800 + B3 * ℓ3 ^ 8 / 40320 + -(w2 * ℓ2 ^ 10 / 14515200) + w2 * ℓ2 ^ 8 / 40320) * u ^ 4 +
      (s3 * ℓ3 ^ 11 / 39916800 + -(C3 * ℓ3 ^ 12 / 479001600) + -(B3 * ℓ3 ^ 10 / 3628800) + w2 * ℓ2 ^ 12 / 1916006400 + -(w2 * ℓ2 ^ 10 / 3628800)) * u ^ 5 +
      (-(s3 * ℓ3 ^ 13 / 6227020800) + C3 * ℓ3 ^ 14 / 87178291200 + B3 * ℓ3 ^ 12 / 479001600 + -(w2 * ℓ2 ^ 14 / 348713164800) + w2 * ℓ2 ^ 12 / 479001600) * u ^ 6 +
      (s3 * ℓ3 ^ 15 / 1307674368000 + -(C3 * ℓ3 ^ 16 / 20922789888000) + -(B3 * ℓ3 ^ 14 / 87178291200) + w2 * ℓ2 ^ 16 / 83691159552000 + -(w2 * ℓ2 ^ 14 / 87178291200)) * u ^ 7 +
      (-(s3 * ℓ3 ^ 17 / 355687428096000) + C3 * ℓ3 ^ 18 / 6402373705728000 + B3 * ℓ3 ^ 16 / 20922789888000 + -(w2 * ℓ2 ^ 18 / 25609494822912000) + w2 * ℓ2 ^ 16 / 20922789888000) * u ^ 8 +
      (s3 * ℓ3 ^ 19 / 121645100408832000 + -(C3 * ℓ3 ^ 20 / 2432902008176640000) + -(B3 * ℓ3 ^ 18 / 6402373705728000) + w2 * ℓ2 ^ 20 / 9731608032706560000 + -(w2 * ℓ2 ^ 18 / 6402373705728000)) * u ^ 9 +
      (-(s3 * ℓ3 ^ 21 / 51090942171709440000) + C3 * ℓ3 ^ 22 / 1124000727777607680000 + B3 * ℓ3 ^ 20 / 2432902008176640000 + w2 * ℓ2 ^ 20 / 2432902008176640000) * u ^ 10 +
      (s3 * ℓ3 ^ 23 / 25852016738884976640000 + -(C3 * ℓ3 ^ 24 / 620448401733239439360000) + -(B3 * ℓ3 ^ 22 / 1124000727777607680000)) * u ^ 11 +
      (-(s3 * ℓ3 ^ 25 / 15511210043330985984000000) + C3 * ℓ3 ^ 26 / 403291461126605635584000000 + B3 * ℓ3 ^ 24 / 620448401733239439360000) * u ^ 12 +
      (s3 * ℓ3 ^ 27 / 10888869450418352160768000000 + -(B3 * ℓ3 ^ 26 / 403291461126605635584000000)) * u ^ 13 +
      (B3 * ℓ3 ^ 28 / 304888344611713860501504000000) * u ^ 14) - 1 / 2 ≤ ((41 / 2880) * u - 19 / 144) * (1 / 4 + u) := by
  have hs3_1 : (191861 / 110771 : ℝ) ≤ s3 := by linarith only [hs3_low]
  have hs3_2 : s3 ≤ 262087 / 151316 := by linarith only [hs3_high]
  have hC3_1 : (298125447305 / 377736531657 : ℝ) ≤ C3 := by linarith only [hC3_def, hs2_2, hs3_low]
  have hC3_2 : C3 ≤ 21085900441 / 26716655592 := by linarith only [hC3_def, hs2_1, hs3_high]
  have hB3_1 : (1025701003 / 3339581949 : ℝ) ≤ B3 := by linarith only [hB3_def, hs2_1, hs3_high]
  have hB3_2 : B3 ≤ 116015940154 / 377736531657 := by linarith only [hB3_def, hs2_2, hs3_low]
  have hw2_1 : (90538942856 / 125912177219 : ℝ) ≤ w2 := by linarith only [hw2_def, hs2_2, hs3_low]
  have hw2_2 : w2 ≤ 2401373926 / 3339581949 := by linarith only [hw2_def, hs2_1, hs3_high]
  have hc0 := two_cell_coeff_bound_0 hℓ2_1 hℓ3_1 hℓ3_2 hs3_1 hs3_2 hC3_2 hw2_1
  have hc1 := two_cell_coeff_bound_1 hℓ2_1 hℓ2_2 hℓ3_1 hℓ3_2 hs3_2 hC3_1 hB3_1 hw2_1 hw2_2
  have hc2 := two_cell_coeff_bound_2 hℓ2_1 hℓ2_2 hℓ3_1 hℓ3_2 hs3_1 hC3_2 hB3_2 hw2_1 hw2_2
  have hc3 := two_cell_coeff_bound_3 hℓ2_1 hℓ2_2 hℓ3_1 hℓ3_2 hs3_2 hC3_1 hB3_1 hw2_1 hw2_2
  have hc4 := two_cell_coeff_bound_4 hℓ2_1 hℓ2_2 hℓ3_1 hℓ3_2 hs3_1 hC3_2 hB3_2 hw2_1 hw2_2
  have hc5 := two_cell_coeff_bound_5 hℓ2_1 hℓ2_2 hℓ3_1 hℓ3_2 hs3_2 hC3_1 hB3_1 hw2_1 hw2_2
  have hc6 := two_cell_coeff_bound_6 hℓ2_1 hℓ2_2 hℓ3_1 hℓ3_2 hs3_1 hC3_2 hB3_2 hw2_1 hw2_2
  have hc7 := two_cell_coeff_bound_7 hℓ2_1 hℓ2_2 hℓ3_1 hℓ3_2 hs3_2 hC3_1 hB3_1 hw2_1 hw2_2
  have hc8 := two_cell_coeff_bound_8 hℓ2_1 hℓ2_2 hℓ3_1 hℓ3_2 hs3_1 hC3_2 hB3_2 hw2_1 hw2_2
  have hc9 := two_cell_coeff_bound_9 hℓ2_1 hℓ2_2 hℓ3_1 hℓ3_2 hs3_2 hC3_1 hB3_1 hw2_1 hw2_2
  have hc10 := two_cell_coeff_bound_10 hℓ2_1 hℓ2_2 hℓ3_1 hℓ3_2 hs3_1 hC3_2 hB3_2 hw2_2
  have hc11 := two_cell_coeff_bound_11 hℓ3_1 hℓ3_2 hs3_2 hC3_1 hB3_1
  have hc12 := two_cell_coeff_bound_12 hℓ3_1 hℓ3_2 hs3_1 hC3_2 hB3_2
  have hc13 := two_cell_coeff_bound_13 hℓ3_1 hℓ3_2 hs3_2 hB3_1
  have hc14 := two_cell_coeff_bound_14 hℓ3_1 hℓ3_2 hB3_2
  have hmono := two_cell_poly_mono_of_coeffs hc0 hc1 hc2 hc3 hc4 hc5 hc6 hc7 hc8 hc9 hc10 hc11 hc12 hc13 hc14 hu_nonneg
  rcases le_total u 18 with h18 | h18
  · exact hmono.trans (two_cell_bernstein_iv0 hu_nonneg h18)
  · rcases le_total u 90 with h90 | h90
    · exact hmono.trans (two_cell_bernstein_iv1 h18 h90)
    · exact hmono.trans (two_cell_bernstein_iv2 h90 hr)

private theorem mul_sin_ge_scaled_taylor_degree_twenty_eight (r ℓ3 : ℝ) (hℓ3_nn : 0 ≤ ℓ3) :
    r ^ 2 * (ℓ3 - ℓ3 ^ 3 * (r ^ 2) ^ 1 / 6 + ℓ3 ^ 5 * (r ^ 2) ^ 2 / 120 - ℓ3 ^ 7 * (r ^ 2) ^ 3 / 5040 + ℓ3 ^ 9 * (r ^ 2) ^ 4 / 362880 - ℓ3 ^ 11 * (r ^ 2) ^ 5 / 39916800 + ℓ3 ^ 13 * (r ^ 2) ^ 6 / 6227020800 - ℓ3 ^ 15 * (r ^ 2) ^ 7 / 1307674368000 + ℓ3 ^ 17 * (r ^ 2) ^ 8 / 355687428096000 - ℓ3 ^ 19 * (r ^ 2) ^ 9 / 121645100408832000 + ℓ3 ^ 21 * (r ^ 2) ^ 10 / 51090942171709440000 - ℓ3 ^ 23 * (r ^ 2) ^ 11 / 25852016738884976640000 + ℓ3 ^ 25 * (r ^ 2) ^ 12 / 15511210043330985984000000 - ℓ3 ^ 27 * (r ^ 2) ^ 13 / 10888869450418352160768000000) ≤ r * Real.sin (r * ℓ3) := by
  rcases le_total 0 r with hr | hr
  · have h := mul_le_mul_of_nonneg_left
      (taylor_degree_twenty_seven_le_sin_of_nonneg (mul_nonneg hr hℓ3_nn)) hr
    have hid :
        r * ((r * ℓ3) - (r * ℓ3) ^ 3 / 6 + (r * ℓ3) ^ 5 / 120 - (r * ℓ3) ^ 7 / 5040 + (r * ℓ3) ^ 9 / 362880 - (r * ℓ3) ^ 11 / 39916800 + (r * ℓ3) ^ 13 / 6227020800 - (r * ℓ3) ^ 15 / 1307674368000 + (r * ℓ3) ^ 17 / 355687428096000 - (r * ℓ3) ^ 19 / 121645100408832000 + (r * ℓ3) ^ 21 / 51090942171709440000 - (r * ℓ3) ^ 23 / 25852016738884976640000 + (r * ℓ3) ^ 25 / 15511210043330985984000000 - (r * ℓ3) ^ 27 / 10888869450418352160768000000) =
        r ^ 2 * (ℓ3 - ℓ3 ^ 3 * (r ^ 2) ^ 1 / 6 + ℓ3 ^ 5 * (r ^ 2) ^ 2 / 120 - ℓ3 ^ 7 * (r ^ 2) ^ 3 / 5040 + ℓ3 ^ 9 * (r ^ 2) ^ 4 / 362880 - ℓ3 ^ 11 * (r ^ 2) ^ 5 / 39916800 + ℓ3 ^ 13 * (r ^ 2) ^ 6 / 6227020800 - ℓ3 ^ 15 * (r ^ 2) ^ 7 / 1307674368000 + ℓ3 ^ 17 * (r ^ 2) ^ 8 / 355687428096000 - ℓ3 ^ 19 * (r ^ 2) ^ 9 / 121645100408832000 + ℓ3 ^ 21 * (r ^ 2) ^ 10 / 51090942171709440000 - ℓ3 ^ 23 * (r ^ 2) ^ 11 / 25852016738884976640000 + ℓ3 ^ 25 * (r ^ 2) ^ 12 / 15511210043330985984000000 - ℓ3 ^ 27 * (r ^ 2) ^ 13 / 10888869450418352160768000000) := by ring
    linarith
  · have hr_neg : 0 ≤ -r := neg_nonneg.mpr hr
    have h := mul_le_mul_of_nonneg_left
      (taylor_degree_twenty_seven_le_sin_of_nonneg (mul_nonneg hr_neg hℓ3_nn)) hr_neg
    rw [show -r * ℓ3 = -(r * ℓ3) by ring, Real.sin_neg] at h
    have hid :
        (-r) * ((-(r * ℓ3)) - (-(r * ℓ3)) ^ 3 / 6 + (-(r * ℓ3)) ^ 5 / 120 - (-(r * ℓ3)) ^ 7 / 5040 + (-(r * ℓ3)) ^ 9 / 362880 - (-(r * ℓ3)) ^ 11 / 39916800 + (-(r * ℓ3)) ^ 13 / 6227020800 - (-(r * ℓ3)) ^ 15 / 1307674368000 + (-(r * ℓ3)) ^ 17 / 355687428096000 - (-(r * ℓ3)) ^ 19 / 121645100408832000 + (-(r * ℓ3)) ^ 21 / 51090942171709440000 - (-(r * ℓ3)) ^ 23 / 25852016738884976640000 + (-(r * ℓ3)) ^ 25 / 15511210043330985984000000 - (-(r * ℓ3)) ^ 27 / 10888869450418352160768000000) =
        r ^ 2 * (ℓ3 - ℓ3 ^ 3 * (r ^ 2) ^ 1 / 6 + ℓ3 ^ 5 * (r ^ 2) ^ 2 / 120 - ℓ3 ^ 7 * (r ^ 2) ^ 3 / 5040 + ℓ3 ^ 9 * (r ^ 2) ^ 4 / 362880 - ℓ3 ^ 11 * (r ^ 2) ^ 5 / 39916800 + ℓ3 ^ 13 * (r ^ 2) ^ 6 / 6227020800 - ℓ3 ^ 15 * (r ^ 2) ^ 7 / 1307674368000 + ℓ3 ^ 17 * (r ^ 2) ^ 8 / 355687428096000 - ℓ3 ^ 19 * (r ^ 2) ^ 9 / 121645100408832000 + ℓ3 ^ 21 * (r ^ 2) ^ 10 / 51090942171709440000 - ℓ3 ^ 23 * (r ^ 2) ^ 11 / 25852016738884976640000 + ℓ3 ^ 25 * (r ^ 2) ^ 12 / 15511210043330985984000000 - ℓ3 ^ 27 * (r ^ 2) ^ 13 / 10888869450418352160768000000) := by ring
    have hid2 : (-r) * -Real.sin (r * ℓ3) = r * Real.sin (r * ℓ3) := by ring
    linarith

private theorem two_cell_taylor_grouping_eq (r s3 ℓ3 ℓ2 C3 B3 w2 : ℝ) :
    -1 / 2 + 2 * (s3 - 1) * r ^ 2 -
      s3 * (r ^ 2 * (ℓ3 - ℓ3 ^ 3 * (r ^ 2) ^ 1 / 6 + ℓ3 ^ 5 * (r ^ 2) ^ 2 / 120 - ℓ3 ^ 7 * (r ^ 2) ^ 3 / 5040 + ℓ3 ^ 9 * (r ^ 2) ^ 4 / 362880 - ℓ3 ^ 11 * (r ^ 2) ^ 5 / 39916800 + ℓ3 ^ 13 * (r ^ 2) ^ 6 / 6227020800 - ℓ3 ^ 15 * (r ^ 2) ^ 7 / 1307674368000 + ℓ3 ^ 17 * (r ^ 2) ^ 8 / 355687428096000 - ℓ3 ^ 19 * (r ^ 2) ^ 9 / 121645100408832000 + ℓ3 ^ 21 * (r ^ 2) ^ 10 / 51090942171709440000 - ℓ3 ^ 23 * (r ^ 2) ^ 11 / 25852016738884976640000 + ℓ3 ^ 25 * (r ^ 2) ^ 12 / 15511210043330985984000000 - ℓ3 ^ 27 * (r ^ 2) ^ 13 / 10888869450418352160768000000)) +
      C3 * ((r * ℓ3) ^ 2 / 2 - (r * ℓ3) ^ 4 / 24 + (r * ℓ3) ^ 6 / 720 - (r * ℓ3) ^ 8 / 40320 + (r * ℓ3) ^ 10 / 3628800 - (r * ℓ3) ^ 12 / 479001600 + (r * ℓ3) ^ 14 / 87178291200 - (r * ℓ3) ^ 16 / 20922789888000 + (r * ℓ3) ^ 18 / 6402373705728000 - (r * ℓ3) ^ 20 / 2432902008176640000 + (r * ℓ3) ^ 22 / 1124000727777607680000 - (r * ℓ3) ^ 24 / 620448401733239439360000 + (r * ℓ3) ^ 26 / 403291461126605635584000000) -
      (B3 * r ^ 2) * ((r * ℓ3) ^ 2 / 2 - (r * ℓ3) ^ 4 / 24 + (r * ℓ3) ^ 6 / 720 - (r * ℓ3) ^ 8 / 40320 + (r * ℓ3) ^ 10 / 3628800 - (r * ℓ3) ^ 12 / 479001600 + (r * ℓ3) ^ 14 / 87178291200 - (r * ℓ3) ^ 16 / 20922789888000 + (r * ℓ3) ^ 18 / 6402373705728000 - (r * ℓ3) ^ 20 / 2432902008176640000 + (r * ℓ3) ^ 22 / 1124000727777607680000 - (r * ℓ3) ^ 24 / 620448401733239439360000 + (r * ℓ3) ^ 26 / 403291461126605635584000000 - (r * ℓ3) ^ 28 / 304888344611713860501504000000) -
      ((1 / 4 + r ^ 2) * w2) * ((r * ℓ2) ^ 2 / 2 - (r * ℓ2) ^ 4 / 24 + (r * ℓ2) ^ 6 / 720 - (r * ℓ2) ^ 8 / 40320 + (r * ℓ2) ^ 10 / 3628800 - (r * ℓ2) ^ 12 / 479001600 + (r * ℓ2) ^ 14 / 87178291200 - (r * ℓ2) ^ 16 / 20922789888000 + (r * ℓ2) ^ 18 / 6402373705728000 - (r * ℓ2) ^ 20 / 2432902008176640000) =
    (r ^ 2) * ((2 * (s3 - 1) + -(s3 * ℓ3 ^ 1 / 1) + C3 * ℓ3 ^ 2 / 2 + -(w2 * ℓ2 ^ 2 / 8)) +
    (s3 * ℓ3 ^ 3 / 6 + -(C3 * ℓ3 ^ 4 / 24) + -(B3 * ℓ3 ^ 2 / 2) + w2 * ℓ2 ^ 4 / 96 + -(w2 * ℓ2 ^ 2 / 2)) * (r ^ 2) ^ 1 +
    (-(s3 * ℓ3 ^ 5 / 120) + C3 * ℓ3 ^ 6 / 720 + B3 * ℓ3 ^ 4 / 24 + -(w2 * ℓ2 ^ 6 / 2880) + w2 * ℓ2 ^ 4 / 24) * (r ^ 2) ^ 2 +
    (s3 * ℓ3 ^ 7 / 5040 + -(C3 * ℓ3 ^ 8 / 40320) + -(B3 * ℓ3 ^ 6 / 720) + w2 * ℓ2 ^ 8 / 161280 + -(w2 * ℓ2 ^ 6 / 720)) * (r ^ 2) ^ 3 +
    (-(s3 * ℓ3 ^ 9 / 362880) + C3 * ℓ3 ^ 10 / 3628800 + B3 * ℓ3 ^ 8 / 40320 + -(w2 * ℓ2 ^ 10 / 14515200) + w2 * ℓ2 ^ 8 / 40320) * (r ^ 2) ^ 4 +
    (s3 * ℓ3 ^ 11 / 39916800 + -(C3 * ℓ3 ^ 12 / 479001600) + -(B3 * ℓ3 ^ 10 / 3628800) + w2 * ℓ2 ^ 12 / 1916006400 + -(w2 * ℓ2 ^ 10 / 3628800)) * (r ^ 2) ^ 5 +
    (-(s3 * ℓ3 ^ 13 / 6227020800) + C3 * ℓ3 ^ 14 / 87178291200 + B3 * ℓ3 ^ 12 / 479001600 + -(w2 * ℓ2 ^ 14 / 348713164800) + w2 * ℓ2 ^ 12 / 479001600) * (r ^ 2) ^ 6 +
    (s3 * ℓ3 ^ 15 / 1307674368000 + -(C3 * ℓ3 ^ 16 / 20922789888000) + -(B3 * ℓ3 ^ 14 / 87178291200) + w2 * ℓ2 ^ 16 / 83691159552000 + -(w2 * ℓ2 ^ 14 / 87178291200)) * (r ^ 2) ^ 7 +
    (-(s3 * ℓ3 ^ 17 / 355687428096000) + C3 * ℓ3 ^ 18 / 6402373705728000 + B3 * ℓ3 ^ 16 / 20922789888000 + -(w2 * ℓ2 ^ 18 / 25609494822912000) + w2 * ℓ2 ^ 16 / 20922789888000) * (r ^ 2) ^ 8 +
    (s3 * ℓ3 ^ 19 / 121645100408832000 + -(C3 * ℓ3 ^ 20 / 2432902008176640000) + -(B3 * ℓ3 ^ 18 / 6402373705728000) + w2 * ℓ2 ^ 20 / 9731608032706560000 + -(w2 * ℓ2 ^ 18 / 6402373705728000)) * (r ^ 2) ^ 9 +
    (-(s3 * ℓ3 ^ 21 / 51090942171709440000) + C3 * ℓ3 ^ 22 / 1124000727777607680000 + B3 * ℓ3 ^ 20 / 2432902008176640000 + w2 * ℓ2 ^ 20 / 2432902008176640000) * (r ^ 2) ^ 10 +
    (s3 * ℓ3 ^ 23 / 25852016738884976640000 + -(C3 * ℓ3 ^ 24 / 620448401733239439360000) + -(B3 * ℓ3 ^ 22 / 1124000727777607680000)) * (r ^ 2) ^ 11 +
    (-(s3 * ℓ3 ^ 25 / 15511210043330985984000000) + C3 * ℓ3 ^ 26 / 403291461126605635584000000 + B3 * ℓ3 ^ 24 / 620448401733239439360000) * (r ^ 2) ^ 12 +
    (s3 * ℓ3 ^ 27 / 10888869450418352160768000000 + -(B3 * ℓ3 ^ 26 / 403291461126605635584000000)) * (r ^ 2) ^ 13 +
    (B3 * ℓ3 ^ 28 / 304888344611713860501504000000) * (r ^ 2) ^ 14) - 1 / 2 := by ring

/-- **Low- and Mid-Frequency (`r ^ 2 ≤ 116`) Two-Cell + Resolvent Numerator Bound**. -/
theorem neg_mul_integral_one_three_cosLogProfile_sub_half_le_of_sq_le {r : ℝ} (hr : r ^ 2 ≤ 116) :
    -(1 / 4 + r ^ 2) *
        ((∫ x in (1 : ℝ)..2,
          (cosLogProfile r x - cellSecant (cosLogProfile r) 2 x) / Real.sqrt x) +
         (∫ x in (2 : ℝ)..3,
          (cosLogProfile r x - cellSecant (cosLogProfile r) 3 x) / Real.sqrt x)) -
      1 / 2 ≤
    ((41 / 2880) * r ^ 2 - 19 / 144) * (1 / 4 + r ^ 2) := by
  rw [neg_mul_integral_one_three_cosLogProfile_sub_half_eq r]
  have hℓ2_1 : (693147179 / 1000000000 : ℝ) ≤ Real.log 2 := four_panel_artanh_log_two_lower
  have hℓ2_2 : Real.log 2 ≤ 693147181 / 1000000000 := four_panel_artanh_log_two_upper
  have hℓ3_1 : (1098612287 / 1000000000 : ℝ) ≤ Real.log 3 := four_panel_artanh_log_three_lower
  have hℓ3_2 : Real.log 3 ≤ 1098612289 / 1000000000 := four_panel_artanh_log_three_upper
  have hs2_1 : (1607521 / 1136689 : ℝ) ≤ Real.sqrt 2 := pell_sqrt_two_lower_nine
  have hs2_2 : Real.sqrt 2 ≤ 665857 / 470832 := pell_sqrt_two_upper_nine
  have hs3_low : (716035 / 413403 : ℝ) ≤ Real.sqrt 3 := pell_sqrt_three_lower_nine
  have hs3_high : Real.sqrt 3 ≤ 978122 / 564719 := pell_sqrt_three_upper_nine
  generalize hℓ2_eq : Real.log 2 = ℓ2 at hℓ2_1 hℓ2_2 ⊢
  generalize hℓ3_eq : Real.log 3 = ℓ3 at hℓ3_1 hℓ3_2 ⊢
  generalize hs2_eq : Real.sqrt 2 = s2 at hs2_1 hs2_2 ⊢
  generalize hs3_eq : Real.sqrt 3 = s3 at hs3_low hs3_high ⊢
  generalize hC3_def : s3 - (2 / 3) * s2 = C3
  generalize hB3_def : (8 / 3) * s2 - 2 * s3 = B3
  generalize hw2_def : 4 / 3 + 4 * s3 - (16 / 3) * s2 = w2
  have hB3_eq : (8 * s2 - 6 * s3) / 3 = B3 := by linarith only [hB3_def]
  have hw2_eq : (4 + 12 * s3 - 16 * s2) / 3 = w2 := by linarith only [hw2_def]
  rw [hB3_eq, hw2_eq]
  have hu_nonneg : 0 ≤ r ^ 2 := sq_nonneg r
  have hsin_scaled := mul_sin_ge_scaled_taylor_degree_twenty_eight r ℓ3 (by linarith only [hℓ3_1])
  have hcos3_up := one_sub_cos_le_taylor_degree_twenty_six (r * ℓ3)
  have hcos3_low := taylor_degree_twenty_eight_le_one_sub_cos (r * ℓ3)
  have hcos2_low := taylor_degree_twenty_le_one_sub_cos (r * ℓ2)
  have hterm_sin := mul_le_mul_of_nonneg_left hsin_scaled (by linarith only [hs3_low] : 0 ≤ s3)
  have hterm_C3 := mul_le_mul_of_nonneg_left hcos3_up
    (by linarith only [hC3_def, hs2_2, hs3_low] : 0 ≤ C3)
  have hterm_B3 := mul_le_mul_of_nonneg_left hcos3_low
    (mul_nonneg (by linarith only [hB3_def, hs2_1, hs3_high] : 0 ≤ B3) (sq_nonneg r))
  have hterm_w2 := mul_le_mul_of_nonneg_left hcos2_low
    (mul_nonneg (by positivity : (0 : ℝ) ≤ 1 / 4 + r ^ 2)
      (by linarith only [hw2_def, hs2_2, hs3_low] : 0 ≤ w2))
  have hinner := two_cell_taylor_poly_le_joint_resolvent
    hℓ2_1 hℓ2_2 hℓ3_1 hℓ3_2 hs2_1 hs2_2 hs3_low hs3_high
    hC3_def.symm hB3_def.symm hw2_def.symm hu_nonneg hr
  have hpoly_id := two_cell_taylor_grouping_eq r s3 ℓ3 ℓ2 C3 B3 w2
  have h1 :
      -1 / 2 + 2 * (s3 - 1) * r ^ 2 - s3 * r * Real.sin (r * ℓ3) +
          (C3 - B3 * r ^ 2) * (1 - Real.cos (r * ℓ3)) -
          (1 / 4 + r ^ 2) * w2 * (1 - Real.cos (r * ℓ2)) =
        -1 / 2 + 2 * (s3 - 1) * r ^ 2 - s3 * (r * Real.sin (r * ℓ3)) +
          C3 * (1 - Real.cos (r * ℓ3)) - (B3 * r ^ 2) * (1 - Real.cos (r * ℓ3)) -
          ((1 / 4 + r ^ 2) * w2) * (1 - Real.cos (r * ℓ2)) := by ring
  rw [h1]
  linarith only [hterm_sin, hterm_C3, hterm_B3, hterm_w2, hinner, hpoly_id]

/-- **High-Frequency (`116 ≤ r ^ 2`) Two-Cell + Resolvent Numerator Bound via Cauchy–Schwarz**. -/
theorem neg_mul_integral_one_three_cosLogProfile_sub_half_le_of_le_sq {r : ℝ} (hr : 116 ≤ r ^ 2) :
    -(1 / 4 + r ^ 2) *
        ((∫ x in (1 : ℝ)..2,
          (cosLogProfile r x - cellSecant (cosLogProfile r) 2 x) / Real.sqrt x) +
         (∫ x in (2 : ℝ)..3,
          (cosLogProfile r x - cellSecant (cosLogProfile r) 3 x) / Real.sqrt x)) -
      1 / 2 ≤
    ((41 / 2880) * r ^ 2 - 19 / 144) * (1 / 4 + r ^ 2) := by
  rw [neg_mul_integral_one_three_cosLogProfile_sub_half_eq r]
  have hs2_1 : (1607521 / 1136689 : ℝ) ≤ Real.sqrt 2 := pell_sqrt_two_lower_nine
  have hs2_2 : Real.sqrt 2 ≤ 665857 / 470832 := pell_sqrt_two_upper_nine
  have hs3_low : (716035 / 413403 : ℝ) ≤ Real.sqrt 3 := pell_sqrt_three_lower_nine
  have hs3_high : Real.sqrt 3 ≤ 978122 / 564719 := pell_sqrt_three_upper_nine
  have hs3_2 : Real.sqrt 3 ≤ 262087 / 151316 := by linarith only [hs3_high]
  have hs3_sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hcos2_nn : 0 ≤ 1 - Real.cos (r * Real.log 2) := sub_nonneg.mpr (Real.cos_le_one _)
  have hw2_nn : 0 ≤ (4 + 12 * Real.sqrt 3 - 16 * Real.sqrt 2) / 3 := by
    linarith only [hs2_2, hs3_low]
  have hdrop_w2 :
      0 ≤ (1 / 4 + r ^ 2) * ((4 + 12 * Real.sqrt 3 - 16 * Real.sqrt 2) / 3) *
        (1 - Real.cos (r * Real.log 2)) :=
    mul_nonneg (mul_nonneg (by positivity) hw2_nn) hcos2_nn
  generalize hC3_def : Real.sqrt 3 - (2 / 3) * Real.sqrt 2 = C3
  generalize hB3_def : (8 * Real.sqrt 2 - 6 * Real.sqrt 3) / 3 = B3
  have hC3_1 : (298125447305 / 377736531657 : ℝ) ≤ C3 := by linarith only [hC3_def, hs2_2, hs3_low]
  have hC3_2 : C3 ≤ 21085900441 / 26716655592 := by linarith only [hC3_def, hs2_1, hs3_high]
  have hB3_1 : (1025701003 / 3339581949 : ℝ) ≤ B3 := by linarith only [hB3_def, hs2_1, hs3_high]
  have hB3_2 : B3 ≤ 116015940154 / 377736531657 := by linarith only [hB3_def, hs2_2, hs3_low]
  have hu_nn : 0 ≤ r ^ 2 := sq_nonneg r
  have hcs := sq_linear_cos_sin_le (B3 * r ^ 2 - C3) (-Real.sqrt 3 * r) (r * Real.log 3)
  have hamp_sq :
      (B3 * r ^ 2 - C3) ^ 2 + (-Real.sqrt 3 * r) ^ 2 ≤
        ((192 / 625) * r ^ 2 + 41 / 10) ^ 2 := by
    have hB3_sq : B3 ^ 2 ≤ (116015940154 / 377736531657 : ℝ) ^ 2 := by
      nlinarith only [hB3_1, hB3_2]
    have hB3C3 : (305787570320562146915 / 1261482102599584259493 : ℝ) ≤ B3 * C3 := by
      nlinarith only [hB3_1, hC3_1]
    have hC3_sq : C3 ^ 2 ≤ (21085900441 / 26716655592 : ℝ) ^ 2 := by
      nlinarith only [hC3_1, hC3_2]
    have hm2 := mul_le_mul_of_nonneg_right hB3_sq (by positivity : 0 ≤ (r ^ 2) ^ 2)
    have hm1 := mul_le_mul_of_nonneg_right hB3C3 hu_nn
    have hid1 : (B3 * r ^ 2 - C3) ^ 2 + (-Real.sqrt 3 * r) ^ 2 =
        B3 ^ 2 * (r ^ 2) ^ 2 + (Real.sqrt 3 ^ 2 - 2 * (B3 * C3)) * r ^ 2 + C3 ^ 2 := by ring
    have hid2 : ((192 / 625) * r ^ 2 + 41 / 10) ^ 2 =
        (192 / 625) ^ 2 * (r ^ 2) ^ 2 + 2 * (192 / 625) * (41 / 10) * r ^ 2 + (41 / 10) ^ 2 := by
      ring
    rw [hid1, hs3_sq, hid2]
    linarith only [hm2, hm1, hC3_sq]
  have hosc_le :
      (B3 * r ^ 2 - C3) * Real.cos (r * Real.log 3) +
        (-Real.sqrt 3 * r) * Real.sin (r * Real.log 3) ≤
        (192 / 625) * r ^ 2 + 41 / 10 := by
    have h1 := le_abs_self
      ((B3 * r ^ 2 - C3) * Real.cos (r * Real.log 3) +
        (-Real.sqrt 3 * r) * Real.sin (r * Real.log 3))
    have h2 :
        |(B3 * r ^ 2 - C3) * Real.cos (r * Real.log 3) +
          (-Real.sqrt 3 * r) * Real.sin (r * Real.log 3)| ≤
          (192 / 625) * r ^ 2 + 41 / 10 := by
      rw [← Real.sqrt_sq_eq_abs,
        ← Real.sqrt_sq (by positivity : 0 ≤ (192 / 625) * r ^ 2 + 41 / 10)]
      exact Real.sqrt_le_sqrt (hcs.trans hamp_sq)
    exact h1.trans h2
  have hsec_slope :
      (2 * (Real.sqrt 3 - 1) - B3) * r ^ 2 ≤
        (2 * (262087 / 151316 - 1) - 1025701003 / 3339581949) * r ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith only [hs3_2, hB3_1]) hu_nn
  have hu_quad : 0 ≤ (r ^ 2) ^ 2 - 232 * r ^ 2 + 13456 := by
    rw [show (r ^ 2) ^ 2 - 232 * r ^ 2 + 13456 = (r ^ 2 - 116) ^ 2 by ring]
    positivity
  have hsplit :
      -1 / 2 + 2 * (Real.sqrt 3 - 1) * r ^ 2 -
        Real.sqrt 3 * r * Real.sin (r * Real.log 3) +
        (C3 - B3 * r ^ 2) * (1 - Real.cos (r * Real.log 3)) =
      (2 * (Real.sqrt 3 - 1) - B3) * r ^ 2 + (-1 / 2 + C3) +
        ((B3 * r ^ 2 - C3) * Real.cos (r * Real.log 3) +
          (-Real.sqrt 3 * r) * Real.sin (r * Real.log 3)) := by ring
  have hrhs_exp :
      ((41 / 2880) * r ^ 2 - 19 / 144) * (1 / 4 + r ^ 2) =
        (41 / 2880) * (r ^ 2) ^ 2 - (1479 / 11520) * r ^ 2 - 19 / 576 := by ring
  linarith only [hdrop_w2, hC3_2, hosc_le, hsec_slope, hu_quad, hr, hsplit, hrhs_exp]

/-- **The Global Two-Cell + Resolvent Numerator Bound (`∀ r : ℝ`)**. -/
theorem neg_mul_integral_one_three_cosLogProfile_sub_half_le_joint_resolvent (r : ℝ) :
    -(1 / 4 + r ^ 2) *
        ((∫ x in (1 : ℝ)..2,
          (cosLogProfile r x - cellSecant (cosLogProfile r) 2 x) / Real.sqrt x) +
         (∫ x in (2 : ℝ)..3,
          (cosLogProfile r x - cellSecant (cosLogProfile r) 3 x) / Real.sqrt x)) -
      1 / 2 ≤
    ((41 / 2880) * r ^ 2 - 19 / 144) * (1 / 4 + r ^ 2) := by
  rcases le_total (r ^ 2) 116 with hr | hr
  · exact neg_mul_integral_one_three_cosLogProfile_sub_half_le_of_sq_le hr
  · exact neg_mul_integral_one_three_cosLogProfile_sub_half_le_of_le_sq hr

/-- **The Global Two-Cell Cosine-Log + Resolvent Envelope (`-(41 / 2880) r² + 19 / 144 - (1 / 2) / (1 / 4 + r²) ≤ I_2(r) + I_3(r)`)**:
for **every** `r : ℝ`,
`-(41 / 2880) * r ^ 2 + 19 / 144 - (1 / 2) * (1 / (1 / 4 + r ^ 2)) ≤ I_2(r) + I_3(r)`. -/
theorem two_cell_resolvent_envelope_le_integral_one_three_cosLogProfile (r : ℝ) :
    -(41 / 2880 : ℝ) * r ^ 2 + 19 / 144 - (1 / 2) * (1 / (1 / 4 + r ^ 2)) ≤
      (∫ x in (1 : ℝ)..2,
        (cosLogProfile r x - cellSecant (cosLogProfile r) 2 x) / Real.sqrt x) +
      (∫ x in (2 : ℝ)..3,
        (cosLogProfile r x - cellSecant (cosLogProfile r) 3 x) / Real.sqrt x) := by
  have hden_pos : (0 : ℝ) < 1 / 4 + r ^ 2 := by positivity
  have hden_ne : (1 / 4 + r ^ 2 : ℝ) ≠ 0 := hden_pos.ne'
  have hle := div_le_div_of_nonneg_right
    (neg_mul_integral_one_three_cosLogProfile_sub_half_le_joint_resolvent r) hden_pos.le
  have hlhs :
      (-(1 / 4 + r ^ 2) *
          ((∫ x in (1 : ℝ)..2,
            (cosLogProfile r x - cellSecant (cosLogProfile r) 2 x) / Real.sqrt x) +
           (∫ x in (2 : ℝ)..3,
            (cosLogProfile r x - cellSecant (cosLogProfile r) 3 x) / Real.sqrt x)) -
          1 / 2) /
          (1 / 4 + r ^ 2) =
        -((∫ x in (1 : ℝ)..2,
            (cosLogProfile r x - cellSecant (cosLogProfile r) 2 x) / Real.sqrt x) +
          (∫ x in (2 : ℝ)..3,
            (cosLogProfile r x - cellSecant (cosLogProfile r) 3 x) / Real.sqrt x)) -
          (1 / 2) * (1 / (1 / 4 + r ^ 2)) := by
    field_simp [hden_ne]
  have hrhs :
      (((41 / 2880) * r ^ 2 - 19 / 144) * (1 / 4 + r ^ 2)) / (1 / 4 + r ^ 2) =
        (41 / 2880) * r ^ 2 - 19 / 144 := by
    field_simp [hden_ne]
  rw [hlhs, hrhs] at hle
  linarith

/-- **Clamped Product-Measure Fubini Identity on the Second Cell (`n = 3`, `[2, 3]`)**:
for every `f : WeilTestFn`,
`∫ x in 2..3, (weilSymmetricLogNumerator f.1 x - cellSecant (weilSymmetricLogNumerator f.1) 3 x) / Real.sqrt x = (1 / (2 * π)) * ∫ r : ℝ, ‖paperFT f.1 r‖ ^ 2 * (2 * ∫ x in 2..3, (cosLogProfile r x - cellSecant (cosLogProfile r) 3 x) / Real.sqrt x)`. -/
theorem integral_two_three_weilSymmetricLogNumerator_sub_cellSecant_div_sqrt_eq_spectral
    (f : WeilTestFn) :
    (∫ x in (2 : ℝ)..3,
        (weilSymmetricLogNumerator f.1 x - cellSecant (weilSymmetricLogNumerator f.1) 3 x) /
          Real.sqrt x) =
      (1 / (2 * Real.pi)) *
        ∫ r : ℝ,
          ‖paperFT f.1 r‖ ^ 2 *
            (2 * ∫ x in (2 : ℝ)..3,
              (cosLogProfile r x - cellSecant (cosLogProfile r) 3 x) / Real.sqrt x) := by
  let clamp : ℝ → ℝ := fun x => min 3 (max 2 x)
  let G : ℝ → ℝ → ℝ := fun x r =>
    ‖paperFT f.1 r‖ ^ 2 *
      (2 * (cosLogProfile r (clamp x) - cellSecant (cosLogProfile r) 3 (clamp x)) /
        Real.sqrt (clamp x))
  have hclamp_eq : ∀ x ∈ Icc (2 : ℝ) 3, clamp x = x := fun x hx => by
    dsimp only [clamp]
    rw [max_eq_right hx.1, min_eq_right hx.2]
  have hclamp_ge_two : ∀ x : ℝ, 2 ≤ clamp x := fun x => by
    dsimp only [clamp]
    exact le_min (by norm_num) (le_max_left 2 x)
  have hclamp_le_three : ∀ x : ℝ, clamp x ≤ 3 := fun x => by
    dsimp only [clamp]
    exact min_le_left 3 (max 2 x)
  have hclamp_cont : Continuous clamp :=
    continuous_const.min (continuous_const.max continuous_id)
  have hG_meas : AEStronglyMeasurable (Function.uncurry G)
      ((volume.restrict (Ioc (2 : ℝ) 3)).prod volume) := by
    have hft_meas : AEStronglyMeasurable (fun p : ℝ × ℝ => ‖paperFT f.1 p.2‖ ^ 2)
        ((volume.restrict (Ioc (2 : ℝ) 3)).prod volume) :=
      (integrable_paperFT_norm_sq f).aestronglyMeasurable.comp_snd
    have hlog_clamp : Continuous fun p : ℝ × ℝ => Real.log (clamp p.1) :=
      Real.continuousOn_log.comp_continuous (hclamp_cont.comp continuous_fst) fun p =>
        (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (hclamp_ge_two p.1)).ne'
    have hcos_clamp : Continuous fun p : ℝ × ℝ => cosLogProfile p.2 (clamp p.1) := by
      unfold cosLogProfile
      exact Real.continuous_cos.comp (continuous_snd.mul hlog_clamp)
    have hsec_clamp : Continuous fun p : ℝ × ℝ => cellSecant (cosLogProfile p.2) 3 (clamp p.1) := by
      unfold cellSecant cosLogProfile
      have h1 : Continuous fun p : ℝ × ℝ => ((3 : ℕ) : ℝ) - clamp p.1 :=
        continuous_const.sub (hclamp_cont.comp continuous_fst)
      have h2 : Continuous fun p : ℝ × ℝ => clamp p.1 - (((3 : ℕ) : ℝ) - 1) :=
        (hclamp_cont.comp continuous_fst).sub continuous_const
      have h3 : Continuous fun p : ℝ × ℝ => Real.cos (p.2 * Real.log (((3 : ℕ) : ℝ) - 1)) :=
        Real.continuous_cos.comp (continuous_snd.mul continuous_const)
      have h4 : Continuous fun p : ℝ × ℝ => Real.cos (p.2 * Real.log (3 : ℕ)) :=
        Real.continuous_cos.comp (continuous_snd.mul continuous_const)
      exact (h1.mul h3).add (h2.mul h4)
    have hsqrt_clamp : Continuous fun p : ℝ × ℝ => Real.sqrt (clamp p.1) :=
      Real.continuous_sqrt.comp (hclamp_cont.comp continuous_fst)
    have hquot : Continuous fun p : ℝ × ℝ =>
        2 * (cosLogProfile p.2 (clamp p.1) - cellSecant (cosLogProfile p.2) 3 (clamp p.1)) /
          Real.sqrt (clamp p.1) :=
      (continuous_const.mul (hcos_clamp.sub hsec_clamp)).div hsqrt_clamp fun p =>
        (Real.sqrt_pos.mpr (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (hclamp_ge_two p.1))).ne'
    exact hft_meas.mul hquot.aestronglyMeasurable
  have hG_bound : ∀ p : ℝ × ℝ, ‖Function.uncurry G p‖ ≤ 6 * ‖paperFT f.1 p.2‖ ^ 2 := by
    intro ⟨x, r⟩
    change ‖G x r‖ ≤ 6 * ‖paperFT f.1 r‖ ^ 2
    dsimp only [G]
    have hc2 : 2 ≤ clamp x := hclamp_ge_two x
    have hc3 : clamp x ≤ 3 := hclamp_le_three x
    have hsqrt_ge : 1 ≤ Real.sqrt (clamp x) := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt (by linarith)
    have hcos_abs : |cosLogProfile r (clamp x)| ≤ 1 := Real.abs_cos_le_one _
    have hsec_abs : |cellSecant (cosLogProfile r) 3 (clamp x)| ≤ 2 := by
      unfold cellSecant
      norm_num
      have ha : |cosLogProfile r 2| ≤ 1 := Real.abs_cos_le_one _
      have hb : |cosLogProfile r 3| ≤ 1 := Real.abs_cos_le_one _
      have htri := abs_add_le ((3 - clamp x) * cosLogProfile r 2)
        ((clamp x - 2) * cosLogProfile r 3)
      have hw1 : |3 - clamp x| = 3 - clamp x := abs_of_nonneg (by linarith)
      have hw2 : |clamp x - 2| = clamp x - 2 := abs_of_nonneg (by linarith)
      rw [abs_mul, abs_mul, hw1, hw2] at htri
      nlinarith
    have hnum_abs :
        |2 * (cosLogProfile r (clamp x) - cellSecant (cosLogProfile r) 3 (clamp x))| ≤ 6 := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      have htri := abs_sub (cosLogProfile r (clamp x)) (cellSecant (cosLogProfile r) 3 (clamp x))
      linarith
    have hdiv_abs :
        |2 * (cosLogProfile r (clamp x) - cellSecant (cosLogProfile r) 3 (clamp x)) /
          Real.sqrt (clamp x)| ≤ 6 := by
      rw [abs_div, abs_of_pos (lt_of_lt_of_le zero_lt_one hsqrt_ge)]
      exact (div_le_self (abs_nonneg _) hsqrt_ge).trans hnum_abs
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _), mul_comm]
    exact mul_le_mul_of_nonneg_right hdiv_abs (sq_nonneg _)
  haveI : IsFiniteMeasure (volume.restrict (Ioc (2 : ℝ) 3)) := ⟨by simp [Real.volume_Ioc]⟩
  have hprod_int : Integrable (Function.uncurry G)
      ((volume.restrict (Ioc (2 : ℝ) 3)).prod volume) :=
    Integrable.mono' ((integrable_const (6 : ℝ)).mul_prod (integrable_paperFT_norm_sq f))
      hG_meas (Eventually.of_forall hG_bound)
  have hswap := MeasureTheory.integral_integral_swap hprod_int
  have hlhs :
      (∫ x in (2 : ℝ)..3,
          (weilSymmetricLogNumerator f.1 x - cellSecant (weilSymmetricLogNumerator f.1) 3 x) /
            Real.sqrt x) =
        (1 / (2 * Real.pi)) * ∫ x in Ioc (2 : ℝ) 3, ∫ r : ℝ, G x r := by
    rw [intervalIntegral.integral_of_le (by norm_num : (2 : ℝ) ≤ 3), ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
    have hx_cc : x ∈ Icc (2 : ℝ) 3 := Ioc_subset_Icc_self hx
    rw [weilSymmetricLogNumerator_sub_cellSecant_eq_spectral f 3 x, mul_div_assoc,
      ← integral_div]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun r => ?_)
    dsimp only [G]
    rw [hclamp_eq x hx_cc, mul_div_assoc]
  have hrhs :
      (∫ r : ℝ, ∫ x in Ioc (2 : ℝ) 3, G x r) =
        ∫ r : ℝ,
          ‖paperFT f.1 r‖ ^ 2 *
            (2 * ∫ x in (2 : ℝ)..3,
              (cosLogProfile r x - cellSecant (cosLogProfile r) 3 x) / Real.sqrt x) := by
    refine integral_congr_ae (Eventually.of_forall fun r => ?_)
    dsimp only
    rw [intervalIntegral.integral_of_le (by norm_num : (2 : ℝ) ≤ 3),
      ← integral_const_mul, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
    have hx_cc : x ∈ Icc (2 : ℝ) 3 := Ioc_subset_Icc_self hx
    dsimp only [G]
    rw [hclamp_eq x hx_cc, mul_div_assoc]
  rw [hlhs, hswap, hrhs]

/-- Integrability of `r ↦ ‖paperFT f.1 r‖ ^ 2 * (2 * I_3(r))`. -/
theorem integrable_paperFT_norm_sq_mul_two_integral_two_three_cosLogProfile (f : WeilTestFn) :
    Integrable fun r : ℝ =>
      ‖paperFT f.1 r‖ ^ 2 *
        (2 * ∫ x in (2 : ℝ)..3,
          (cosLogProfile r x - cellSecant (cosLogProfile r) 3 x) / Real.sqrt x) := by
  have hmeas : AEStronglyMeasurable (fun r : ℝ =>
      ‖paperFT f.1 r‖ ^ 2 *
        (2 * ∫ x in (2 : ℝ)..3,
          (cosLogProfile r x - cellSecant (cosLogProfile r) 3 x) / Real.sqrt x)) volume := by
    have h1 : AEStronglyMeasurable (fun r : ℝ => ‖paperFT f.1 r‖ ^ 2) volume :=
      (integrable_paperFT_norm_sq f).aestronglyMeasurable
    have h2 : Continuous fun r : ℝ =>
        ∫ x in (2 : ℝ)..3,
          (cosLogProfile r x - cellSecant (cosLogProfile r) 3 x) / Real.sqrt x := by
      have hrew : (fun r : ℝ =>
          ∫ x in (2 : ℝ)..3,
            (cosLogProfile r x - cellSecant (cosLogProfile r) 3 x) / Real.sqrt x) =
          fun r : ℝ =>
            ((cosLogAntideriv r 3 - cosLogAntideriv r 2) -
              (((12 * Real.sqrt 3 - 14 * Real.sqrt 2) / 3) * Real.cos (r * Real.log 2) +
                ((8 * Real.sqrt 2 - 6 * Real.sqrt 3) / 3) * Real.cos (r * Real.log 3))) := by
        ext r
        have h := neg_mul_integral_two_three_cosLogProfile_sub_cellSecant_div_sqrt_eq r
        have hden_ne : (1 / 4 + r ^ 2 : ℝ) ≠ 0 := by positivity
        apply mul_left_cancel₀ hden_ne
        linarith
      rw [hrew]
      unfold cosLogAntideriv
      refine Continuous.sub (Continuous.sub ?_ ?_) (by fun_prop)
      · refine Continuous.div (by fun_prop) (by fun_prop) (fun r => by positivity)
      · refine Continuous.div (by fun_prop) (by fun_prop) (fun r => by positivity)
    exact h1.mul (continuous_const.mul h2).aestronglyMeasurable
  have hbound : ∀ r : ℝ,
      ‖‖paperFT f.1 r‖ ^ 2 *
        (2 * ∫ x in (2 : ℝ)..3,
          (cosLogProfile r x - cellSecant (cosLogProfile r) 3 x) / Real.sqrt x)‖ ≤
        6 * ‖paperFT f.1 r‖ ^ 2 := by
    intro r
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg _),
      abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hint_abs :
        |∫ x in (2 : ℝ)..3,
          (cosLogProfile r x - cellSecant (cosLogProfile r) 3 x) / Real.sqrt x| ≤ 3 := by
      have h := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := 2) (b := 3) (C := 3)
        (f := fun x => (cosLogProfile r x - cellSecant (cosLogProfile r) 3 x) / Real.sqrt x)
        (fun x hx => by
          rw [uIoc_of_le (by norm_num : (2 : ℝ) ≤ 3)] at hx
          have hx2 : 2 ≤ x := hx.1.le
          have hx3 : x ≤ 3 := hx.2
          have hsqrt_ge : 1 ≤ Real.sqrt x := by
            rw [← Real.sqrt_one]
            exact Real.sqrt_le_sqrt (by linarith)
          have hcos_abs : |cosLogProfile r x| ≤ 1 := Real.abs_cos_le_one _
          have hsec_abs : |cellSecant (cosLogProfile r) 3 x| ≤ 2 := by
            unfold cellSecant
            norm_num
            have ha : |cosLogProfile r 2| ≤ 1 := Real.abs_cos_le_one _
            have hb : |cosLogProfile r 3| ≤ 1 := Real.abs_cos_le_one _
            have htri := abs_add_le ((3 - x) * cosLogProfile r 2)
              ((x - 2) * cosLogProfile r 3)
            have hw1 : |3 - x| = 3 - x := abs_of_nonneg (by linarith)
            have hw2 : |x - 2| = x - 2 := abs_of_nonneg (by linarith)
            rw [abs_mul, abs_mul, hw1, hw2] at htri
            nlinarith
          rw [Real.norm_eq_abs, abs_div, abs_of_pos (lt_of_lt_of_le zero_lt_one hsqrt_ge)]
          refine (div_le_self (abs_nonneg _) hsqrt_ge).trans ?_
          have htri := abs_sub (cosLogProfile r x) (cellSecant (cosLogProfile r) 3 x)
          linarith)
      rw [Real.norm_eq_abs, show |(3 : ℝ) - 2| = 1 by norm_num, mul_one] at h
      exact h
    nlinarith [sq_nonneg ‖paperFT f.1 r‖]
  exact ((integrable_paperFT_norm_sq f).const_mul 6).mono' hmeas (Eventually.of_forall hbound)

/-- **The Two-Cell (`[1, 3]`) + Resolvent Spectral Inequality (`19 / 72` Surplus, `41 / 2880` Slope)**:
for every `f : WeilTestFn` with `Integrable (fun r => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))`,
`(19 / 72) * ∫ ‖f.1‖² - (41 / 2880) * spectralSecondMoment f.1 ≤ bochnerResolventEnergy (EF.weilTest f.1 f.1) + I_2(f) + I_3(f)`. -/
theorem nineteen_seventy_seconds_l2_sub_forty_one_second_le_bochnerResolventEnergy_add_integral_one_three
    (f : WeilTestFn)
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2)) :
    (19 / 72 : ℝ) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) -
        (41 / 2880) * spectralSecondMoment f.1 ≤
      bochnerResolventEnergy (EF.weilTest f.1 f.1) +
        (∫ x in (1 : ℝ)..2,
          (weilSymmetricLogNumerator f.1 x - cellSecant (weilSymmetricLogNumerator f.1) 2 x) /
            Real.sqrt x) +
        (∫ x in (2 : ℝ)..3,
          (weilSymmetricLogNumerator f.1 x - cellSecant (weilSymmetricLogNumerator f.1) 3 x) /
            Real.sqrt x) := by
  rw [integral_one_two_weilSymmetricLogNumerator_sub_cellSecant_div_sqrt_eq_spectral f,
    integral_two_three_weilSymmetricLogNumerator_sub_cellSecant_div_sqrt_eq_spectral f,
    bochnerResolventEnergy_weilTest_eq f]
  have hsq := integrable_paperFT_norm_sq f
  have hres_int := integrable_paperFT_norm_sq_mul_inv_quarter_add_sq f
  have hcell2_int := integrable_paperFT_norm_sq_mul_two_integral_one_two_cosLogProfile f
  have hcell3_int := integrable_paperFT_norm_sq_mul_two_integral_two_three_cosLogProfile f
  have hplanch := one_div_two_pi_mul_integral_paperFT_norm_sq_mul_two_eq f
  have hlhs_eq :
      (19 / 72 : ℝ) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) -
          (41 / 2880) * spectralSecondMoment f.1 =
        (1 / (2 * Real.pi)) *
          ∫ r : ℝ,
            ((19 / 144 : ℝ) * (‖paperFT f.1 r‖ ^ 2 * 2) +
              (-(41 / 2880 : ℝ)) * (‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))) := by
    unfold spectralSecondMoment
    rw [integral_add ((hsq.mul_const 2).const_mul (19 / 144 : ℝ))
      (hint2.const_mul (-(41 / 2880 : ℝ))),
      integral_const_mul, integral_const_mul]
    linear_combination -(19 / 144 : ℝ) * hplanch
  have hrhs_eq :
      (1 / (2 * Real.pi)) * (∫ r : ℝ, ‖paperFT f.1 r‖ ^ 2 * (1 / (1 / 4 + r ^ 2))) +
          (1 / (2 * Real.pi)) *
            (∫ r : ℝ,
              ‖paperFT f.1 r‖ ^ 2 *
                (2 * ∫ x in (1 : ℝ)..2,
                  (cosLogProfile r x - cellSecant (cosLogProfile r) 2 x) / Real.sqrt x)) +
          (1 / (2 * Real.pi)) *
            (∫ r : ℝ,
              ‖paperFT f.1 r‖ ^ 2 *
                (2 * ∫ x in (2 : ℝ)..3,
                  (cosLogProfile r x - cellSecant (cosLogProfile r) 3 x) / Real.sqrt x)) =
        (1 / (2 * Real.pi)) *
          ∫ r : ℝ,
            (‖paperFT f.1 r‖ ^ 2 * (1 / (1 / 4 + r ^ 2)) +
              ‖paperFT f.1 r‖ ^ 2 *
                (2 * ∫ x in (1 : ℝ)..2,
                  (cosLogProfile r x - cellSecant (cosLogProfile r) 2 x) / Real.sqrt x) +
              ‖paperFT f.1 r‖ ^ 2 *
                (2 * ∫ x in (2 : ℝ)..3,
                  (cosLogProfile r x - cellSecant (cosLogProfile r) 3 x) / Real.sqrt x)) := by
    rw [integral_add (hres_int.add hcell2_int) hcell3_int, integral_add hres_int hcell2_int]
    ring
  rw [hlhs_eq, hrhs_eq]
  refine mul_le_mul_of_nonneg_left ?_ (div_nonneg zero_le_one Real.two_pi_pos.le)
  refine integral_mono
    (((hsq.mul_const 2).const_mul (19 / 144 : ℝ)).add (hint2.const_mul (-(41 / 2880 : ℝ))))
    ((hres_int.add hcell2_int).add hcell3_int) fun r => ?_
  dsimp only
  have hpt := two_cell_resolvent_envelope_le_integral_one_three_cosLogProfile r
  have hmul := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hpt (by norm_num : (0 : ℝ) ≤ 2))
    (sq_nonneg ‖paperFT f.1 r‖)
  linarith

/-- **Tail Cell-Weight Sum Bound on `Finset.Icc 4 N` (`≤ 31 / 2880`)**:
for every `N : ℕ`, `∑ n ∈ Finset.Icc 4 N, hermiteQuinticCellWeight n ≤ 31 / 2880`. -/
theorem sum_Icc_four_hermiteQuinticCellWeight_le (N : ℕ) :
    (∑ n ∈ Finset.Icc 4 N, hermiteQuinticCellWeight n) ≤ 31 / 2880 := by
  have h4_bound :
      hermiteQuinticCellWeight 4 ≤
        (1 / 12) * ((1 / 3) * (1 / Real.sqrt 3) - 1 / 8) -
          (1 / Real.sqrt 3 - 1 / 2) * (61 / 2520) := by
    rw [hermiteQuinticCellWeight_eq]
    have hlog4 := two_mul_sub_div_add_le_log_sub_log
      (by norm_num : (0 : ℝ) < 3) (by norm_num : (3 : ℝ) ≤ 4)
    have h4_eq : (4 : ℝ) = 2 ^ 2 := by norm_num
    have hsqrt4 : Real.sqrt 4 = 2 := by
      rw [h4_eq, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
    have hsqrt4_ge : Real.sqrt 3 ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by norm_num)
    have hdiff4 : 0 ≤ 1 / Real.sqrt 3 - 1 / 2 := by
      have := one_div_le_one_div_of_le (Real.sqrt_pos.mpr (by norm_num)) hsqrt4_ge
      rw [hsqrt4] at this
      linarith
    have h1 : ((4 : ℕ) : ℝ) - 1 = 3 := by norm_num
    have h2 : ((4 : ℕ) : ℝ) = 4 := by norm_num
    rw [h1, h2, hsqrt4]
    have hmul := mul_le_mul_of_nonneg_left hlog4 hdiff4
    linarith
  have hsqrt3_ge : (19 / 11 : ℝ) ≤ Real.sqrt 3 := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 19 / 11)]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hinv_sqrt3_le : 1 / Real.sqrt 3 ≤ 11 / 19 := by
    have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 19 / 11) hsqrt3_ge
    linarith
  have htail5 := sum_Icc_five_hermiteQuinticCellWeight_le N
  by_cases hN4 : 4 ≤ N
  · rw [sum_Icc_eq_add_sum_Icc_succ hermiteQuinticCellWeight hN4]
    linarith
  · rw [Finset.Icc_eq_empty hN4, Finset.sum_empty]
    norm_num

/-- **Tail Geometric-Mean Curvature Bound on `Finset.Icc 4 N` (`-(31 / 2880) √(S(S + 2L))`)**. -/
theorem neg_thirty_one_twenty_eight_eightieths_sqrt_le_sum_Icc_four
    (f : WeilTestFn)
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))
    (N : ℕ) :
    -(31 / 2880) *
        Real.sqrt
          (spectralSecondMoment f.1 *
            (spectralSecondMoment f.1 + 2 * ∫ u : ℝ, ‖f.1 u‖ ^ 2)) ≤
      ∑ n ∈ Finset.Icc 4 N,
        ∫ x in ((n : ℝ) - 1)..(n : ℝ),
          (weilSymmetricLogNumerator f.1 x - cellSecant (weilSymmetricLogNumerator f.1) n x) /
            Real.sqrt x := by
  let S := spectralSecondMoment f.1
  let L := ∫ u : ℝ, ‖f.1 u‖ ^ 2
  have hS_nonneg : 0 ≤ S := spectralSecondMoment_nonneg f.1
  have hL_nonneg : 0 ≤ L := integral_nonneg fun _ => sq_nonneg _
  have hvar : ∀ {b : ℝ}, 0 < b →
      -(31 / 2880) * ((b + 1 / (4 * b)) * S + 2 * b * L) ≤
        ∑ n ∈ Finset.Icc 4 N,
          ∫ x in ((n : ℝ) - 1)..(n : ℝ),
            (weilSymmetricLogNumerator f.1 x - cellSecant (weilSymmetricLogNumerator f.1) n x) /
              Real.sqrt x := by
    intro b hb
    let M := (b + 1 / (4 * b)) * S + 2 * b * L
    have hM_nonneg : 0 ≤ M := by dsimp only [M]; positivity
    have hcell_le : ∀ n ∈ Finset.Icc 4 N,
        -M * hermiteQuinticCellWeight n ≤
          ∫ x in ((n : ℝ) - 1)..(n : ℝ),
            (weilSymmetricLogNumerator f.1 x - cellSecant (weilSymmetricLogNumerator f.1) n x) /
              Real.sqrt x := by
      intro n hn
      have hn4 : 4 ≤ n := (Finset.mem_Icc.mp hn).1
      have hn2 : 2 ≤ n := by omega
      have hn2_real : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
      have hn_le : (n : ℝ) - 1 ≤ (n : ℝ) := by linarith
      have hint_low : IntervalIntegrable
          (fun x => -M * ((Real.log x - cellSecant Real.log n x) / Real.sqrt x))
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
        dsimp only [M, S, L]
        linarith [show -(((b + 1 / (4 * b)) * spectralSecondMoment f.1 +
            2 * b * ∫ u : ℝ, ‖f.1 u‖ ^ 2) * (Real.log x - cellSecant Real.log n x)) /
            Real.sqrt x =
          -((b + 1 / (4 * b)) * spectralSecondMoment f.1 + 2 * b * ∫ u : ℝ, ‖f.1 u‖ ^ 2) *
            ((Real.log x - cellSecant Real.log n x) / Real.sqrt x) by ring]
      rw [intervalIntegral.integral_const_mul] at hmono
      have hweight := mul_le_mul_of_nonneg_left
        (integral_log_sub_cellSecant_div_sqrt_le_hermiteQuinticCellWeight hn2) hM_nonneg
      linarith
    have hsum := Finset.sum_le_sum hcell_le
    rw [← Finset.mul_sum] at hsum
    have htail := mul_le_mul_of_nonneg_left (sum_Icc_four_hermiteQuinticCellWeight_le N) hM_nonneg
    linarith
  change -(31 / 2880) * Real.sqrt (S * (S + 2 * L)) ≤ _
  rcases eq_or_lt_of_le hS_nonneg with hS0 | hS_pos
  · rw [← hS0, zero_mul, Real.sqrt_zero, mul_zero]
    refine le_of_forall_pos_le_add fun ε hε => ?_
    rcases eq_or_lt_of_le hL_nonneg with hL0 | hL_pos
    · have h1 := hvar zero_lt_one
      rw [← hS0, ← hL0] at h1
      linarith
    · let b := 1440 * ε / (31 * L)
      have hb_pos : 0 < b := by dsimp only [b]; positivity
      have h1 := hvar hb_pos
      rw [← hS0, mul_zero, zero_add] at h1
      have h2 : (31 / 2880) * (2 * b * L) = ε := by
        dsimp only [b]
        have hL_ne : L ≠ 0 := hL_pos.ne'
        field_simp [hL_ne]
        ring
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

/-- **The Two-Cell `41 / 2880 + 31 / 2880 = 1 / 40` Resolvent + Secant Numerator Law**:
for every `f : WeilTestFn` with `Integrable (fun r => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))` and `3 ≤ N`,
`(19 / 72) * ∫ ‖f.1‖² - (41 / 2880) * S - (31 / 2880) * √(S(S + 2L)) ≤ bochnerResolventEnergy (EF.weilTest f.1 f.1) + secantNumeratorCellDefect f.1 N`. -/
theorem nineteen_seventy_seconds_l2_sub_forty_one_second_sub_thirty_one_geom_le_bochnerResolventEnergy_add_secantNumeratorCellDefect
    (f : WeilTestFn)
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))
    {N : ℕ} (hN3 : 3 ≤ N) :
    (19 / 72 : ℝ) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) -
        (41 / 2880) * spectralSecondMoment f.1 -
        (31 / 2880) *
          Real.sqrt
            (spectralSecondMoment f.1 *
              (spectralSecondMoment f.1 + 2 * ∫ u : ℝ, ‖f.1 u‖ ^ 2)) ≤
      bochnerResolventEnergy (EF.weilTest f.1 f.1) +
        secantNumeratorCellDefect f.1 N := by
  unfold secantNumeratorCellDefect
  rw [sum_Icc_eq_add_sum_Icc_succ _ (by omega : 2 ≤ N),
    sum_Icc_eq_add_sum_Icc_succ _ hN3]
  have h13 :=
    nineteen_seventy_seconds_l2_sub_forty_one_second_le_bochnerResolventEnergy_add_integral_one_three
      f hint2
  have h4 := neg_thirty_one_twenty_eight_eightieths_sqrt_le_sum_Icc_four f hint2 N
  have hc2 : ((2 : ℕ) : ℝ) - 1 = 1 ∧ ((2 : ℕ) : ℝ) = 2 := ⟨by norm_num, by norm_num⟩
  have hc3 : ((3 : ℕ) : ℝ) - 1 = 2 ∧ ((3 : ℕ) : ℝ) = 3 := ⟨by norm_num, by norm_num⟩
  rw [hc2.1, hc2.2, hc3.1, hc3.2]
  linarith

/-! ## Section 3: Coercivity, Unconditional `0 ≤ markovEnergy`, and Cutoff-Free `EWU` Spectral Gaps up to `43` and `45`, Deep into the `S / L > 69 / 2 = 34.5` Regime -/

/-- **Automatic Integer Support-Cutoff Existence (`3 ≤ N`) for `WeilTestFn`**:
every `f : WeilTestFn` admits an integer cutoff `3 ≤ N` such that `EF.weilTest f.1 f.1 (Real.log x) = 0`
and `EF.weilTest f.1 f.1 (-Real.log x) = 0` at `x = N` and for all `x > N`. -/
theorem exists_support_cutoff_three_weilTest (f : WeilTestFn) :
    ∃ N : ℕ, 3 ≤ N ∧
      (EF.weilTest f.1 f.1 (Real.log N) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log N) = 0) ∧
      (∀ x : ℝ, (N : ℝ) < x →
        EF.weilTest f.1 f.1 (Real.log x) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log x) = 0) := by
  obtain ⟨N, hN2, _, hN⟩ := exists_support_cutoff_weilTest f
  refine ⟨N + 1, by omega, hN (N + 1 : ℕ) (by exact_mod_cast Nat.lt_succ_self N), fun x hx =>
    hN x (lt_trans (by exact_mod_cast Nat.lt_succ_self N) hx)⟩

/-- **Universal Tangent Upper Bound `Real.sqrt (S * (S + 2 * L)) ≤ (3961 / 3960) * S + (44 / 45) * L`**:
evaluating the variational envelope at `b = 22 / 45` (`((3961 / 3960) S + (44 / 45) L)² - S(S + 2L) = ((89 / 3960) S - (44 / 45) L)² ≥ 0`) gives a linear upper bound that is exact at `S / L = 348480 / 8010 ≈ 43.51`. -/
theorem sqrt_spectralSecondMoment_mul_add_two_l2_le_add_forty_four_forty_fifths
    (f : WeilTestFn) :
    Real.sqrt
        (spectralSecondMoment f.1 *
          (spectralSecondMoment f.1 + 2 * ∫ u : ℝ, ‖f.1 u‖ ^ 2)) ≤
      (3961 / 3960) * spectralSecondMoment f.1 + (44 / 45) * ∫ u : ℝ, ‖f.1 u‖ ^ 2 := by
  let S := spectralSecondMoment f.1
  let L := ∫ u : ℝ, ‖f.1 u‖ ^ 2
  have hS_nonneg : 0 ≤ S := spectralSecondMoment_nonneg f.1
  have hL_nonneg : 0 ≤ L := integral_nonneg fun _ => sq_nonneg _
  rw [← Real.sqrt_sq (by positivity : 0 ≤ (3961 / 3960) * S + (44 / 45) * L)]
  refine Real.sqrt_le_sqrt ?_
  have hsq : 0 ≤ ((89 / 3960) * S - (44 / 45) * L) ^ 2 := sq_nonneg _
  linarith

/-- **Resolvent-Enhanced Quadrature Coercivity up to Critical Ratio `43` (Upgraded from `33`)**:
whenever `spectralSecondMoment f.1 ≤ 43 * ∫ ‖f.1‖²`, we have
`(1 / 700) * ∫ ‖f.1‖² ≤ bochnerResolventEnergy (EF.weilTest f.1 f.1) + rightCellQuadratureDefect (weilContinuumLogProfile f.1) N`! -/
theorem one_seven_hundredth_l2_le_bochnerResolventEnergy_add_rightCellQuadratureDefect_of_spectralSecondMoment_le_forty_three
    (f : WeilTestFn)
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))
    {N : ℕ} (hN3 : 3 ≤ N)
    (hN0 : EF.weilTest f.1 f.1 (Real.log N) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log N) = 0)
    (hN : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0)
    (hsec : spectralSecondMoment f.1 ≤ 43 * ∫ u : ℝ, ‖f.1 u‖ ^ 2) :
    (1 / 700) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) ≤
      bochnerResolventEnergy (EF.weilTest f.1 f.1) +
        rightCellQuadratureDefect (weilContinuumLogProfile f.1) N := by
  have hL : 0 ≤ ∫ u : ℝ, ‖f.1 u‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have h1 :=
    two_forty_seven_three_hundredths_l2_add_secantNumerator_le_rightCellQuadratureDefect
      f (by omega : 1 ≤ N) hN0 hN
  have h2 :=
    nineteen_seventy_seconds_l2_sub_forty_one_second_sub_thirty_one_geom_le_bochnerResolventEnergy_add_secantNumeratorCellDefect
      f hint2 hN3
  have hamgm := sqrt_spectralSecondMoment_mul_add_two_l2_le_add_forty_four_forty_fifths f
  linarith

/-- **Resolvent-Enhanced Quadrature Coercivity on the Nonnegative Log-Value Cone up to `45`
(Upgraded from `69 / 2 = 34.5`, `+10.5` Units into the `S / L > 69 / 2` Regime)**:
whenever `∀ n ∈ Finset.Icc 2 N, 0 ≤ logValue f.1 n` and `spectralSecondMoment f.1 ≤ 45 * ∫ ‖f.1‖²`,
`(1 / 300) * ∫ ‖f.1‖² ≤ bochnerResolventEnergy (EF.weilTest f.1 f.1) + rightCellQuadratureDefect (weilContinuumLogProfile f.1) N`! -/
theorem one_three_hundredth_l2_le_bochnerResolventEnergy_add_rightCellQuadratureDefect_of_spectralSecondMoment_le_forty_five_of_logValue_nonneg
    (f : WeilTestFn)
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))
    {N : ℕ} (hN3 : 3 ≤ N)
    (hN0 : EF.weilTest f.1 f.1 (Real.log N) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log N) = 0)
    (hN : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0)
    (hpos : ∀ n ∈ Finset.Icc 2 N, 0 ≤ logValue f.1 n)
    (hsec : spectralSecondMoment f.1 ≤ 45 * ∫ u : ℝ, ‖f.1 u‖ ^ 2) :
    (1 / 300) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) ≤
      bochnerResolventEnergy (EF.weilTest f.1 f.1) +
        rightCellQuadratureDefect (weilContinuumLogProfile f.1) N := by
  have hL : 0 ≤ ∫ u : ℝ, ‖f.1 u‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have h1 :=
    twelve_sixty_one_fourteen_fortieths_l2_add_secantNumerator_le_rightCellQuadratureDefect_of_logValue_nonneg
      f (by omega : 1 ≤ N) hN0 hN hpos
  have h2 :=
    nineteen_seventy_seconds_l2_sub_forty_one_second_sub_thirty_one_geom_le_bochnerResolventEnergy_add_secantNumeratorCellDefect
      f hint2 hN3
  have hamgm := sqrt_spectralSecondMoment_mul_add_two_l2_le_add_forty_four_forty_fifths f
  linarith

/-- **Resolvent-Enhanced Quadrature Coercivity on the Prime-Blind Cone (`logVector f = 0`) up to `45`
(Upgraded from `69 / 2 = 34.5`, `+10.5` Units into the `S / L > 69 / 2` Regime)**: -/
theorem one_three_hundredth_l2_le_bochnerResolventEnergy_add_rightCellQuadratureDefect_of_spectralSecondMoment_le_forty_five_of_logVector_eq_zero
    (f : WeilTestFn) (hblind : logVector f = 0)
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))
    {N : ℕ} (hN3 : 3 ≤ N)
    (hN0 : EF.weilTest f.1 f.1 (Real.log N) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log N) = 0)
    (hN : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0)
    (hsec : spectralSecondMoment f.1 ≤ 45 * ∫ u : ℝ, ‖f.1 u‖ ^ 2) :
    (1 / 300) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) ≤
      bochnerResolventEnergy (EF.weilTest f.1 f.1) +
        rightCellQuadratureDefect (weilContinuumLogProfile f.1) N := by
  have hL : 0 ≤ ∫ u : ℝ, ‖f.1 u‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have h1 :=
    twelve_sixty_one_fourteen_fortieths_l2_add_secantNumerator_le_rightCellQuadratureDefect_of_logVector_eq_zero
      f hblind (by omega : 1 ≤ N) hN0 hN
  have h2 :=
    nineteen_seventy_seconds_l2_sub_forty_one_second_sub_thirty_one_geom_le_bochnerResolventEnergy_add_secantNumeratorCellDefect
      f hint2 hN3
  have hamgm := sqrt_spectralSecondMoment_mul_add_two_l2_le_add_forty_four_forty_fifths f
  linarith

/-- **Unconditional `0 ≤ markovEnergy F` on the Primitive Hyperplane up to `43 * ∫ ‖F‖²`
(Upgraded from `33 * ∫ ‖F‖²`)**: -/
theorem markovEnergy_ofReal_nonneg_of_spectralSecondMoment_le_forty_three_of_cosh_zero
    (m : ℕ) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hcosh : coshHalfMoment f = 0)
    (hint2 : Integrable fun r : ℝ => ‖paperFT (realWeilTestFn f hf hfc).1 r‖ ^ 2 * (2 * r ^ 2))
    {N : ℕ} (hN3 : 3 ≤ N)
    (hN0 : EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log N) = 0 ∧
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log N) = 0)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log x) = 0 ∧
        EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log x) = 0)
    (hdiff : ∀ n ∈ Finset.Icc 2 N,
      0 ≤ iteratedForwardDiff m (logValue (realWeilTestFn f hf hfc).1) n)
    (hsec_bound : spectralSecondMoment (realWeilTestFn f hf hfc).1 ≤
      43 * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) :
    0 ≤ markovEnergy (realWeilTestFn f hf hfc).1 := by
  have hL_nonneg : 0 ≤ ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  let θ := max (max 1 (Real.log (N : ℝ))) 2801
  have hθlog : Real.log (N : ℝ) ≤ θ :=
    (le_max_right 1 (Real.log (N : ℝ))).trans (le_max_left _ _)
  have hθ_large : (2801 : ℝ) ≤ θ := le_max_right _ _
  have hθ_sub : (2800 : ℝ) ≤ θ - 1 := by linarith
  have hbase := one_hundredth_l2_add_theta_slope_quadrature_le_markovEnergy_of_cosh_zero
    m hf hfc hcosh (by omega : 1 ≤ N) hθlog hN hdiff
  have hatom := atomPairRe_weilTest_le_two_mul_integral_norm_sq (realWeilTestFn f hf hfc)
  have h1 :=
    two_forty_seven_three_hundredths_l2_add_secantNumerator_le_rightCellQuadratureDefect
      (realWeilTestFn f hf hfc) (by omega : 1 ≤ N) hN0 (fun n hn => hN n (by exact_mod_cast hn))
  have h2 :=
    neg_seven_four_eightieths_second_sub_seventy_one_geom_le_secantNumeratorCellDefect
      (realWeilTestFn f hf hfc) hint2 N
  have hamgm :=
    sqrt_spectralSecondMoment_mul_add_two_l2_le_add_forty_four_forty_fifths
      (realWeilTestFn f hf hfc)
  have hcomb :=
    one_seven_hundredth_l2_le_bochnerResolventEnergy_add_rightCellQuadratureDefect_of_spectralSecondMoment_le_forty_three
      (realWeilTestFn f hf hfc) hint2 hN3 hN0 (fun n hn => hN n (by exact_mod_cast hn)) hsec_bound
  have hθ_comb :
      (2800 : ℝ) * ((1 / 700) * (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2)) ≤
        (θ - 1) *
          (bochnerResolventEnergy
            (EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1) +
            rightCellQuadratureDefect (weilContinuumLogProfile (realWeilTestFn f hf hfc).1) N) :=
    mul_le_mul hθ_sub hcomb (by positivity) (by linarith)
  have hsinh_nonneg : 0 ≤ 2 * θ * sinhHalfMoment f ^ 2 := by positivity
  linarith

/-- **Unconditional `0 ≤ markovEnergy F` on the Nonnegative Log-Value Cone up to `45 * ∫ ‖F‖²`
(Upgraded from `(69 / 2) * ∫ ‖F‖² = 34.5 * ∫ ‖F‖²`, Deep into the `S / L > 69 / 2` Regime)**: -/
theorem markovEnergy_ofReal_nonneg_of_spectralSecondMoment_le_forty_five_of_cosh_zero_of_logValue_nonneg
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hcosh : coshHalfMoment f = 0)
    (hint2 : Integrable fun r : ℝ => ‖paperFT (realWeilTestFn f hf hfc).1 r‖ ^ 2 * (2 * r ^ 2))
    {N : ℕ} (hN3 : 3 ≤ N)
    (hN0 : EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log N) = 0 ∧
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log N) = 0)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log x) = 0 ∧
        EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log x) = 0)
    (hpos : ∀ n ∈ Finset.Icc 2 N, 0 ≤ logValue (realWeilTestFn f hf hfc).1 n)
    (hsec_bound : spectralSecondMoment (realWeilTestFn f hf hfc).1 ≤
      45 * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) :
    0 ≤ markovEnergy (realWeilTestFn f hf hfc).1 := by
  have hL_nonneg : 0 ≤ ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  let θ := max (max 1 (Real.log (N : ℝ))) 1201
  have hθlog : Real.log (N : ℝ) ≤ θ :=
    (le_max_right 1 (Real.log (N : ℝ))).trans (le_max_left _ _)
  have hθ_large : (1201 : ℝ) ≤ θ := le_max_right _ _
  have hθ_sub : (1200 : ℝ) ≤ θ - 1 := by linarith
  have hbase := one_hundredth_l2_add_theta_slope_quadrature_le_markovEnergy_of_cosh_zero
    0 hf hfc hcosh (by omega : 1 ≤ N) hθlog hN (fun n hn => by simpa [iteratedForwardDiff] using hpos n hn)
  have hatom := atomPairRe_weilTest_le_two_mul_integral_norm_sq (realWeilTestFn f hf hfc)
  have h1 :=
    twelve_sixty_one_fourteen_fortieths_l2_add_secantNumerator_le_rightCellQuadratureDefect_of_logValue_nonneg
      (realWeilTestFn f hf hfc) (by omega : 1 ≤ N) hN0 (fun n hn => hN n (by exact_mod_cast hn)) hpos
  have h2 :=
    neg_seven_four_eightieths_second_sub_seventy_one_geom_le_secantNumeratorCellDefect
      (realWeilTestFn f hf hfc) hint2 N
  have hamgm :=
    sqrt_spectralSecondMoment_mul_add_two_l2_le_add_forty_four_forty_fifths
      (realWeilTestFn f hf hfc)
  have hcomb :=
    one_three_hundredth_l2_le_bochnerResolventEnergy_add_rightCellQuadratureDefect_of_spectralSecondMoment_le_forty_five_of_logValue_nonneg
      (realWeilTestFn f hf hfc) hint2 hN3 hN0 (fun n hn => hN n (by exact_mod_cast hn)) hpos hsec_bound
  have hθ_comb :
      (1200 : ℝ) * ((1 / 300) * (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2)) ≤
        (θ - 1) *
          (bochnerResolventEnergy
            (EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1) +
            rightCellQuadratureDefect (weilContinuumLogProfile (realWeilTestFn f hf hfc).1) N) :=
    mul_le_mul hθ_sub hcomb (by positivity) (by linarith)
  have hsinh_nonneg : 0 ≤ 2 * θ * sinhHalfMoment f ^ 2 := by positivity
  linarith

/-- **The `43` Spectral Poincaré / Uncertainty Gap Law on the Primitive Hyperplane
(Upgraded from `33`)**: -/
theorem forty_three_l2_lt_spectralSecondMoment_of_cosh_zero_of_unitStep_nonneg
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hcosh : coshHalfMoment f = 0)
    (hint2 : Integrable fun r : ℝ => ‖paperFT (realWeilTestFn f hf hfc).1 r‖ ^ 2 * (2 * r ^ 2))
    {N : ℕ} (hN3 : 3 ≤ N)
    (hN0 : EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log N) = 0 ∧
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log N) = 0)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log x) = 0 ∧
        EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log x) = 0)
    (hunit : 0 ≤ primeBlindCounterterm unitStepCountertermWeight (realWeilTestFn f hf hfc))
    (hpos_l2 : 0 < ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) :
    43 * (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) <
      spectralSecondMoment (realWeilTestFn f hf hfc).1 := by
  by_contra! hle
  have hcons :=
    unitStep_add_rightCellQuadratureDefect_add_bochnerResolventEnergy_add_sinh_sq_eq_zero_of_cosh_zero
      hf hfc hcosh (by omega : 1 ≤ N) hN
  have hcoerc :=
    one_seven_hundredth_l2_le_bochnerResolventEnergy_add_rightCellQuadratureDefect_of_spectralSecondMoment_le_forty_three
      (realWeilTestFn f hf hfc) hint2 hN3 hN0 (fun n hn => hN n (by exact_mod_cast hn)) hle
  have hsinh_nonneg : 0 ≤ 2 * sinhHalfMoment f ^ 2 := by positivity
  linarith

/-- **The `45` Spectral Poincaré / Uncertainty Gap Law on the Nonnegative Log-Value Cone
(Upgraded from `69 / 2 = 34.5`, `+10.5` Units into the `S / L > 69 / 2` Regime)**: -/
theorem forty_five_l2_lt_spectralSecondMoment_of_cosh_zero_of_logValue_nonneg
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hcosh : coshHalfMoment f = 0)
    (hint2 : Integrable fun r : ℝ => ‖paperFT (realWeilTestFn f hf hfc).1 r‖ ^ 2 * (2 * r ^ 2))
    {N : ℕ} (hN3 : 3 ≤ N)
    (hN0 : EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log N) = 0 ∧
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log N) = 0)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log x) = 0 ∧
        EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log x) = 0)
    (hpos : ∀ n ∈ Finset.Icc 2 N, 0 ≤ logValue (realWeilTestFn f hf hfc).1 n)
    (hpos_l2 : 0 < ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) :
    45 * (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) <
      spectralSecondMoment (realWeilTestFn f hf hfc).1 := by
  by_contra! hle
  have hcons :=
    unitStep_add_rightCellQuadratureDefect_add_bochnerResolventEnergy_add_sinh_sq_eq_zero_of_cosh_zero
      hf hfc hcosh (by omega : 1 ≤ N) hN
  have hcoerc :=
    one_three_hundredth_l2_le_bochnerResolventEnergy_add_rightCellQuadratureDefect_of_spectralSecondMoment_le_forty_five_of_logValue_nonneg
      (realWeilTestFn f hf hfc) hint2 hN3 hN0 (fun n hn => hN n (by exact_mod_cast hn)) hpos hle
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

/-- **The `45` Spectral Poincaré / Uncertainty Gap Law on the Prime-Blind Cone
(Upgraded from `69 / 2 = 34.5`, `+10.5` Units into the `S / L > 69 / 2` Regime)**: -/
theorem forty_five_l2_lt_spectralSecondMoment_of_cosh_zero_of_logVector_eq_zero
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hcosh : coshHalfMoment f = 0)
    (hint2 : Integrable fun r : ℝ => ‖paperFT (realWeilTestFn f hf hfc).1 r‖ ^ 2 * (2 * r ^ 2))
    {N : ℕ} (hN3 : 3 ≤ N)
    (hN0 : EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log N) = 0 ∧
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log N) = 0)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log x) = 0 ∧
        EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log x) = 0)
    (hblind : logVector (realWeilTestFn f hf hfc) = 0)
    (hpos_l2 : 0 < ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) :
    45 * (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) <
      spectralSecondMoment (realWeilTestFn f hf hfc).1 := by
  by_contra! hle
  have hcons :=
    unitStep_add_rightCellQuadratureDefect_add_bochnerResolventEnergy_add_sinh_sq_eq_zero_of_cosh_zero
      hf hfc hcosh (by omega : 1 ≤ N) hN
  have hcoerc :=
    one_three_hundredth_l2_le_bochnerResolventEnergy_add_rightCellQuadratureDefect_of_spectralSecondMoment_le_forty_five_of_logVector_eq_zero
      (realWeilTestFn f hf hfc) hblind hint2 hN3 hN0 (fun n hn => hN n (by exact_mod_cast hn)) hle
  have hunit_zero :
      primeBlindCounterterm unitStepCountertermWeight (realWeilTestFn f hf hfc) = 0 := by
    unfold primeBlindCounterterm
    rw [hblind, map_zero]
  have hsinh_nonneg : 0 ≤ 2 * sinhHalfMoment f ^ 2 := by positivity
  linarith

/-- **Cutoff-Free `43` Kinetic Spectral Gap on `WeilEvenPolarTestFn` (Upgraded from `33`)**: -/
theorem WeilEvenPolarTestFn.forty_three_l2_lt_spectralSecondMoment_of_unitStep_nonneg
    (g : WeilEvenPolarTestFn)
    (hint2 : Integrable fun r : ℝ => ‖paperFT g.1.1 r‖ ^ 2 * (2 * r ^ 2))
    (hunit : 0 ≤ primeBlindCounterterm unitStepCountertermWeight g.1)
    (hpos_l2 : 0 < ∫ u : ℝ, ‖g.1.1 u‖ ^ 2) :
    43 * (∫ u : ℝ, ‖g.1.1 u‖ ^ 2) < spectralSecondMoment g.1.1 := by
  by_contra! hle
  obtain ⟨N, hN3, hN0, hN⟩ := exists_support_cutoff_three_weilTest g.1
  have hN1 : 1 ≤ N := by omega
  have hcons :=
    WeilEvenPolarTestFn.unitStep_add_rightCellQuadratureDefect_add_bochnerResolventEnergy_eq_zero
      g hN1 hN
  have hcoerc :=
    one_seven_hundredth_l2_le_bochnerResolventEnergy_add_rightCellQuadratureDefect_of_spectralSecondMoment_le_forty_three
      g.1 hint2 hN3 hN0 (fun n hn => hN n (by exact_mod_cast hn)) hle
  linarith

/-- **Cutoff-Free `45` Kinetic Spectral Gap on `WeilEvenPolarTestFn` with Nonnegative Log-Values
(Upgraded from `69 / 2 = 34.5`)**: -/
theorem WeilEvenPolarTestFn.forty_five_l2_lt_spectralSecondMoment_of_logValue_nonneg
    (g : WeilEvenPolarTestFn)
    (hint2 : Integrable fun r : ℝ => ‖paperFT g.1.1 r‖ ^ 2 * (2 * r ^ 2))
    (hpos : ∀ n : ℕ, 2 ≤ n → 0 ≤ logValue g.1.1 n)
    (hpos_l2 : 0 < ∫ u : ℝ, ‖g.1.1 u‖ ^ 2) :
    45 * (∫ u : ℝ, ‖g.1.1 u‖ ^ 2) < spectralSecondMoment g.1.1 := by
  by_contra! hle
  obtain ⟨N, hN3, hN0, hN⟩ := exists_support_cutoff_three_weilTest g.1
  have hN1 : 1 ≤ N := by omega
  have hcons :=
    WeilEvenPolarTestFn.unitStep_add_rightCellQuadratureDefect_add_bochnerResolventEnergy_eq_zero
      g hN1 hN
  have hpos_Icc : ∀ n ∈ Finset.Icc 2 N, 0 ≤ logValue g.1.1 n :=
    fun n hn => hpos n (Finset.mem_Icc.mp hn).1
  have hcoerc :=
    one_three_hundredth_l2_le_bochnerResolventEnergy_add_rightCellQuadratureDefect_of_spectralSecondMoment_le_forty_five_of_logValue_nonneg
      g.1 hint2 hN3 hN0 (fun n hn => hN n (by exact_mod_cast hn)) hpos_Icc hle
  have hunit_nonneg : 0 ≤ primeBlindCounterterm unitStepCountertermWeight g.1 := by
    rw [primeBlindCounterterm_eq_sum_Icc unitStepCountertermWeight g.1
      (fun n hn => hN n (by exact_mod_cast hn))]
    refine Finset.sum_nonneg fun n hn => ?_
    have hn_mem := Finset.mem_Icc.mp hn
    unfold unitStepCountertermWeight
    rw [if_pos hn_mem.1]
    exact mul_nonneg zero_le_one (hpos n hn_mem.1)
  linarith

/-- **Cutoff-Free `45` Kinetic Spectral Gap on Prime-Blind `WeilEvenPolarTestFn` (`logVector g.1 = 0`)
(Upgraded from `69 / 2 = 34.5`, `+10.5` Units into the `S / L > 69 / 2` Regime)**: -/
theorem WeilEvenPolarTestFn.forty_five_l2_lt_spectralSecondMoment_of_logVector_eq_zero
    (g : WeilEvenPolarTestFn) (hblind : logVector g.1 = 0)
    (hint2 : Integrable fun r : ℝ => ‖paperFT g.1.1 r‖ ^ 2 * (2 * r ^ 2))
    (hpos_l2 : 0 < ∫ u : ℝ, ‖g.1.1 u‖ ^ 2) :
    45 * (∫ u : ℝ, ‖g.1.1 u‖ ^ 2) < spectralSecondMoment g.1.1 := by
  by_contra! hle
  obtain ⟨N, hN3, hN0, hN⟩ := exists_support_cutoff_three_weilTest g.1
  have hN1 : 1 ≤ N := by omega
  have hcons :=
    WeilEvenPolarTestFn.rightCellQuadratureDefect_add_bochnerResolventEnergy_eq_zero_of_logVector_eq_zero
      g hblind hN1 hN
  have hcoerc :=
    one_three_hundredth_l2_le_bochnerResolventEnergy_add_rightCellQuadratureDefect_of_spectralSecondMoment_le_forty_five_of_logVector_eq_zero
      g.1 hblind hint2 hN3 hN0 (fun n hn => hN n (by exact_mod_cast hn)) hle
  linarith

/-- **Cutoff-Free `45` Kinetic Spectral Gap on Prime-Blind `SmoothEvenPolarTestFn`**: -/
theorem SmoothEvenPolarTestFn.forty_five_l2_lt_spectralSecondMoment_of_logVector_eq_zero
    (f : SmoothEvenPolarTestFn) (hblind : logVector f.1.1 = 0)
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1.1.1 r‖ ^ 2 * (2 * r ^ 2))
    (hpos_l2 : 0 < ∫ u : ℝ, ‖f.1.1.1 u‖ ^ 2) :
    45 * (∫ u : ℝ, ‖f.1.1.1 u‖ ^ 2) < spectralSecondMoment f.1.1.1 :=
  WeilEvenPolarTestFn.forty_five_l2_lt_spectralSecondMoment_of_logVector_eq_zero
    f.1 hblind hint2 hpos_l2

/-- **Cutoff-Free `45` Kinetic Spectral Gap on Prime-Blind Real Primitive-Hyperplane Tests**: -/
theorem forty_five_l2_lt_spectralSecondMoment_of_cosh_zero_of_logVector_eq_zero_unconditional
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hcosh : coshHalfMoment f = 0)
    (hint2 : Integrable fun r : ℝ => ‖paperFT (realWeilTestFn f hf hfc).1 r‖ ^ 2 * (2 * r ^ 2))
    (hblind : logVector (realWeilTestFn f hf hfc) = 0)
    (hpos_l2 : 0 < ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) :
    45 * (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) <
      spectralSecondMoment (realWeilTestFn f hf hfc).1 := by
  obtain ⟨N, hN3, hN0, hN⟩ := exists_support_cutoff_three_weilTest (realWeilTestFn f hf hfc)
  exact forty_five_l2_lt_spectralSecondMoment_of_cosh_zero_of_logVector_eq_zero
    hf hfc hcosh hint2 hN3 hN0 hN hblind hpos_l2

/-- **Joint Single-Source Mixture Purification with `evenBlindMinimum` and the `45` Spectral Gap**: -/
theorem exists_single_smooth_blind_purification_with_forty_five_gap
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
        45 * (∫ x : ℝ, ‖f.1.1.1 x‖ ^ 2) < spectralSecondMoment f.1.1.1) := by
  obtain ⟨f, a, u, N, hN2, hf0, hfe, hmin, hcons, htail, _⟩ :=
    exists_single_smooth_blind_purification_with_clamped_conservation c hc hblind_c
  exact ⟨f, a, u, N, hN2, hf0, hfe, hmin, hcons, htail,
    fun hint2 hpos =>
      SmoothEvenPolarTestFn.forty_five_l2_lt_spectralSecondMoment_of_logVector_eq_zero
        f hf0 hint2 hpos⟩

end RHTower

end
