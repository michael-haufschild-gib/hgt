import GaloisForLFunctions.RHTower.XiThetaExplicitBounds
import GaloisForLFunctions.RHTower.XiEntireReal
import GaloisForLFunctions.RHTower.XiHadamardFactorization
import GaloisForLFunctions.RHTower.GammaSewnMobiusXiWardHardyTransport

/-!
# Certified central disc bounds for the centered Xi source

Pushing the certified strip bound `‖Λ₀‖ ≤ 2/5` through the affine weld
`xi(s) = s(s−1)/2·Λ₀(s) + ½` gives the explicit disc bound
`‖XiC z‖ ≤ 7/4` on `‖z‖ ≤ 2` and the center lower bound
`‖XiC 0‖ ≥ 9/20` — the two inputs of the Jensen counting step. -/

open Complex Real

namespace RHTower

noncomputable section

/-- Numeric strip bound for the completed source. -/
theorem norm_completedRiemannZeta₀_le_two_fifths {s : ℂ}
    (h1 : -(3 / 2) ≤ s.re) (h2 : s.re ≤ 5 / 2) :
    ‖completedRiemannZeta₀ s‖ ≤ 2 / 5 :=
  (norm_completedRiemannZeta₀_le h1 h2).trans stripConstant_le_two_fifths

/-- **Certified disc bound**: `‖XiC z‖ ≤ 7/4` for `‖z‖ ≤ 2`. -/
theorem norm_XiC_le_of_norm_le_two {z : ℂ} (hz : ‖z‖ ≤ 2) :
    ‖XiC z‖ ≤ 7 / 4 := by
  rw [XiC, xi]
  have hsre : ((1 / 2 : ℂ) + z * I).re = 1 / 2 - z.im := by
    simp [Complex.add_re, Complex.mul_re]
    ring
  have hzim : |z.im| ≤ 2 := (Complex.abs_im_le_norm z).trans hz
  have hstrip1 : -(3 / 2) ≤ ((1 / 2 : ℂ) + z * I).re := by
    rw [hsre]
    have := (abs_le.mp hzim).2
    linarith
  have hstrip2 : ((1 / 2 : ℂ) + z * I).re ≤ 5 / 2 := by
    rw [hsre]
    have := (abs_le.mp hzim).1
    linarith
  have hΛ := norm_completedRiemannZeta₀_le_two_fifths hstrip1 hstrip2
  have hs_norm : ‖(1 / 2 : ℂ) + z * I‖ ≤ 5 / 2 := by
    calc ‖(1 / 2 : ℂ) + z * I‖ ≤ ‖(1 / 2 : ℂ)‖ + ‖z * I‖ :=
          norm_add_le _ _
      _ = 1 / 2 + ‖z‖ := by
          rw [norm_mul, Complex.norm_I, mul_one]
          norm_num
      _ ≤ 5 / 2 := by linarith
  have hs1_norm : ‖(1 / 2 : ℂ) + z * I - 1‖ ≤ 5 / 2 := by
    have hrw : (1 / 2 : ℂ) + z * I - 1 = -(1 / 2 : ℂ) + z * I := by
      ring
    rw [hrw]
    calc ‖-(1 / 2 : ℂ) + z * I‖ ≤ ‖-(1 / 2 : ℂ)‖ + ‖z * I‖ :=
          norm_add_le _ _
      _ = 1 / 2 + ‖z‖ := by
          rw [norm_neg, norm_mul, Complex.norm_I, mul_one]
          norm_num
      _ ≤ 5 / 2 := by linarith
  calc ‖((1 / 2 : ℂ) + z * I) * ((1 / 2 : ℂ) + z * I - 1) / 2 *
      completedRiemannZeta₀ ((1 / 2 : ℂ) + z * I) + 1 / 2‖
      ≤ ‖((1 / 2 : ℂ) + z * I) * ((1 / 2 : ℂ) + z * I - 1) / 2 *
          completedRiemannZeta₀ ((1 / 2 : ℂ) + z * I)‖ +
        ‖(1 / 2 : ℂ)‖ := norm_add_le _ _
    _ ≤ 5 / 2 * (5 / 2) / 2 * (2 / 5) + 1 / 2 := by
        have hnorm : ‖((1 / 2 : ℂ) + z * I) *
            ((1 / 2 : ℂ) + z * I - 1) / 2 *
            completedRiemannZeta₀ ((1 / 2 : ℂ) + z * I)‖ =
            ‖(1 / 2 : ℂ) + z * I‖ * ‖(1 / 2 : ℂ) + z * I - 1‖ / 2 *
              ‖completedRiemannZeta₀ ((1 / 2 : ℂ) + z * I)‖ := by
          rw [norm_mul, norm_div, norm_mul]
          norm_num
        rw [hnorm]
        have h1 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
        rw [h1]
        have hΛ0 := norm_nonneg
          (completedRiemannZeta₀ ((1 / 2 : ℂ) + z * I))
        have hn2 := norm_nonneg ((1 / 2 : ℂ) + z * I - 1)
        have hAB : ‖(1 / 2 : ℂ) + z * I‖ *
            ‖(1 / 2 : ℂ) + z * I - 1‖ ≤ 5 / 2 * (5 / 2) :=
          mul_le_mul hs_norm hs1_norm hn2 (by norm_num)
        have hABd : ‖(1 / 2 : ℂ) + z * I‖ *
            ‖(1 / 2 : ℂ) + z * I - 1‖ / 2 ≤ 5 / 2 * (5 / 2) / 2 := by
          linarith
        have hABd0 : (0 : ℝ) ≤ ‖(1 / 2 : ℂ) + z * I‖ *
            ‖(1 / 2 : ℂ) + z * I - 1‖ / 2 := by positivity
        have hfin := mul_le_mul hABd hΛ hΛ0 (by norm_num :
          (0 : ℝ) ≤ 5 / 2 * (5 / 2) / 2)
        linarith
    _ ≤ 7 / 4 := by norm_num

/-- **Certified center lower bound**: `‖XiC 0‖ ≥ 9/20`. -/
theorem norm_XiC_zero_ge : 9 / 20 ≤ ‖XiC 0‖ := by
  rw [XiC, xi]
  have harg : (1 / 2 : ℂ) + 0 * I = 1 / 2 := by ring
  rw [harg]
  have hΛ : ‖completedRiemannZeta₀ (1 / 2 : ℂ)‖ ≤ 2 / 5 := by
    apply norm_completedRiemannZeta₀_le_two_fifths
    · norm_num
    · norm_num
  have hco : ‖(1 / 2 : ℂ) * ((1 / 2 : ℂ) - 1) / 2 *
      completedRiemannZeta₀ (1 / 2 : ℂ)‖ ≤ 1 / 20 := by
    have hnorm : ‖(1 / 2 : ℂ) * ((1 / 2 : ℂ) - 1) / 2 *
        completedRiemannZeta₀ (1 / 2 : ℂ)‖ =
        ‖(1 / 2 : ℂ) * ((1 / 2 : ℂ) - 1) / 2‖ *
          ‖completedRiemannZeta₀ (1 / 2 : ℂ)‖ := norm_mul _ _
    rw [hnorm]
    have hc : ‖(1 / 2 : ℂ) * ((1 / 2 : ℂ) - 1) / 2‖ = 1 / 8 := by
      have : (1 / 2 : ℂ) * ((1 / 2 : ℂ) - 1) / 2 = -(1 / 8 : ℂ) := by
        ring
      rw [this, norm_neg]
      norm_num
    rw [hc]
    have hΛ0 := norm_nonneg (completedRiemannZeta₀ (1 / 2 : ℂ))
    nlinarith [hΛ]
  have htri : ‖(1 / 2 : ℂ)‖ ≤
      ‖(1 / 2 : ℂ) * ((1 / 2 : ℂ) - 1) / 2 *
        completedRiemannZeta₀ (1 / 2 : ℂ) + 1 / 2‖ +
      ‖(1 / 2 : ℂ) * ((1 / 2 : ℂ) - 1) / 2 *
        completedRiemannZeta₀ (1 / 2 : ℂ)‖ := by
    have h := norm_add_le
      ((1 / 2 : ℂ) * ((1 / 2 : ℂ) - 1) / 2 *
        completedRiemannZeta₀ (1 / 2 : ℂ) + 1 / 2)
      (-((1 / 2 : ℂ) * ((1 / 2 : ℂ) - 1) / 2 *
        completedRiemannZeta₀ (1 / 2 : ℂ)))
    rw [norm_neg] at h
    calc ‖(1 / 2 : ℂ)‖ = ‖((1 / 2 : ℂ) * ((1 / 2 : ℂ) - 1) / 2 *
          completedRiemannZeta₀ (1 / 2 : ℂ) + 1 / 2) +
          -((1 / 2 : ℂ) * ((1 / 2 : ℂ) - 1) / 2 *
            completedRiemannZeta₀ (1 / 2 : ℂ))‖ := by
          congr 1
          ring
      _ ≤ _ := h
  have h12 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  rw [h12] at htri
  linarith

/-- **CERTIFIED CENTRAL ZERO-FREE UNIT DISC**: `XiC` has no zero in the
closed unit ball.  Jensen's inequality with the certified disc constants
allows total divisor mass at most one there (`log(35/9) < log 4`), and
evenness would force any zero to appear in a pair. -/
theorem XiC_ne_zero_of_norm_le_one {z : ℂ} (hz : ‖z‖ ≤ 1) :
    XiC z ≠ 0 := by
  intro hzero
  have hXiC0 : XiC 0 ≠ 0 := by
    intro h
    have h9 := norm_XiC_zero_ge
    rw [h] at h9
    norm_num at h9
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at hzero
    exact hXiC0 hzero
  have hana : AnalyticOnNhd ℂ XiC (Metric.closedBall 0 |(2 : ℝ)|) :=
    XiC_analytic.mono (Set.subset_univ _)
  have hbound : ∀ w ∈ Metric.sphere (0 : ℂ) |(2 : ℝ)|,
      ‖XiC w‖ ≤ 7 / 4 := by
    intro w hw
    apply norm_XiC_le_of_norm_le_two
    have hw2 : ‖w‖ = 2 := by
      have h := Metric.mem_sphere.mp hw
      rw [dist_zero_right] at h
      rw [h]
      norm_num
    linarith [hw2.le]
  have hjensen := AnalyticOnNhd.sum_divisor_le (c := (0 : ℂ))
    (r := (1 : ℝ)) (R := (2 : ℝ)) (M := (7 / 4 : ℝ)) (f := XiC)
    (by norm_num) (by norm_num) (by norm_num) hana hXiC0 hbound
  have hnorm0pos : (0 : ℝ) < ‖XiC 0‖ := norm_pos_iff.mpr hXiC0
  have hrhs : Real.log ((7 / 4) / ‖XiC 0‖) /
      Real.log ((2 : ℝ) / 1) < 2 := by
    have h9 := norm_XiC_zero_ge
    have h1 : (7 / 4 : ℝ) / ‖XiC 0‖ ≤ 35 / 9 := by
      calc (7 / 4 : ℝ) / ‖XiC 0‖ ≤ (7 / 4) / (9 / 20) :=
            div_le_div_of_nonneg_left (by norm_num) (by norm_num) h9
        _ = 35 / 9 := by norm_num
    have hpos : (0 : ℝ) < (7 / 4) / ‖XiC 0‖ := by positivity
    have h2 : Real.log ((7 / 4 : ℝ) / ‖XiC 0‖) ≤ Real.log (35 / 9) :=
      Real.log_le_log hpos h1
    have h3 : Real.log (35 / 9 : ℝ) < Real.log 4 :=
      Real.log_lt_log (by norm_num) (by norm_num)
    have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 from by norm_num, Real.log_pow]
      norm_num
    have h5 : ((2 : ℝ) / 1) = 2 := by norm_num
    rw [h5, div_lt_iff₀ (Real.log_pos (by norm_num))]
    linarith
  have hlt := lt_of_le_of_lt hjensen hrhs
  have hana1 : AnalyticOnNhd ℂ XiC (Metric.closedBall 0 |(1 : ℝ)|) :=
    XiC_analytic.mono (Set.subset_univ _)
  have horder_ne_top : ∀ w : ℂ, analyticOrderAt XiC w ≠ ⊤ := by
    intro w htop
    rw [analyticOrderAt_eq_top] at htop
    have h := XiC_analytic.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (Set.mem_univ w) htop
    exact hXiC0 (h (Set.mem_univ 0))
  have hdiv_at : ∀ w : ℂ, w ∈ Metric.closedBall (0 : ℂ) |(1 : ℝ)| →
      XiC w = 0 →
      1 ≤ MeromorphicOn.divisor XiC
        (Metric.closedBall 0 |(1 : ℝ)|) w := by
    intro w hw hw0
    rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hana1 hw]
    have hne0 : analyticOrderAt XiC w ≠ 0 := by
      intro h0
      exact ((hana1 w hw).analyticOrderAt_eq_zero.mp h0) hw0
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (horder_ne_top w)
    rw [← hn, ENat.map_coe, WithTop.untop₀_coe]
    have hn0 : n ≠ 0 := by
      intro h
      rw [h] at hn
      exact hne0 (by exact_mod_cast hn.symm)
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
  have hzmem : z ∈ Metric.closedBall (0 : ℂ) |(1 : ℝ)| := by
    rw [Metric.mem_closedBall, dist_zero_right]
    calc ‖z‖ ≤ 1 := hz
      _ ≤ |(1 : ℝ)| := by norm_num
  have hnzmem : -z ∈ Metric.closedBall (0 : ℂ) |(1 : ℝ)| := by
    rw [Metric.mem_closedBall, dist_zero_right, norm_neg]
    calc ‖z‖ ≤ 1 := hz
      _ ≤ |(1 : ℝ)| := by norm_num
  have hdivz := hdiv_at z hzmem hzero
  have hdivnz := hdiv_at (-z) hnzmem (by rw [XiC_even]; exact hzero)
  have hzne : z ≠ -z := by
    intro h
    apply hz0
    have h2 : z + z = 0 := by
      nth_rewrite 2 [h]
      ring
    have h3 : (2 : ℂ) * z = 0 := by
      rw [two_mul]
      exact h2
    rcases mul_eq_zero.mp h3 with h4 | h4
    · norm_num at h4
    · exact h4
  have hfin := (MeromorphicOn.divisor XiC
    (Metric.closedBall (0 : ℂ) |(1 : ℝ)|)).finiteSupport
    (isCompact_closedBall 0 |(1 : ℝ)|)
  have hsum_ge : (2 : ℤ) ≤ ∑ᶠ u, MeromorphicOn.divisor XiC
      (Metric.closedBall (0 : ℂ) |(1 : ℝ)|) u := by
    rw [finsum_eq_sum _ hfin]
    have hzin : z ∈ hfin.toFinset := by
      rw [Set.Finite.mem_toFinset, Function.mem_support]
      omega
    have hnzin : -z ∈ hfin.toFinset := by
      rw [Set.Finite.mem_toFinset, Function.mem_support]
      omega
    have hsub : ({z, -z} : Finset ℂ) ⊆ hfin.toFinset := by
      intro x hx
      rcases Finset.mem_insert.mp hx with h | h
      · rw [h]; exact hzin
      · rw [Finset.mem_singleton.mp h]; exact hnzin
    calc (2 : ℤ)
        ≤ ∑ i ∈ ({z, -z} : Finset ℂ), MeromorphicOn.divisor XiC
            (Metric.closedBall (0 : ℂ) |(1 : ℝ)|) i := by
          rw [Finset.sum_insert (by
            rw [Finset.mem_singleton]
            exact hzne), Finset.sum_singleton]
          linarith [hdivz, hdivnz]
      _ ≤ ∑ i ∈ hfin.toFinset, MeromorphicOn.divisor XiC
            (Metric.closedBall (0 : ℂ) |(1 : ℝ)|) i :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun i _ _ => MeromorphicOn.AnalyticOnNhd.divisor_nonneg hana1 i)
  have hcast : (2 : ℝ) ≤ ((∑ᶠ u, MeromorphicOn.divisor XiC
      (Metric.closedBall (0 : ℂ) |(1 : ℝ)|) u : ℤ) : ℝ) := by
    exact_mod_cast hsum_ge
  linarith [hlt, hcast]

/-- **UNCONDITIONAL HEIGHT FLOOR**: every strict-right (off-critical) zero
has squared height above `3/4`: the certified central zero-free unit disc
combined with critical-strip confinement `|Re λ| < ½`. -/
theorem xiRightUpper_height_sq_gt (q : XiRightUpperZeroCopy) :
    3 / 4 < ((xiRightCenteredZero q.1).im) ^ 2 := by
  have hlt := abs_xiRightCenteredZero_re_lt_half q.1
  have hzero : XiC (xiSpectralPoint q.1.1) = 0 :=
    (XiC_eq_zero_iff_exists_xiZeroCopy _).mpr ⟨q.1.1, rfl⟩
  have hpt : ‖xiRightCenteredZero q.1‖ = ‖xiSpectralPoint q.1.1‖ := by
    rw [show xiRightCenteredZero q.1 =
      I * xiSpectralPoint q.1.1 from rfl, norm_mul, Complex.norm_I,
      one_mul]
  have hdisc : 1 < ‖xiRightCenteredZero q.1‖ := by
    by_contra hle
    push Not at hle
    have hnorm : ‖xiSpectralPoint q.1.1‖ ≤ 1 := by
      rw [← hpt]
      exact hle
    exact XiC_ne_zero_of_norm_le_one hnorm hzero
  have h1 : 1 < ‖xiRightCenteredZero q.1‖ ^ 2 := by
    nlinarith [hdisc, norm_nonneg (xiRightCenteredZero q.1)]
  have h2 : Complex.normSq (xiRightCenteredZero q.1) =
      ‖xiRightCenteredZero q.1‖ ^ 2 := Complex.normSq_eq_norm_sq _
  rw [← h2, Complex.normSq_apply] at h1
  have habs := abs_lt.mp hlt
  nlinarith [habs.1, habs.2, h1]

private theorem xi_eq_mul_completedRiemannZeta' {s : ℂ} (hs0 : s ≠ 0)
    (hs1 : s ≠ 1) :
    xi s = s * (s - 1) / 2 * completedRiemannZeta s := by
  rw [xi, completedRiemannZeta_eq]
  have h1s : (1 : ℂ) - s ≠ 0 := by
    intro h
    exact hs1 (by linear_combination -h)
  field_simp
  ring

/-- **UNCONDITIONAL CENTRAL ZERO-FREE DISC FOR ζ**: the Riemann zeta
function has no zero within distance `1` of the central point `½` (in the
right half-plane, away from the pole).  Machine-checked from the theta
series through Jensen's inequality, with no numerics and no zero-location
input. -/
theorem riemannZeta_ne_zero_of_dist_le_one {s : ℂ} (hs0 : s ≠ 0)
    (hs1 : s ≠ 1) (hre : 0 < s.re) (hd : ‖s - 1 / 2‖ ≤ 1) :
    riemannZeta s ≠ 0 := by
  intro hzero
  have hΛ : completedRiemannZeta s = 0 := by
    have hζ := riemannZeta_def_of_ne_zero hs0
    rw [hzero] at hζ
    have hG : Complex.Gammaℝ s ≠ 0 :=
      Complex.Gammaℝ_ne_zero_of_re_pos hre
    have h := hζ.symm
    rw [div_eq_zero_iff] at h
    rcases h with h | h
    · exact h
    · exact absurd h hG
  have hxi : xi s = 0 := by
    rw [xi_eq_mul_completedRiemannZeta' hs0 hs1, hΛ, mul_zero]
  have hXiC : XiC (-I * (s - 1 / 2)) = 0 := by
    rw [XiC]
    have harg : (1 / 2 : ℂ) + -I * (s - 1 / 2) * I = s := by
      rw [show (-I * (s - 1 / 2) * I) = -(I * I) * (s - 1 / 2) from by
        ring, I_mul_I]
      ring
    rw [harg]
    exact hxi
  have hnorm : ‖-I * (s - 1 / 2)‖ ≤ 1 := by
    rw [norm_mul, norm_neg, Complex.norm_I, one_mul]
    exact hd
  exact XiC_ne_zero_of_norm_le_one hnorm hXiC

end

end RHTower
