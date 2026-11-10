import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Tactic
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# The first nonzero jet of an analytic phase profile

A nonconstant analytic profile which is unimodular on the real unit
interval starts with a nonzero imaginary coefficient. Its exact
analytic factorization gives a uniform remainder on the complex unit
disc, hence a sharp shifted prime decay exponent.
-/

open Complex Filter Topology Metric Set
noncomputable section
set_option autoImplicit false
namespace GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations

/-- A continuous leading factor of a unit-modulus arc is imaginary at its origin. -/
theorem firstUnitCoefficient_re_eq_zero {G : ℂ → ℂ} {m : ℕ} (hm : 0 < m)
    (hG : ContinuousAt G 0)
    (hunit : ∀ x : ℝ, x ∈ Icc 0 1 → ‖1 + (x : ℂ) ^ m * G (x : ℂ)‖ = 1) :
    (G 0).re = 0 := by
  have hreal (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) :
      2 * (G (x : ℂ)).re + x ^ m * ‖G (x : ℂ)‖ ^ 2 = 0 := by
    have hn : Complex.normSq (1 + (x : ℂ) ^ m * G (x : ℂ)) = 1 := by
      rw [Complex.normSq_eq_norm_sq, hunit x ⟨hx.le, hx1⟩]
      norm_num
    have hgn : ‖G (x : ℂ)‖ ^ 2 = (G (x : ℂ)).re ^ 2 + (G (x : ℂ)).im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      ring
    rw [← Complex.ofReal_pow] at hn
    simp only [Complex.normSq_apply, Complex.add_re, Complex.one_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.add_im,
      Complex.one_im, Complex.mul_im, zero_add] at hn
    have hp : x ^ m * (2 * (G (x : ℂ)).re + x ^ m * ‖G (x : ℂ)‖ ^ 2) = 0 := by
      rw [hgn]
      nlinarith only [hn]
    exact (mul_eq_zero.mp hp).resolve_left (pow_ne_zero m hx.ne')
  have hx : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℂ)) :=
    (Complex.continuous_ofReal.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have hg := hG.tendsto.comp hx
  have hr := Complex.continuous_re.continuousAt.tendsto.comp hg
  have ht : Tendsto (fun x : ℝ => x) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    (continuous_id.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have hp : Tendsto (fun x : ℝ => x ^ m) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa only [zero_pow hm.ne'] using ht.pow m
  have hlim : Tendsto (fun x : ℝ => 2 * (G (x : ℂ)).re + x ^ m * ‖G (x : ℂ)‖ ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (2 * (G 0).re)) := by
    simpa only [Function.comp_apply, zero_mul, add_zero] using (hr.const_mul 2).add (hp.mul (hg.norm.pow 2))
  have he : ∀ᶠ x : ℝ in 𝓝[>] 0,
      2 * (G (x : ℂ)).re + x ^ m * ‖G (x : ℂ)‖ ^ 2 = 0 := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (gt_mem_nhds (zero_lt_one : (0 : ℝ) < 1))] with x hx hx1
    exact hreal x hx hx1.le
  have hz : 2 * (G 0).re = 0 :=
    tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (by
      filter_upwards [he] with x hx
      exact hx.symm))
  linarith only [hz]


/-- The canonical Taylor series of the deviation from the trivial phase. -/
def smoothingTaylorSeries (Φ : ℂ → ℂ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  cauchyPowerSeries (fun z => Φ z - 1) 0 1

/-- Taylor coefficients include the zero constant coefficient of a normalized profile. -/
def smoothingTaylorCoefficient (Φ : ℂ → ℂ) (n : ℕ) : ℂ :=
  (smoothingTaylorSeries Φ).coeff n

/-- The canonical series converges throughout any larger analytic profile disc. -/
theorem smoothingTaylor_hasFPowerSeriesOnBall {Φ : ℂ → ℂ} {R : NNReal} (hR : 1 < (R : ℝ))
    (hΦ : AnalyticOnNhd ℂ Φ (closedBall 0 R)) :
    HasFPowerSeriesOnBall (fun z => Φ z - 1) (smoothingTaylorSeries Φ) 0 R := by
  have hF : AnalyticOnNhd ℂ (fun z => Φ z - 1) (closedBall 0 R) := hΦ.sub analyticOnNhd_const
  have hRp : 0 < R := by exact_mod_cast (zero_lt_one.trans hR)
  have hlarge := hF.differentiableOn.hasFPowerSeriesOnBall hRp
  have hsmall : HasFPowerSeriesOnBall (fun z => Φ z - 1)
      (smoothingTaylorSeries Φ) 0 (1 : ENNReal) :=
    (hF.mono (Metric.closedBall_subset_closedBall hR.le)).differentiableOn.hasFPowerSeriesOnBall
      (R := (1 : NNReal)) zero_lt_one
  have he := hsmall.hasFPowerSeriesAt.eq_formalMultilinearSeries hlarge.hasFPowerSeriesAt
  rw [he]
  exact hlarge

theorem smoothingTaylorCoefficient_zero {Φ : ℂ → ℂ} {R : NNReal} (hR : 1 < (R : ℝ))
    (hΦ : AnalyticOnNhd ℂ Φ (closedBall 0 R)) (h0 : Φ 0 = 1) :
    smoothingTaylorCoefficient Φ 0 = 0 := by
  have hp := smoothingTaylor_hasFPowerSeriesOnBall hR hΦ
  have hh := hp.hasFPowerSeriesAt.coeff_zero (1 : Fin 0 → ℂ)
  change smoothingTaylorCoefficient Φ 0 = Φ 0 - 1 at hh
  simpa only [h0, sub_self] using hh

/-- Absolute Taylor convergence is valid on the closed unit disc, including its endpoint. -/
theorem smoothingTaylor_hasSum {Φ : ℂ → ℂ} {R : NNReal} (hR : 1 < (R : ℝ))
    (hΦ : AnalyticOnNhd ℂ Φ (closedBall 0 R)) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    HasSum (fun n : ℕ => smoothingTaylorCoefficient Φ n * z ^ n) (Φ z - 1) := by
  have hp := smoothingTaylor_hasFPowerSeriesOnBall hR hΦ
  have hmem : z ∈ Metric.eball (0 : ℂ) R := by
    rw [Metric.eball_coe, Metric.mem_ball, dist_zero_right]
    exact hz.trans_lt hR
  simpa only [FormalMultilinearSeries.apply_eq_pow_smul_coeff, smul_eq_mul,
    smoothingTaylorCoefficient, zero_add, mul_comm] using hp.hasSum hmem

theorem summable_norm_smoothingTaylorCoefficient {Φ : ℂ → ℂ} {R : NNReal} (hR : 1 < (R : ℝ))
    (hΦ : AnalyticOnNhd ℂ Φ (closedBall 0 R)) :
    Summable (fun n : ℕ => ‖smoothingTaylorCoefficient Φ n‖) := by
  have hp := smoothingTaylor_hasFPowerSeriesOnBall hR hΦ
  have hmem : (1 : ℂ) ∈ Metric.eball 0 (smoothingTaylorSeries Φ).radius := by
    apply Metric.eball_subset_eball hp.r_le
    rw [Metric.eball_coe, Metric.mem_ball, dist_zero_right, norm_one]
    exact hR
  simpa only [FormalMultilinearSeries.apply_eq_pow_smul_coeff, one_pow, one_smul,
    smoothingTaylorCoefficient] using (smoothingTaylorSeries Φ).summable_norm_apply hmem

/-- A larger Taylor disc controls the linear weight needed for shifted prime logarithms. -/
theorem summable_smoothingTaylorCoefficient_weight {Φ : ℂ → ℂ} {R : NNReal} (hR : 1 < (R : ℝ))
    (hΦ : AnalyticOnNhd ℂ Φ (closedBall 0 R)) (C : ℝ) :
    Summable (fun n : ℕ => ‖smoothingTaylorCoefficient Φ n‖ * (C + (n : ℝ) + 1)) := by
  obtain ⟨ρ, hρ1, hρR⟩ := exists_between hR
  have hρ0 : 0 < ρ := zero_lt_one.trans hρ1
  have hδ : 0 < ρ - 1 := sub_pos.mpr hρ1
  have hp := smoothingTaylor_hasFPowerSeriesOnBall hR hΦ
  have hmem : (ρ : ℂ) ∈ Metric.eball 0 (smoothingTaylorSeries Φ).radius := by
    apply Metric.eball_subset_eball hp.r_le
    rw [Metric.eball_coe, Metric.mem_ball, dist_zero_right, norm_real, Real.norm_eq_abs, abs_of_pos hρ0]
    exact hρR
  have hs : Summable (fun n : ℕ => ‖smoothingTaylorCoefficient Φ n‖ * ρ ^ n) := by
    simpa only [FormalMultilinearSeries.apply_eq_pow_smul_coeff, norm_smul, norm_pow,
      norm_real, Real.norm_eq_abs, abs_of_pos hρ0, smoothingTaylorCoefficient, mul_comm] using
      (smoothingTaylorSeries Φ).summable_norm_apply hmem
  have hBern (n : ℕ) : 1 + (n : ℝ) * (ρ - 1) ≤ ρ ^ n := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hmul := mul_le_mul_of_nonneg_right ih hρ0.le
      have hnon := mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) (sq_nonneg (ρ - 1))
      rw [pow_succ, Nat.cast_add, Nat.cast_one]
      nlinarith only [hmul, hnon]
  let B := 1 / (ρ - 1) + 1
  have hweight (n : ℕ) : (n : ℝ) + 1 ≤ B * ρ ^ n := by
    have hn : (n : ℝ) ≤ ρ ^ n / (ρ - 1) :=
      (le_div_iff₀ hδ).mpr (by linarith only [hBern n])
    have h1 : 1 ≤ ρ ^ n :=
      (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg n) hδ.le)).trans (hBern n)
    calc
      _ ≤ ρ ^ n / (ρ - 1) + ρ ^ n := add_le_add hn h1
      _ = _ := by dsimp [B]; ring
  have hw : Summable (fun n : ℕ => ‖smoothingTaylorCoefficient Φ n‖ * ((n : ℝ) + 1)) := by
    apply (hs.mul_left B).of_nonneg_of_le (fun n => by positivity)
    intro n
    exact (mul_le_mul_of_nonneg_left (hweight n) (norm_nonneg _)).trans_eq (by ring)
  have hsum := ((summable_norm_smoothingTaylorCoefficient hR hΦ).mul_left C).add hw
  refine hsum.congr (fun n => ?_)
  ring

/-- The total nonconstant coefficient mass is minus two at a Liouville endpoint. -/
theorem tsum_smoothingTaylorCoefficient {Φ : ℂ → ℂ} {R : NNReal} (hR : 1 < (R : ℝ))
    (hΦ : AnalyticOnNhd ℂ Φ (closedBall 0 R)) (h1 : Φ 1 = -1) :
    (∑' n : ℕ, smoothingTaylorCoefficient Φ n) = -2 := by
  have hh := (smoothingTaylor_hasSum hR hΦ (z := 1) (by simp)).tsum_eq
  simpa only [one_pow, mul_one, h1, show (-1 : ℂ) - 1 = -2 by ring] using hh

/-- The first nonzero phase coefficient and its next-order remainder are derived from analyticity. -/
theorem analyticPhase_first_jet {Φ : ℂ → ℂ} {R : NNReal} (hR : 1 < (R : ℝ))
    (hΦ : AnalyticOnNhd ℂ Φ (closedBall 0 R)) (h0 : Φ 0 = 1) (h1 : Φ 1 = -1)
    (hunit : ∀ x : ℝ, x ∈ Icc 0 1 → ‖Φ (x : ℂ)‖ = 1) :
    ∃ m : ℕ, 0 < m ∧ ∃ b : ℝ, b ≠ 0 ∧ ∃ G : ℂ → ℂ,
      AnalyticOnNhd ℂ G (closedBall 0 R) ∧ G 0 = (b : ℂ) * I ∧
      (∀ z : ℂ, Φ z - 1 = z ^ m * G z) ∧
      smoothingTaylorCoefficient Φ m = (b : ℂ) * I ∧
      (∀ k < m, smoothingTaylorCoefficient Φ k = 0) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, ‖z‖ ≤ 1 →
        ‖Φ z - 1 - (b : ℂ) * I * z ^ m‖ ≤ C * ‖z‖ ^ (m + 1) := by
  let F : ℂ → ℂ := fun z => Φ z - 1
  let p := smoothingTaylorSeries Φ
  have hp : HasFPowerSeriesOnBall F p 0 R := smoothingTaylor_hasFPowerSeriesOnBall hR hΦ
  have hpn : p ≠ 0 := by
    intro hp0
    have hmem : (1 : ℂ) ∈ Metric.eball 0 R := by
      rw [Metric.eball_coe, Metric.mem_ball, dist_zero_right, norm_one]
      exact hR
    have he := (hp.hasSum hmem).tsum_eq
    norm_num [hp0, F, h1] at he
  let G : ℂ → ℂ := (Function.swap dslope 0)^[p.order] F
  have hG0 : AnalyticAt ℂ G 0 :=
    (hp.hasFPowerSeriesAt.has_fpower_series_iterate_dslope_fslope p.order).analyticAt
  have hGn : G 0 ≠ 0 := hp.hasFPowerSeriesAt.iterate_dslope_fslope_ne_zero hpn
  have hfac (z : ℂ) : Φ z - 1 = z ^ p.order * G z := by
    simpa only [sub_zero, smul_eq_mul] using hp.hasFPowerSeriesAt.eq_pow_order_mul_iterate_dslope z
  have hm : 0 < p.order := by
    by_contra hnot
    have hm0 : p.order = 0 := Nat.eq_zero_of_not_pos hnot
    have he := hfac 0
    rw [h0, sub_self, hm0, pow_zero, one_mul] at he
    exact hGn he.symm
  have hGa : AnalyticOnNhd ℂ G (closedBall 0 R) := by
    intro z hz
    by_cases hz0 : z = 0
    · subst z
      exact hG0
    have hquot : AnalyticAt ℂ (fun w => (Φ w - 1) / w ^ p.order) z :=
      ((hΦ z hz).sub analyticAt_const).div (analyticAt_id.pow p.order) (pow_ne_zero _ hz0)
    apply hquot.congr
    filter_upwards [continuous_id.continuousAt.eventually_ne hz0] with w hw
    apply (div_eq_iff (pow_ne_zero p.order hw)).mpr
    change Φ w - 1 = G w * w ^ p.order
    rw [hfac, mul_comm]
  have hRe : (G 0).re = 0 := firstUnitCoefficient_re_eq_zero hm hG0.continuousAt (by
    intro x hx
    have he : 1 + (x : ℂ) ^ p.order * G (x : ℂ) = Φ (x : ℂ) := by
      rw [← hfac]
      ring
    rw [he]
    exact hunit x hx)
  have hb : (G 0).im ≠ 0 := by
    intro hi
    apply hGn
    exact Complex.ext hRe hi
  have hcb : G 0 = ((G 0).im : ℂ) * I := by
    apply Complex.ext <;> simp [hRe]
  have hGunit : ContinuousOn G (closedBall (0 : ℂ) 1) := hGa.continuousOn.mono
    (Metric.closedBall_subset_closedBall hR.le)
  have hHu : ContinuousOn (dslope G 0) (closedBall (0 : ℂ) 1) :=
    (continuousOn_dslope (mem_of_superset (Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)
      Metric.ball_subset_closedBall)).mpr ⟨hGunit, hG0.differentiableAt⟩
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn hHu
  have hcoeff : smoothingTaylorCoefficient Φ p.order = G 0 := by
    have hh := (hp.hasFPowerSeriesAt.has_fpower_series_iterate_dslope_fslope p.order).coeff_zero
      (1 : Fin 0 → ℂ)
    change (FormalMultilinearSeries.fslope^[p.order] p).coeff 0 = G 0 at hh
    change p.coeff p.order = G 0
    simpa only [FormalMultilinearSeries.coeff_iterate_fslope, zero_add] using hh
  have hbelow (k : ℕ) (hk : k < p.order) : smoothingTaylorCoefficient Φ k = 0 := by
    change p k (fun _ => 1) = 0
    rw [p.apply_eq_zero_of_lt_order hk]
    rfl
  refine ⟨p.order, hm, (G 0).im, hb, G, hGa, hcb, hfac, hcoeff.trans hcb, hbelow,
    max C 0, le_max_right _ _, ?_⟩
  intro z hz
  have hbound : ‖dslope G 0 z‖ ≤ max C 0 :=
    (hC z (by simpa only [Metric.mem_closedBall, dist_zero_right] using hz)).trans (le_max_left _ _)
  have he : Φ z - 1 - ((G 0).im : ℂ) * I * z ^ p.order =
      z ^ (p.order + 1) * dslope G 0 z := by
    have hd : z * dslope G 0 z = G z - G 0 := by
      simpa only [sub_zero, smul_eq_mul] using sub_smul_dslope G 0 z
    rw [← hcb, hfac, pow_succ]
    linear_combination -z ^ p.order * hd
  rw [he, norm_mul, norm_pow]
  exact (mul_le_mul_of_nonneg_left hbound (pow_nonneg (norm_nonneg z) _)).trans_eq (mul_comm _ _)

#print axioms summable_smoothingTaylorCoefficient_weight
#print axioms tsum_smoothingTaylorCoefficient
#print axioms firstUnitCoefficient_re_eq_zero
#print axioms analyticPhase_first_jet
end GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations
