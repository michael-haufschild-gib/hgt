import GaloisForLFunctions.RHTower.XiSliceGaussianTailCompensation
import GaloisForLFunctions.RHTower.XiSliceGaussianTailHeightBounds
import GaloisForLFunctions.RHTower.XiSliceGaussianTailWindowBounds

/-!
# A dense Gaussian background in the actual Xi divisor

At height `exp(u⁴)` and cutoff `u³`, the real quadratic tail coefficient
diverges while the fourth moment vanishes even after multiplication by its
square. Multiplicative compensation then converges to one uniformly on
complex discs whose physical radius grows linearly in `u`.
-/

open Filter Topology Complex
namespace RHTower
noncomputable section

/-- The real quadratic coefficient of the Xi tail at height `exp(u⁴)` and cutoff `u³`. -/
def xiSliceDenseGaussianCoefficient (u : ℝ) : ℝ :=
  (xiSliceGaussianTailQuadratic (Real.exp (u ^ 4))
    (xiSliceGaussianRadiusHead (Real.exp (u ^ 4)) (u ^ 3))).re

/-- The actual Xi product outside the cutoff `u³` about height `exp(u⁴)`. -/
def xiSliceDenseGaussianTail (u : ℝ) (z : ℂ) : ℂ :=
  xiSliceGaussianTail (Real.exp (u ^ 4))
    (xiSliceGaussianRadiusHead (Real.exp (u ^ 4)) (u ^ 3)) z

private def denseMomentConstant : ℝ := 4 * (3650 + 5 * (smallHeightCount : ℝ))

private theorem denseMomentConstant_pos : 0 < denseMomentConstant := by
  unfold denseMomentConstant
  positivity

private theorem dense_radius_tendsto : Tendsto (fun u : ℝ => u ^ 3) atTop atTop :=
  tendsto_pow_atTop (by decide : 3 ≠ 0)

private theorem dense_height_tendsto : Tendsto (fun u : ℝ => Real.exp (u ^ 4)) atTop atTop :=
  Real.tendsto_exp_atTop.comp (tendsto_pow_atTop (by decide : 4 ≠ 0))

private theorem eventually_dense_fourth_le :
    ∀ᶠ u : ℝ in atTop,
      xiSliceGaussianTailFourth (Real.exp (u ^ 4))
        (xiSliceGaussianRadiusHead (Real.exp (u ^ 4)) (u ^ 3)) ≤ denseMomentConstant / u ^ 2 := by
  filter_upwards [dense_height_tendsto.eventually_ge_atTop 4,
    dense_radius_tendsto.eventually_ge_atTop 3, eventually_gt_atTop (0 : ℝ)]
    with u ht hR hu
  have h := xiSliceGaussianTailFourth_le_log ht hR
  rw [Real.log_exp] at h
  refine h.trans_eq ?_
  change denseMomentConstant * u ^ 4 / (u ^ 3) ^ 2 = denseMomentConstant / u ^ 2
  field_simp [hu.ne']

private theorem eventually_dense_mass_upper :
    ∀ᶠ u : ℝ in atTop,
      xiSliceGaussianTailMass (Real.exp (u ^ 4))
        (xiSliceGaussianRadiusHead (Real.exp (u ^ 4)) (u ^ 3)) ≤ denseMomentConstant * u := by
  filter_upwards [dense_height_tendsto.eventually_ge_atTop 4,
    dense_radius_tendsto.eventually_ge_atTop 8, eventually_ge_atTop (1 : ℝ)]
    with u ht hR hu
  have hu0 : 0 < u := zero_lt_one.trans_le hu
  have hcube : 1 ≤ u ^ 3 := one_le_pow₀ hu
  have hsqrt : 1 ≤ Real.sqrt (u ^ 3) := (Real.one_le_sqrt).2 hcube
  have h := xiSliceGaussianTailMass_le_cutoff_bound ht hR
  rw [Real.log_exp] at h
  have heq : 4 * (480 * u ^ 4 + 240 + smallHeightCount) / u ^ 3 =
      1920 * u + (960 + 4 * smallHeightCount) / u ^ 3 := by
    field_simp [hu0.ne']
    ring
  rw [heq] at h
  have hrem : (960 + 4 * (smallHeightCount : ℝ)) / u ^ 3 ≤
      (960 + 4 * (smallHeightCount : ℝ)) * u := by
    calc
      _ ≤ 960 + 4 * (smallHeightCount : ℝ) := div_le_self (by positivity) hcube
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hu
  have hsrem : (640 : ℝ) / Real.sqrt (u ^ 3) ≤ 640 * u := by
    calc
      _ ≤ 640 := div_le_self (by norm_num) hsqrt
      _ ≤ _ := le_mul_of_one_le_right (by norm_num) hu
  have hconst : (3520 + 4 * (smallHeightCount : ℝ)) ≤ denseMomentConstant := by
    unfold denseMomentConstant
    nlinarith only [Nat.cast_nonneg (α := ℝ) smallHeightCount]
  have hconstu := mul_le_mul_of_nonneg_right hconst hu0.le
  linarith only [h, hrem, hsrem, hconstu]

private theorem eventually_dense_fourth_le_fifth :
    ∀ᶠ u : ℝ in atTop,
      xiSliceGaussianTailFourth (Real.exp (u ^ 4))
        (xiSliceGaussianRadiusHead (Real.exp (u ^ 4)) (u ^ 3)) ≤ denseMomentConstant / u ^ 5 := by
  filter_upwards [eventually_dense_mass_upper, eventually_gt_atTop (0 : ℝ)] with u hmass hu
  have hR : 0 < u ^ 3 := pow_pos hu 3
  calc
    _ ≤ xiSliceGaussianTailMass (Real.exp (u ^ 4))
        (xiSliceGaussianRadiusHead (Real.exp (u ^ 4)) (u ^ 3)) / (u ^ 3) ^ 2 :=
      xiSliceGaussianTailFourth_le (Real.exp (u ^ 4)) hR
    _ ≤ denseMomentConstant * u / (u ^ 3) ^ 2 :=
      div_le_div_of_nonneg_right hmass (sq_nonneg _)
    _ = denseMomentConstant / u ^ 5 := by field_simp [hu.ne']

private theorem eventually_dense_mass_lower :
    ∀ᶠ u : ℝ in atTop, u / (100 * Real.pi) ≤
      xiSliceGaussianTailMass (Real.exp (u ^ 4))
        (xiSliceGaussianRadiusHead (Real.exp (u ^ 4)) (u ^ 3)) := by
  obtain ⟨T₀, R₀, _hT₀, _hR₀, hbound⟩ := exists_xiSliceGaussianTailMass_height_lower
  filter_upwards [dense_height_tendsto.eventually_ge_atTop T₀,
    dense_radius_tendsto.eventually_ge_atTop R₀, eventually_ge_atTop (4 : ℝ)]
    with u ht hR hu
  have hu0 : 0 < u := by linarith only [hu]
  have hcut : 4 * u ^ 3 ≤ Real.exp (u ^ 4) := by
    have h := mul_le_mul_of_nonneg_right hu (by positivity : 0 ≤ u ^ 3)
    have he := Real.add_one_le_exp (u ^ 4)
    nlinarith only [h, he]
  have h := hbound (Real.exp (u ^ 4)) (u ^ 3) ht hR hcut
  rw [Real.log_exp] at h
  have heq : u ^ 4 / (100 * Real.pi * u ^ 3) = u / (100 * Real.pi) := by
    field_simp [hu0.ne']
  simpa only [heq] using h

/-- The real Gaussian coefficient of the actual moving Xi tail diverges to infinity. -/
theorem tendsto_xiSliceDenseGaussianCoefficient_atTop :
    Tendsto xiSliceDenseGaussianCoefficient atTop atTop := by
  have hsmall : Tendsto (fun u : ℝ => denseMomentConstant / u ^ 2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by decide : 2 ≠ 0))
  refine tendsto_atTop.2 fun b => ?_
  filter_upwards [eventually_dense_mass_lower, eventually_dense_fourth_le,
    hsmall.eventually (gt_mem_nhds zero_lt_one),
    eventually_ge_atTop (100 * Real.pi * (b + 1))] with u hmass hfourth hsmallu hu
  have hlin : b + 1 ≤ u / (100 * Real.pi) := by
    apply (le_div_iff₀ (by positivity : 0 < 100 * Real.pi)).2
    nlinarith only [hu]
  have hdefect := (xiSliceGaussianTailTransverse_bounds (Real.exp (u ^ 4))
    (xiSliceGaussianRadiusHead (Real.exp (u ^ 4)) (u ^ 3))).2
  rw [xiSliceDenseGaussianCoefficient, xiSliceGaussianTailQuadratic_re_eq]
  linarith only [hlin, hmass, hfourth, hsmallu, hdefect]

/-- The fourth-moment error remains negligible after a square loss in the growing coefficient. -/
theorem tendsto_xiSliceDenseGaussianFourth_mul_coefficient_sq :
    Tendsto (fun u : ℝ =>
      xiSliceGaussianTailFourth (Real.exp (u ^ 4))
        (xiSliceGaussianRadiusHead (Real.exp (u ^ 4)) (u ^ 3)) *
          xiSliceDenseGaussianCoefficient u ^ 2) atTop (𝓝 0) := by
  have hbound : Tendsto (fun u : ℝ => denseMomentConstant ^ 3 / u ^ 3) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by decide : 3 ≠ 0))
  refine squeeze_zero' (Eventually.of_forall (fun u => mul_nonneg
    (tsum_nonneg (fun _ => sq_nonneg _)) (sq_nonneg _))) ?_ hbound
  filter_upwards [eventually_dense_mass_upper, eventually_dense_fourth_le_fifth,
    tendsto_xiSliceDenseGaussianCoefficient_atTop.eventually_ge_atTop 0,
    eventually_gt_atTop (0 : ℝ)] with u hmass hfourth hcoef0 hu
  have hcoef : xiSliceDenseGaussianCoefficient u ≤ denseMomentConstant * u := by
    rw [xiSliceDenseGaussianCoefficient, xiSliceGaussianTailQuadratic_re_eq]
    exact (sub_le_self _ (xiSliceGaussianTailTransverse_bounds _ _).1).trans hmass
  calc
    _ ≤ (denseMomentConstant / u ^ 5) * (denseMomentConstant * u) ^ 2 :=
      mul_le_mul hfourth (pow_le_pow_left₀ hcoef0 hcoef 2) (sq_nonneg _)
        (by have := denseMomentConstant_pos; positivity)
    _ = _ := by field_simp [hu.ne']

private theorem dense_coefficient_ofReal (u : ℝ) :
    (xiSliceDenseGaussianCoefficient u : ℂ) =
      xiSliceGaussianTailQuadratic (Real.exp (u ^ 4))
        (xiSliceGaussianRadiusHead (Real.exp (u ^ 4)) (u ^ 3)) := by
  apply Complex.ext
  · rfl
  · simpa only [Complex.ofReal_im] using
      (xiSliceGaussianTailQuadratic_im_eq_zero (Real.exp (u ^ 4)) (u ^ 3)).symm

/-- The actual Xi tail has a growing real Gaussian background, with relative error tending
uniformly to zero on every fixed physical disc. The complementary finite block is retained. -/
theorem tendstoUniformlyOn_xiSliceDenseGaussianTail_compensated (M : ℝ) :
    TendstoUniformlyOn
      (fun u (z : ℂ) => Complex.exp (-((xiSliceDenseGaussianCoefficient u : ℂ) * z ^ 2)) *
        xiSliceDenseGaussianTail u z)
      (fun _ => (1 : ℂ)) atTop (Metric.closedBall 0 M) := by
  let K := max M 0
  have hK : 0 ≤ K := le_max_right _ _
  have hlim : Tendsto (fun u : ℝ => Real.exp (K ^ 4 * denseMomentConstant / u ^ 2) - 1)
      atTop (𝓝 0) := by
    have hdiv : Tendsto (fun u : ℝ => K ^ 4 * denseMomentConstant / u ^ 2) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by decide : 2 ≠ 0))
    have he := Real.continuous_exp.continuousAt.tendsto.comp hdiv
    simpa only [Function.comp_apply, Real.exp_zero, sub_self] using he.sub_const 1
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [eventually_dense_fourth_le,
    dense_radius_tendsto.eventually_ge_atTop (max 1 K),
    hlim.eventually (gt_mem_nhds hε)] with u hfourth hR hsmall
  intro z hz
  have hzK : ‖z‖ ≤ K := (mem_closedBall_zero_iff.mp hz).trans (le_max_left _ _)
  have hR0 : 0 < u ^ 3 := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hR)
  have hzR : ‖z‖ ≤ u ^ 3 := hzK.trans ((le_max_right _ _).trans hR)
  have hcomp :
      ‖Complex.exp (-((xiSliceDenseGaussianCoefficient u : ℂ) * z ^ 2)) *
          xiSliceDenseGaussianTail u z - 1‖ ≤
        Real.exp (‖z‖ ^ 4 * xiSliceGaussianTailFourth (Real.exp (u ^ 4))
          (xiSliceGaussianRadiusHead (Real.exp (u ^ 4)) (u ^ 3))) - 1 := by
    simpa only [xiSliceDenseGaussianTail, dense_coefficient_ofReal, mul_comm] using
      norm_xiSliceGaussianTail_compensated_sub_one_le (Real.exp (u ^ 4)) hR0 hzR
  have hB0 : 0 ≤ xiSliceGaussianTailFourth (Real.exp (u ^ 4))
      (xiSliceGaussianRadiusHead (Real.exp (u ^ 4)) (u ^ 3)) :=
    tsum_nonneg (fun _ => sq_nonneg _)
  have hprod : ‖z‖ ^ 4 * xiSliceGaussianTailFourth (Real.exp (u ^ 4))
      (xiSliceGaussianRadiusHead (Real.exp (u ^ 4)) (u ^ 3)) ≤
        K ^ 4 * denseMomentConstant / u ^ 2 := by
    calc
      _ ≤ K ^ 4 * (denseMomentConstant / u ^ 2) :=
        mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hzK 4) hfourth hB0 (pow_nonneg hK 4)
      _ = K ^ 4 * denseMomentConstant / u ^ 2 := by ring
  rw [dist_eq_norm, norm_sub_rev]
  exact hcomp.trans_lt ((sub_le_sub_right (Real.exp_le_exp.mpr hprod) 1).trans_lt hsmall)

/-- Relative Gaussian convergence holds on physical discs whose radius grows linearly in `u`. -/
theorem tendstoUniformlyOn_xiSliceDenseGaussianTail_dilated (M : ℝ) :
    TendstoUniformlyOn
      (fun u (z : ℂ) =>
        Complex.exp (-((xiSliceDenseGaussianCoefficient u : ℂ) * ((u : ℂ) * z) ^ 2)) *
          xiSliceDenseGaussianTail u ((u : ℂ) * z))
      (fun _ => (1 : ℂ)) atTop (Metric.closedBall 0 M) := by
  let K := max M 0
  have hK : 0 ≤ K := le_max_right _ _
  have hlim : Tendsto (fun u : ℝ => Real.exp (K ^ 4 * denseMomentConstant / u) - 1)
      atTop (𝓝 0) := by
    have hdiv : Tendsto (fun u : ℝ => K ^ 4 * denseMomentConstant / u) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have he := Real.continuous_exp.continuousAt.tendsto.comp hdiv
    simpa only [Function.comp_apply, Real.exp_zero, sub_self] using he.sub_const 1
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [eventually_dense_fourth_le_fifth,
    (tendsto_pow_atTop (by decide : 2 ≠ 0)).eventually_ge_atTop K,
    eventually_gt_atTop (0 : ℝ), hlim.eventually (gt_mem_nhds hε)]
    with u hfourth hR hu hsmall
  intro z hz
  have hzK : ‖z‖ ≤ K := (mem_closedBall_zero_iff.mp hz).trans (le_max_left _ _)
  have hnorm : ‖(u : ℂ) * z‖ = u * ‖z‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu]
  have hzR : ‖(u : ℂ) * z‖ ≤ u ^ 3 := by
    rw [hnorm]
    calc
      _ ≤ u * K := mul_le_mul_of_nonneg_left hzK hu.le
      _ ≤ u * u ^ 2 := mul_le_mul_of_nonneg_left hR hu.le
      _ = u ^ 3 := by ring
  have hcomp :
      ‖Complex.exp (-((xiSliceDenseGaussianCoefficient u : ℂ) * ((u : ℂ) * z) ^ 2)) *
          xiSliceDenseGaussianTail u ((u : ℂ) * z) - 1‖ ≤
        Real.exp (‖(u : ℂ) * z‖ ^ 4 * xiSliceGaussianTailFourth (Real.exp (u ^ 4))
          (xiSliceGaussianRadiusHead (Real.exp (u ^ 4)) (u ^ 3))) - 1 := by
    simpa only [xiSliceDenseGaussianTail, dense_coefficient_ofReal, mul_comm] using
      norm_xiSliceGaussianTail_compensated_sub_one_le (Real.exp (u ^ 4)) (pow_pos hu 3) hzR
  have hB0 : 0 ≤ xiSliceGaussianTailFourth (Real.exp (u ^ 4))
      (xiSliceGaussianRadiusHead (Real.exp (u ^ 4)) (u ^ 3)) :=
    tsum_nonneg (fun _ => sq_nonneg _)
  have hprod : ‖(u : ℂ) * z‖ ^ 4 * xiSliceGaussianTailFourth (Real.exp (u ^ 4))
      (xiSliceGaussianRadiusHead (Real.exp (u ^ 4)) (u ^ 3)) ≤
        K ^ 4 * denseMomentConstant / u := by
    rw [hnorm]
    calc
      _ ≤ (u * K) ^ 4 * (denseMomentConstant / u ^ 5) :=
        mul_le_mul
          (pow_le_pow_left₀ (mul_nonneg hu.le (norm_nonneg _))
            (mul_le_mul_of_nonneg_left hzK hu.le) 4)
          hfourth hB0 (by positivity)
      _ = _ := by field_simp [hu.ne']
  rw [dist_eq_norm, norm_sub_rev]
  exact hcomp.trans_lt ((sub_le_sub_right (Real.exp_le_exp.mpr hprod) 1).trans_lt hsmall)

end
end RHTower

