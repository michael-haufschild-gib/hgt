import GaloisForLFunctions.RHTower.ThetaCuspFirstAtomReflectionJets
import GaloisForLFunctions.RHTower.ThetaCuspAllOrderLikelihoodCooling

/-!
# Exact Gaussian scale limits of the first-atom reflection jets

Each normalized moment is an explicit rational function of inverse source scale.
Continuity at zero proves all five limits through order ten.
-/

open Filter Topology
namespace RHTower
noncomputable section

/-- First-atom squared source mass is the exact common Gaussian times the seed polynomial. -/
theorem thetaCuspSourceTerm_one_eq_scale_profile (x : ℝ) :
    thetaCuspSourceTerm x 1 = Real.exp (x/2-thetaCuspSingleAtomReflectionScale 1 x) *
      (4*thetaCuspSingleAtomReflectionScale 1 x^(2 : ℕ)-6*thetaCuspSingleAtomReflectionScale 1 x) := by
  simpa [thetaCuspFirstAtomJetPolynomial] using iteratedDeriv_firstAtom_eq_scale_polynomial 0 x

/-- The signed first-atom reflection moment of order 2 has its exact Gaussian scale limit. -/
theorem thetaCuspFirstAtomReflectionJet_2_scaled_tendsto :
    Tendsto (fun x : ℝ => (-1 : ℝ)^(1 : ℕ)*thetaCuspFirstAtomReflectionJet 2 x /
      (thetaCuspSourceTerm x 1^(2 : ℕ)*thetaCuspSingleAtomReflectionScale 1 x^(1 : ℕ)))
      atTop (𝓝 (8 : ℝ)) := by
  let R (u : ℝ) := ((480 : ℝ)*u^(2 : ℕ) + (-384 : ℝ)*u^(1 : ℕ) + (128 : ℝ)) / (4-6*u)^(2 : ℕ)
  have hc : ContinuousAt R 0 := by
    dsimp only [R]
    apply ContinuousAt.div <;> first | fun_prop | norm_num
  have h := hc.tendsto.comp thetaCuspC5FarTail_reflectionScale_inv_tendsto_zero
  have hlim : Tendsto (fun x : ℝ => R ((thetaCuspSingleAtomReflectionScale 1 x)⁻¹))
      atTop (𝓝 (8 : ℝ)) := by
    rw [show R 0 = 8 by norm_num [R]] at h
    exact h
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hq := three_lt_thetaCuspSingleAtomReflectionScale (n := 1) (by norm_num) hx.le
  have hqn : thetaCuspSingleAtomReflectionScale 1 x ≠ 0 := by linarith
  have hb : 4*thetaCuspSingleAtomReflectionScale 1 x^(2 : ℕ)-6*thetaCuspSingleAtomReflectionScale 1 x ≠ 0 := by
    nlinarith [sq_nonneg (thetaCuspSingleAtomReflectionScale 1 x-3)]
  have hd : 4-6*(thetaCuspSingleAtomReflectionScale 1 x)⁻¹ ≠ 0 := by
    apply ne_of_gt
    rw [sub_pos, ← div_eq_mul_inv]
    apply (div_lt_iff₀ (by linarith : 0 < thetaCuspSingleAtomReflectionScale 1 x)).mpr
    linarith
  rw [thetaCuspFirstAtomReflectionJet_2, thetaCuspSourceTerm_one_eq_scale_profile]
  dsimp only [R]
  field_simp [hqn, hb, hd, Real.exp_ne_zero]
  ring

/-- The signed first-atom reflection moment of order 4 has its exact Gaussian scale limit. -/
theorem thetaCuspFirstAtomReflectionJet_4_scaled_tendsto :
    Tendsto (fun x : ℝ => (-1 : ℝ)^(2 : ℕ)*thetaCuspFirstAtomReflectionJet 4 x /
      (thetaCuspSourceTerm x 1^(2 : ℕ)*thetaCuspSingleAtomReflectionScale 1 x^(2 : ℕ)))
      atTop (𝓝 (192 : ℝ)) := by
  let R (u : ℝ) := ((-1920 : ℝ)*u^(3 : ℕ) + (17664 : ℝ)*u^(2 : ℕ) + (-9728 : ℝ)*u^(1 : ℕ) + (3072 : ℝ)) / (4-6*u)^(2 : ℕ)
  have hc : ContinuousAt R 0 := by
    dsimp only [R]
    apply ContinuousAt.div <;> first | fun_prop | norm_num
  have h := hc.tendsto.comp thetaCuspC5FarTail_reflectionScale_inv_tendsto_zero
  have hlim : Tendsto (fun x : ℝ => R ((thetaCuspSingleAtomReflectionScale 1 x)⁻¹))
      atTop (𝓝 (192 : ℝ)) := by
    rw [show R 0 = 192 by norm_num [R]] at h
    exact h
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hq := three_lt_thetaCuspSingleAtomReflectionScale (n := 1) (by norm_num) hx.le
  have hqn : thetaCuspSingleAtomReflectionScale 1 x ≠ 0 := by linarith
  have hb : 4*thetaCuspSingleAtomReflectionScale 1 x^(2 : ℕ)-6*thetaCuspSingleAtomReflectionScale 1 x ≠ 0 := by
    nlinarith [sq_nonneg (thetaCuspSingleAtomReflectionScale 1 x-3)]
  have hd : 4-6*(thetaCuspSingleAtomReflectionScale 1 x)⁻¹ ≠ 0 := by
    apply ne_of_gt
    rw [sub_pos, ← div_eq_mul_inv]
    apply (div_lt_iff₀ (by linarith : 0 < thetaCuspSingleAtomReflectionScale 1 x)).mpr
    linarith
  rw [thetaCuspFirstAtomReflectionJet_4, thetaCuspSourceTerm_one_eq_scale_profile]
  dsimp only [R]
  field_simp [hqn, hb, hd, Real.exp_ne_zero]

/-- The signed first-atom reflection moment of order 6 has its exact Gaussian scale limit. -/
theorem thetaCuspFirstAtomReflectionJet_6_scaled_tendsto :
    Tendsto (fun x : ℝ => (-1 : ℝ)^(3 : ℕ)*thetaCuspFirstAtomReflectionJet 6 x /
      (thetaCuspSourceTerm x 1^(2 : ℕ)*thetaCuspSingleAtomReflectionScale 1 x^(3 : ℕ)))
      atTop (𝓝 (7680 : ℝ)) := by
  let R (u : ℝ) := ((7680 : ℝ)*u^(4 : ℕ) + (-328704 : ℝ)*u^(3 : ℕ) + (1015808 : ℝ)*u^(2 : ℕ) + (-430080 : ℝ)*u^(1 : ℕ) + (122880 : ℝ)) / (4-6*u)^(2 : ℕ)
  have hc : ContinuousAt R 0 := by
    dsimp only [R]
    apply ContinuousAt.div <;> first | fun_prop | norm_num
  have h := hc.tendsto.comp thetaCuspC5FarTail_reflectionScale_inv_tendsto_zero
  have hlim : Tendsto (fun x : ℝ => R ((thetaCuspSingleAtomReflectionScale 1 x)⁻¹))
      atTop (𝓝 (7680 : ℝ)) := by
    rw [show R 0 = 7680 by norm_num [R]] at h
    exact h
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hq := three_lt_thetaCuspSingleAtomReflectionScale (n := 1) (by norm_num) hx.le
  have hqn : thetaCuspSingleAtomReflectionScale 1 x ≠ 0 := by linarith
  have hb : 4*thetaCuspSingleAtomReflectionScale 1 x^(2 : ℕ)-6*thetaCuspSingleAtomReflectionScale 1 x ≠ 0 := by
    nlinarith [sq_nonneg (thetaCuspSingleAtomReflectionScale 1 x-3)]
  have hd : 4-6*(thetaCuspSingleAtomReflectionScale 1 x)⁻¹ ≠ 0 := by
    apply ne_of_gt
    rw [sub_pos, ← div_eq_mul_inv]
    apply (div_lt_iff₀ (by linarith : 0 < thetaCuspSingleAtomReflectionScale 1 x)).mpr
    linarith
  rw [thetaCuspFirstAtomReflectionJet_6, thetaCuspSourceTerm_one_eq_scale_profile]
  dsimp only [R]
  field_simp [hqn, hb, hd, Real.exp_ne_zero]
  ring

/-- The signed first-atom reflection moment of order 8 has its exact Gaussian scale limit. -/
theorem thetaCuspFirstAtomReflectionJet_8_scaled_tendsto :
    Tendsto (fun x : ℝ => (-1 : ℝ)^(4 : ℕ)*thetaCuspFirstAtomReflectionJet 8 x /
      (thetaCuspSourceTerm x 1^(2 : ℕ)*thetaCuspSingleAtomReflectionScale 1 x^(4 : ℕ)))
      atTop (𝓝 (430080 : ℝ)) := by
  let R (u : ℝ) := ((-30720 : ℝ)*u^(5 : ℕ) + (5443584 : ℝ)*u^(4 : ℕ) + (-49553408 : ℝ)*u^(3 : ℕ) + (78446592 : ℝ)*u^(2 : ℕ) + (-27525120 : ℝ)*u^(1 : ℕ) + (6881280 : ℝ)) / (4-6*u)^(2 : ℕ)
  have hc : ContinuousAt R 0 := by
    dsimp only [R]
    apply ContinuousAt.div <;> first | fun_prop | norm_num
  have h := hc.tendsto.comp thetaCuspC5FarTail_reflectionScale_inv_tendsto_zero
  have hlim : Tendsto (fun x : ℝ => R ((thetaCuspSingleAtomReflectionScale 1 x)⁻¹))
      atTop (𝓝 (430080 : ℝ)) := by
    rw [show R 0 = 430080 by norm_num [R]] at h
    exact h
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hq := three_lt_thetaCuspSingleAtomReflectionScale (n := 1) (by norm_num) hx.le
  have hqn : thetaCuspSingleAtomReflectionScale 1 x ≠ 0 := by linarith
  have hb : 4*thetaCuspSingleAtomReflectionScale 1 x^(2 : ℕ)-6*thetaCuspSingleAtomReflectionScale 1 x ≠ 0 := by
    nlinarith [sq_nonneg (thetaCuspSingleAtomReflectionScale 1 x-3)]
  have hd : 4-6*(thetaCuspSingleAtomReflectionScale 1 x)⁻¹ ≠ 0 := by
    apply ne_of_gt
    rw [sub_pos, ← div_eq_mul_inv]
    apply (div_lt_iff₀ (by linarith : 0 < thetaCuspSingleAtomReflectionScale 1 x)).mpr
    linarith
  rw [thetaCuspFirstAtomReflectionJet_8, thetaCuspSourceTerm_one_eq_scale_profile]
  dsimp only [R]
  field_simp [hqn, hb, hd, Real.exp_ne_zero]

/-- The signed first-atom reflection moment of order 10 has its exact Gaussian scale limit. -/
theorem thetaCuspFirstAtomReflectionJet_10_scaled_tendsto :
    Tendsto (fun x : ℝ => (-1 : ℝ)^(5 : ℕ)*thetaCuspFirstAtomReflectionJet 10 x /
      (thetaCuspSourceTerm x 1^(2 : ℕ)*thetaCuspSingleAtomReflectionScale 1 x^(5 : ℕ)))
      atTop (𝓝 (30965760 : ℝ)) := by
  let R (u : ℝ) := ((122880 : ℝ)*u^(6 : ℕ) + (-87834624 : ℝ)*u^(5 : ℕ) + (2001010688 : ℝ)*u^(4 : ℕ) + (-7696220160 : ℝ)*u^(3 : ℕ) + (7596933120 : ℝ)*u^(2 : ℕ) + (-2312110080 : ℝ)*u^(1 : ℕ) + (495452160 : ℝ)) / (4-6*u)^(2 : ℕ)
  have hc : ContinuousAt R 0 := by
    dsimp only [R]
    apply ContinuousAt.div <;> first | fun_prop | norm_num
  have h := hc.tendsto.comp thetaCuspC5FarTail_reflectionScale_inv_tendsto_zero
  have hlim : Tendsto (fun x : ℝ => R ((thetaCuspSingleAtomReflectionScale 1 x)⁻¹))
      atTop (𝓝 (30965760 : ℝ)) := by
    rw [show R 0 = 30965760 by norm_num [R]] at h
    exact h
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hq := three_lt_thetaCuspSingleAtomReflectionScale (n := 1) (by norm_num) hx.le
  have hqn : thetaCuspSingleAtomReflectionScale 1 x ≠ 0 := by linarith
  have hb : 4*thetaCuspSingleAtomReflectionScale 1 x^(2 : ℕ)-6*thetaCuspSingleAtomReflectionScale 1 x ≠ 0 := by
    nlinarith [sq_nonneg (thetaCuspSingleAtomReflectionScale 1 x-3)]
  have hd : 4-6*(thetaCuspSingleAtomReflectionScale 1 x)⁻¹ ≠ 0 := by
    apply ne_of_gt
    rw [sub_pos, ← div_eq_mul_inv]
    apply (div_lt_iff₀ (by linarith : 0 < thetaCuspSingleAtomReflectionScale 1 x)).mpr
    linarith
  rw [thetaCuspFirstAtomReflectionJet_10, thetaCuspSourceTerm_one_eq_scale_profile]
  dsimp only [R]
  field_simp [hqn, hb, hd, Real.exp_ne_zero]
  ring

end
end RHTower
