import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFirstAtomGaussianJetLimits
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspNativeJetFirstAtomApproximation
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspNativeOddSchurCompensation

/-!
# Positive compensated native odd determinant on the cofinal source tail

The exact first-atom Gaussian jet limits and the all-order infinite-source error
bound give a strictly positive limiting determinant. Every fixed center-flux
correction is lower order. Only a compact center comparison remains.
-/

open Filter Topology Set
namespace RHTower
noncomputable section

private theorem q_ne (x : ℝ) : thetaCuspSingleAtomReflectionScale 1 x ≠ 0 := by
  unfold thetaCuspSingleAtomReflectionScale
  positivity

private theorem f_ne {x : ℝ} (hx : 0 < x) : thetaCuspSourceTerm x 1 ≠ 0 :=
  (thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num)).ne'

/-- Fourier-signed native reflection moment normalized by first-atom mass and Gaussian scale. -/
def thetaCuspNativeScaledEvenJet (k : ℕ) (x : ℝ) : ℝ :=
  (-1 : ℝ)^k*thetaCuspNativeReflectionJet (2*k) x /
    (thetaCuspSourceTerm x 1^(2 : ℕ)*thetaCuspSingleAtomReflectionScale 1 x^k)

private theorem native_limit_of_first (k : ℕ) (c : ℝ)
    (hfirst : Tendsto (fun x : ℝ => (-1 : ℝ)^k*thetaCuspFirstAtomReflectionJet (2*k) x /
      (thetaCuspSourceTerm x 1^(2 : ℕ)*thetaCuspSingleAtomReflectionScale 1 x^k)) atTop (𝓝 c)) :
    Tendsto (thetaCuspNativeScaledEvenJet k) atTop (𝓝 c) := by
  have herr := ((thetaCuspNativeReflectionJet_firstAtom_error_scaled_tendsto_zero 0 (2*k)).mul
    (thetaCuspC5FarTail_reflectionScale_inv_tendsto_zero.pow k)).const_mul ((-1 : ℝ)^k)
  have h := hfirst.add herr
  apply (show Tendsto _ atTop (𝓝 c) from by simpa using h).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  unfold thetaCuspNativeScaledEvenJet
  field_simp [q_ne x, f_ne hx]
  ring

theorem thetaCuspNativeScaledEvenJet_one_tendsto :
    Tendsto (thetaCuspNativeScaledEvenJet 1) atTop (𝓝 8) :=
  native_limit_of_first 1 8 thetaCuspFirstAtomReflectionJet_2_scaled_tendsto

theorem thetaCuspNativeScaledEvenJet_two_tendsto :
    Tendsto (thetaCuspNativeScaledEvenJet 2) atTop (𝓝 192) :=
  native_limit_of_first 2 192 thetaCuspFirstAtomReflectionJet_4_scaled_tendsto

theorem thetaCuspNativeScaledEvenJet_three_tendsto :
    Tendsto (thetaCuspNativeScaledEvenJet 3) atTop (𝓝 7680) :=
  native_limit_of_first 3 7680 thetaCuspFirstAtomReflectionJet_6_scaled_tendsto

theorem thetaCuspNativeScaledEvenJet_four_tendsto :
    Tendsto (thetaCuspNativeScaledEvenJet 4) atTop (𝓝 430080) :=
  native_limit_of_first 4 430080 thetaCuspFirstAtomReflectionJet_8_scaled_tendsto

theorem thetaCuspNativeScaledEvenJet_five_tendsto :
    Tendsto (thetaCuspNativeScaledEvenJet 5) atTop (𝓝 30965760) :=
  native_limit_of_first 5 30965760 thetaCuspFirstAtomReflectionJet_10_scaled_tendsto

/-- The complete odd leading minor has the strictly positive Gaussian asymptotic reserve. -/
theorem thetaCuspNativeOddHeadDet_scaled_tendsto :
    Tendsto (fun x : ℝ => thetaCuspNativeOddHeadDet x /
      (thetaCuspSourceTerm x 1^(4 : ℕ)*thetaCuspSingleAtomReflectionScale 1 x^(4 : ℕ)))
      atTop (𝓝 (24576 : ℝ)) := by
  have h := (thetaCuspNativeScaledEvenJet_one_tendsto.mul thetaCuspNativeScaledEvenJet_three_tendsto).sub
    (thetaCuspNativeScaledEvenJet_two_tendsto.pow 2)
  apply (show Tendsto _ atTop (𝓝 (24576 : ℝ)) from by convert h using 1; norm_num).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  norm_num [thetaCuspNativeScaledEvenJet, thetaCuspNativeOddHeadDet]
  field_simp [q_ne x, f_ne hx]

/-- The complete native odd rank-three determinant has a fixed positive asymptotic reserve. -/
theorem thetaCuspNativeOddHankelThreeDet_scaled_tendsto :
    Tendsto (fun x : ℝ => thetaCuspNativeOddHankelThreeDet x /
      (thetaCuspSourceTerm x 1^(6 : ℕ)*thetaCuspSingleAtomReflectionScale 1 x^(9 : ℕ)))
      atTop (𝓝 (96636764160 : ℝ)) := by
  have h1 := thetaCuspNativeScaledEvenJet_one_tendsto
  have h2 := thetaCuspNativeScaledEvenJet_two_tendsto
  have h3 := thetaCuspNativeScaledEvenJet_three_tendsto
  have h4 := thetaCuspNativeScaledEvenJet_four_tendsto
  have h5 := thetaCuspNativeScaledEvenJet_five_tendsto
  have h := (((((h1.mul h3).mul h5).sub (h1.mul (h4.pow 2))).sub ((h2.pow 2).mul h5)).add
    (((h2.mul h3).mul h4).const_mul 2)).sub (h3.pow 3)
  apply (show Tendsto _ atTop (𝓝 (96636764160 : ℝ)) from by convert h using 1; norm_num).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  norm_num [thetaCuspNativeScaledEvenJet, thetaCuspNativeOddHankelThreeDet,
    HilbertMetric.signedEvenHankelThreeDet]
  field_simp [q_ne x, f_ne hx]
  ring

/-- The full source and first atom have the same leading mass. -/
theorem thetaCuspFullSource_div_firstAtom_tendsto_one :
    Tendsto (fun x : ℝ => thetaCuspFullSource x / thetaCuspSourceTerm x 1) atTop (𝓝 1) := by
  have h := (thetaCuspFullSource_derivative_relative_error_scaled_tendsto_zero 0 0).add_const 1
  apply (show Tendsto _ atTop (𝓝 (1 : ℝ)) from by simpa using h).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  field_simp [f_ne hx]
  ring

private theorem firstAtom_scaled_slope_tendsto :
    Tendsto (fun x : ℝ => deriv (fun y : ℝ => thetaCuspSourceTerm y 1) x /
      (thetaCuspSourceTerm x 1*thetaCuspSingleAtomReflectionScale 1 x)) atTop (𝓝 (-2 : ℝ)) := by
  let R (u : ℝ) := (-15*u^(2 : ℕ)+30*u-8)/(4-6*u)
  have hc : ContinuousAt R 0 := by
    dsimp only [R]
    apply ContinuousAt.div <;> first | fun_prop | norm_num
  have h := hc.tendsto.comp thetaCuspC5FarTail_reflectionScale_inv_tendsto_zero
  rw [show R 0 = -2 by norm_num [R]] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hq := three_lt_thetaCuspSingleAtomReflectionScale (n := 1) (by norm_num) hx.le
  have hb : 4*thetaCuspSingleAtomReflectionScale 1 x^(2 : ℕ)-6*thetaCuspSingleAtomReflectionScale 1 x ≠ 0 := by
    nlinarith [sq_nonneg (thetaCuspSingleAtomReflectionScale 1 x-3)]
  have hd : 4-6*(thetaCuspSingleAtomReflectionScale 1 x)⁻¹ ≠ 0 := by
    apply ne_of_gt
    rw [sub_pos, ← div_eq_mul_inv]
    apply (div_lt_iff₀ (by linarith : 0 < thetaCuspSingleAtomReflectionScale 1 x)).mpr
    linarith
  rw [← iteratedDeriv_one, iteratedDeriv_firstAtom_eq_scale_polynomial,
    thetaCuspSourceTerm_one_eq_scale_profile]
  norm_num [R, thetaCuspFirstAtomJetPolynomial, thetaCuspFirstAtomJetStep]
  field_simp [q_ne x, hb, hd, Real.exp_ne_zero]
  ring

/-- The actual logarithmic source slope has the same leading first-atom scale. -/
theorem thetaCuspFullSource_deriv_div_firstAtom_scale_tendsto :
    Tendsto (fun x : ℝ => deriv thetaCuspFullSource x /
      (thetaCuspSourceTerm x 1*thetaCuspSingleAtomReflectionScale 1 x)) atTop (𝓝 (-2 : ℝ)) := by
  have he := (thetaCuspFullSource_derivative_relative_error_scaled_tendsto_zero 0 1).mul
    thetaCuspC5FarTail_reflectionScale_inv_tendsto_zero
  have h := firstAtom_scaled_slope_tendsto.add he
  apply (show Tendsto _ atTop (𝓝 (-2 : ℝ)) from by simpa using h).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  field_simp [q_ne x, f_ne hx]
  ring

private theorem center_div_scale_four_tendsto_zero :
    Tendsto (fun x : ℝ => x/thetaCuspSingleAtomReflectionScale 1 x^(4 : ℕ)) atTop (𝓝 0) := by
  have h := (GaloisForLFunctions.HTGeometry.tendsto_pow_mul_exp_neg_mul_atTop
    (b := (8 : ℝ)) (by norm_num) 1).const_mul ((Real.pi^(4 : ℕ))⁻¹)
  apply (show Tendsto _ atTop (𝓝 (0 : ℝ)) from by simpa using h).congr'
  filter_upwards with x
  have hp : Real.exp (8*x) = Real.exp (2*x)^(4 : ℕ) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  simp only [thetaCuspSingleAtomReflectionScale, Nat.cast_one, one_pow, mul_one,
    mul_pow, Real.exp_neg, hp, div_eq_mul_inv]
  ring

/-- The exact center-flux source correction is lower order than the native determinant reserve. -/
theorem thetaCuspCenterCompensationSource_scaled_tendsto_zero :
    Tendsto (fun x : ℝ => thetaCuspCenterCompensationSource x /
      (thetaCuspSourceTerm x 1^(2 : ℕ)*thetaCuspSingleAtomReflectionScale 1 x^(5 : ℕ))) atTop (𝓝 0) := by
  have hm := thetaCuspFullSource_div_firstAtom_tendsto_one
  have hs := thetaCuspFullSource_deriv_div_firstAtom_scale_tendsto
  have hi := thetaCuspC5FarTail_reflectionScale_inv_tendsto_zero
  have h := (((hm.pow 2).mul (hi.pow 5)).const_mul 3).add
    (((center_div_scale_four_tendsto_zero.mul hm).mul hs).const_mul 2)
  apply (show Tendsto _ atTop (𝓝 (0 : ℝ)) from by simpa using h).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  unfold thetaCuspCenterCompensationSource
  field_simp [q_ne x, f_ne hx]

/-- Every fixed compensation coefficient preserves the strictly positive far-tail determinant limit. -/
theorem thetaCuspNativeOddCompensatedDet_scaled_tendsto (C : ℝ) :
    Tendsto (fun x : ℝ => thetaCuspNativeOddCompensatedDet C x /
      (thetaCuspSourceTerm x 1^(6 : ℕ)*thetaCuspSingleAtomReflectionScale 1 x^(9 : ℕ)))
      atTop (𝓝 (96636764160 : ℝ)) := by
  have h := thetaCuspNativeOddHankelThreeDet_scaled_tendsto.add
    ((thetaCuspNativeOddHeadDet_scaled_tendsto.mul thetaCuspCenterCompensationSource_scaled_tendsto_zero).const_mul C)
  apply (show Tendsto _ atTop (𝓝 (96636764160 : ℝ)) from by simpa using h).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  unfold thetaCuspNativeOddCompensatedDet
  field_simp [q_ne x, f_ne hx]

/-- The complete compensated odd determinant is strictly positive on a cofinal physical ray. -/
theorem eventually_thetaCuspNativeOddCompensatedDet_pos (C : ℝ) :
    ∀ᶠ x : ℝ in atTop, 0 < thetaCuspNativeOddCompensatedDet C x := by
  have he := (thetaCuspNativeOddCompensatedDet_scaled_tendsto C).eventually
    (eventually_gt_nhds (by norm_num : (0 : ℝ) < 96636764160))
  filter_upwards [he, eventually_gt_atTop (0 : ℝ)] with x hp hx
  have hq : 0 < thetaCuspSingleAtomReflectionScale 1 x := by
    unfold thetaCuspSingleAtomReflectionScale
    positivity
  have hm : 0 < thetaCuspSourceTerm x 1^(6 : ℕ)*thetaCuspSingleAtomReflectionScale 1 x^(9 : ℕ) :=
    mul_pos (pow_pos (thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num)) 6) (pow_pos hq 9)
  simpa only [div_mul_cancel₀ _ hm.ne'] using mul_pos hp hm

/-- Canonical compensation leaves only a compact annulus of positive centers to compare. -/
theorem exists_thetaCuspNativeOddCompensatedDet_positive_ends :
    ∃ δ X : ℝ, 0 < δ ∧ δ < X ∧
      (∀ x : ℝ, 0 < x → x < δ →
        0 < thetaCuspNativeOddCompensatedDet thetaCuspNativeOddCompensationCoefficient x) ∧
      (∀ x : ℝ, X ≤ x →
        0 < thetaCuspNativeOddCompensatedDet thetaCuspNativeOddCompensationCoefficient x) := by
  obtain ⟨δ, hδ, hlocal⟩ := exists_thetaCuspNativeOddCompensatedDet_pos_near_zero
  obtain ⟨X, hX⟩ := eventually_atTop.1
    (eventually_thetaCuspNativeOddCompensatedDet_pos thetaCuspNativeOddCompensationCoefficient)
  refine ⟨δ, max X (δ+1), hδ, lt_of_lt_of_le (by linarith) (le_max_right _ _), ?_, ?_⟩
  · intro x hx hxd
    exact hlocal x (by rwa [abs_of_pos hx])
  · intro x hx
    exact hX x ((le_max_left _ _).trans hx)

end
end RHTower
