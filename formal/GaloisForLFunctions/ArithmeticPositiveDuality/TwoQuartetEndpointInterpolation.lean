import GaloisForLFunctions.HTGeometry.ChainObstruction
import Mathlib.Topology.Order.IntermediateValue

/-!
# Two quartet parameters match a donor endpoint jet

Fix transverse depth `1/4`. A quartet parameter `u=eta^2+5/16` has endpoint
value `u^2-1/16` and logarithmic derivative `2(u-1/8)/(u^2-1/16)`.
Two distinct positive ordinates match the product and reciprocal sum of
any four donor endpoint values greater than one. The proof interpolates
between a balanced pair and a quartet approaching the real axis.
-/

noncomputable section
set_option autoImplicit false

open Set

namespace GaloisForLFunctions.ArithmeticPositiveDuality

/-- Endpoint value of a quartet at transverse depth `1/4`. -/
def quartetEndpointMass (u : ℝ) : ℝ := u ^ 2 - 1 / 16

/-- Logarithmic endpoint derivative of the same quartet. -/
def quartetEndpointSlope (u : ℝ) : ℝ := 2 * (u - 1 / 8) / quartetEndpointMass u

private theorem mass_pos {u : ℝ} (hu : 5 / 16 ≤ u) :
    0 < quartetEndpointMass u := by
  unfold quartetEndpointMass
  nlinarith only [hu, sq_nonneg (u - 5 / 16)]

private theorem slope_pos {u : ℝ} (hu : 5 / 16 ≤ u) :
    0 < quartetEndpointSlope u :=
  div_pos (by linarith only [hu]) (mass_pos hu)

private theorem four_sqrt_sqrt_le {a b c d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    4 * Real.sqrt (Real.sqrt (a * b * c * d)) ≤ a + b + c + d := by
  have h₁ := HTGeometry.sqrt_mul_le_add_div_two ha hb
  have h₂ := HTGeometry.sqrt_mul_le_add_div_two hc hd
  have h₃ := HTGeometry.sqrt_mul_le_add_div_two
    (Real.sqrt_nonneg (a * b)) (Real.sqrt_nonneg (c * d))
  have he : Real.sqrt (a * b * c * d) = Real.sqrt (a * b) * Real.sqrt (c * d) := by
    rw [show a * b * c * d = (a * b) * (c * d) by ring,
      Real.sqrt_mul (mul_nonneg ha hb)]
  rw [he]
  linarith only [h₁, h₂, h₃]

private theorem reciprocal_sum_lower {a b c d : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    4 / Real.sqrt (Real.sqrt (a * b * c * d)) ≤ 1 / a + 1 / b + 1 / c + 1 / d := by
  have h := four_sqrt_sqrt_le (inv_nonneg.mpr ha.le) (inv_nonneg.mpr hb.le)
    (inv_nonneg.mpr hc.le) (inv_nonneg.mpr hd.le)
  have he : a⁻¹ * b⁻¹ * c⁻¹ * d⁻¹ = (a * b * c * d)⁻¹ := by ring
  rw [he, Real.sqrt_inv, Real.sqrt_inv] at h
  simpa only [one_div, div_eq_mul_inv, one_mul] using h

/-- Two distinct quartet ordinates match four donor values and their first logarithmic jet. -/
theorem exists_two_quartet_endpoint_parameters {a b c d : ℝ}
    (ha : 1 < a) (hb : 1 < b) (hc : 1 < c) (hd : 1 < d) :
    ∃ u v : ℝ, 5 / 16 < v ∧ v < u ∧
      quartetEndpointMass u * quartetEndpointMass v = a * b * c * d ∧
      quartetEndpointSlope u + quartetEndpointSlope v = 1 / a + 1 / b + 1 / c + 1 / d := by
  let P := a * b * c * d
  let r := Real.sqrt P
  let w := Real.sqrt r
  let B := Real.sqrt (r + 1 / 16)
  let U := fun v : ℝ => Real.sqrt (1 / 16 + P / quartetEndpointMass v)
  let f := fun v : ℝ => quartetEndpointSlope (U v) + quartetEndpointSlope v
  let S := 1 / a + 1 / b + 1 / c + 1 / d
  have ha0 : 0 < a := lt_trans zero_lt_one ha
  have hb0 : 0 < b := lt_trans zero_lt_one hb
  have hc0 : 0 < c := lt_trans zero_lt_one hc
  have hd0 : 0 < d := lt_trans zero_lt_one hd
  have hP : 1 < P := by
    exact one_lt_mul (one_lt_mul (one_lt_mul ha.le hb).le hc).le hd
  have hP0 : 0 < P := lt_trans zero_lt_one hP
  have hr : 1 < r := by
    have he := Real.sq_sqrt hP0.le
    have hn := Real.sqrt_nonneg P
    dsimp only [r]
    nlinarith only [he, hn, hP]
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  have hr2 : r ^ 2 = P := Real.sq_sqrt hP0.le
  have hw : 1 < w := by
    have he := Real.sq_sqrt hr0.le
    have hn := Real.sqrt_nonneg r
    dsimp only [w]
    nlinarith only [he, hn, hr]
  have hw2 : w ^ 2 = r := Real.sq_sqrt hr0.le
  have hB2 : B ^ 2 = r + 1 / 16 := Real.sq_sqrt (by linarith only [hr])
  have hB : 1 < B := by
    have hn : 0 ≤ B := Real.sqrt_nonneg _
    nlinarith only [hB2, hn, hr]
  have hBM : quartetEndpointMass B = r := by
    unfold quartetEndpointMass
    linarith only [hB2]
  have hUB : U B = B := by
    dsimp only [U]
    rw [hBM, ← hr2, sq, mul_div_cancel_right₀ _ hr0.ne']
    exact congrArg Real.sqrt (add_comm _ _)
  have hU2 (v : ℝ) (hv : 5 / 16 ≤ v) :
      U v ^ 2 = 1 / 16 + P / quartetEndpointMass v :=
    Real.sq_sqrt (by positivity [mass_pos hv])
  have hUM (v : ℝ) (hv : 5 / 16 ≤ v) :
      quartetEndpointMass (U v) = P / quartetEndpointMass v := by
    change U v ^ 2 - 1 / 16 = P / quartetEndpointMass v
    linarith only [hU2 v hv]
  have hUlower (v : ℝ) (hv : v ∈ Icc (5 / 16 : ℝ) B) : B ≤ U v := by
    have hMv : quartetEndpointMass v ≤ r := by
      have hs := pow_le_pow_left₀ (by linarith only [hv.1] : 0 ≤ v) hv.2 2
      unfold quartetEndpointMass
      linarith only [hs, hB2]
    have hdiv : r ≤ P / quartetEndpointMass v := by
      apply (le_div_iff₀ (mass_pos hv.1)).mpr
      have hm := mul_le_mul_of_nonneg_left hMv hr0.le
      nlinarith only [hm, hr2]
    have hs := hU2 v hv.1
    have hn : 0 ≤ U v := Real.sqrt_nonneg _
    nlinarith only [hs, hB2, hdiv, hn, hB]
  have hcU : ContinuousOn U (Icc (5 / 16 : ℝ) B) :=
    (continuousOn_const.add (continuousOn_const.div
      ((continuousOn_id.pow 2).sub continuousOn_const)
      (fun v hv => (mass_pos hv.1).ne'))).sqrt
  have hcf : ContinuousOn f (Icc (5 / 16 : ℝ) B) := by
    apply ContinuousOn.add
    · exact (continuousOn_const.mul (hcU.sub continuousOn_const)).div
        ((hcU.pow 2).sub continuousOn_const)
        (fun v hv => (mass_pos (by linarith only [hUlower v hv, hB])).ne')
    · exact (continuousOn_const.mul (continuousOn_id.sub continuousOn_const)).div
        ((continuousOn_id.pow 2).sub continuousOn_const)
        (fun v hv => (mass_pos hv.1).ne')
  have hS4 : S < 4 := by
    have h₁ := one_div_lt_one_div_of_lt zero_lt_one ha
    have h₂ := one_div_lt_one_div_of_lt zero_lt_one hb
    have h₃ := one_div_lt_one_div_of_lt zero_lt_one hc
    have h₄ := one_div_lt_one_div_of_lt zero_lt_one hd
    dsimp only [S]
    simp only [one_div]
    norm_num at h₁ h₂ h₃ h₄
    linarith only [h₁, h₂, h₃, h₄]
  have hleft : S < f (5 / 16) := by
    have hpos := slope_pos (show 5 / 16 ≤ U (5 / 16) by
      have := hUlower (5 / 16) ⟨le_rfl, by linarith only [hB]⟩
      linarith only [this, hB])
    have he : quartetEndpointSlope (5 / 16) = (32 / 3 : ℝ) := by
      norm_num [quartetEndpointSlope, quartetEndpointMass]
    dsimp only [f]
    rw [he]
    linarith only [hpos, hS4]
  have hright : f B < S := by
    have hBw : B < w + 1 / 8 := by
      have hn : 0 ≤ B := Real.sqrt_nonneg _
      nlinarith only [hB2, hw2, hw, hn]
    have hSl : 4 / w ≤ S := reciprocal_sum_lower ha0 hb0 hc0 hd0
    have he : f B = 4 * (B - 1 / 8) / r := by
      dsimp only [f]
      rw [hUB, quartetEndpointSlope, hBM]
      ring
    rw [he]
    apply lt_of_lt_of_le _ hSl
    rw [div_lt_div_iff₀ hr0 (lt_trans zero_lt_one hw)]
    nlinarith only [hBw, hw2, mul_pos (show 0 < w by linarith only [hw])
      (show 0 < w + 1 / 8 - B by linarith only [hBw])]
  obtain ⟨v, hv, he⟩ := intermediate_value_Icc' (by linarith only [hB] : (5 / 16 : ℝ) ≤ B)
    hcf ⟨hright.le, hleft.le⟩
  have hv0 : 5 / 16 < v := lt_of_le_of_ne hv.1 (fun h => by
    rw [← h] at he
    exact (ne_of_gt hleft) he)
  have hvB : v < B := lt_of_le_of_ne hv.2 (fun h => by
    rw [h] at he
    exact (ne_of_lt hright) he)
  refine ⟨U v, v, hv0, hvB.trans_le (hUlower v hv), ?_, he⟩
  rw [hUM v hv.1, div_mul_cancel₀ _ (mass_pos hv.1).ne']

end GaloisForLFunctions.ArithmeticPositiveDuality

#print axioms GaloisForLFunctions.ArithmeticPositiveDuality.exists_two_quartet_endpoint_parameters
