import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.PhysicalComponents.Depth.GaussianLaw

/-! # Physical tolerance gaps at neighboring logarithmic entry depths -/
open Real
namespace GaloisForLFunctions.HTGeometry.ReturnSpacing.PhysicalComponents.Depth
noncomputable section

/-- Below the semicircle, decreasing the arc width by h saves at least
h in projective operator error. -/
theorem chord_gap {x y : ℝ} (hy : 0≤y) (hyx : y≤x) (hx : x≤1/2) :
    x-y ≤ zeroGateArcTolerance x-zeroGateArcTolerance y := by
  let a := π*x/2
  let b := π*y/2
  have hb : 0≤b := div_nonneg (mul_nonneg pi_pos.le hy) (by norm_num)
  have hab : b≤a := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hyx pi_pos.le) (by norm_num)
  have hmax : a≤π/4 := by
    dsimp only [a]
    linarith only [mul_le_mul_of_nonneg_left hx pi_pos.le]
  have hs := QuantumAlg.sin_ge_slope_mul_of_nonneg_of_le (A:=π/2) (x:=(a-b)/2)
    (half_pos pi_pos) (by linarith only [pi_pos])
    (div_nonneg (sub_nonneg.mpr hab) (by norm_num)) (by linarith only [hb,hmax,pi_pos])
  rw [sin_pi_div_two] at hs
  have hc := cos_le_cos_of_nonneg_of_le_pi (x:=(a+b)/2) (y:=π/3)
    (by linarith only [hb,hab]) (by linarith only [pi_pos]) (by linarith only [hab,hmax,pi_pos])
  rw [cos_pi_div_three] at hc
  have hs' : (x-y)/2 ≤ sin ((a-b)/2) := by
    apply le_trans _ hs
    dsimp only [a,b]
    apply le_of_eq
    field_simp [pi_ne_zero]
  have hm := mul_le_mul hs' hc (by norm_num : (0:ℝ)≤1/2) (by linarith only [hs',hyx])
  change x-y≤2*sin a-2*sin b
  rw [←mul_sub,sin_sub_sin]
  linarith only [hm]

/-- Two fixed logarithmic depths z<w leave order 1/d room in physical
operator tolerance, uniformly for every positive integer d. -/
theorem depth_cutoff_gap {x z w : ℝ} (hx : 0<x) (hsmall : x≤1/2)
    (hz : 0≤z) (hw : z<w) {d : ℕ} (hd : 0<d) :
    x*exp (-w)*(w-z)/(d:ℝ) ≤ depthCutoff x d z-depthCutoff x d w := by
  let k : ℝ := d
  have hk : 0<k := Nat.cast_pos.mpr hd
  have hk₁ : 1≤k := by
    change 1≤(d:ℝ)
    exact_mod_cast (show 1≤d by omega)
  have hpos : 0≤w := hz.trans hw.le
  have he : exp (-w)≤exp (-w/k) := by
    apply exp_le_exp.mpr
    apply (le_div_iff₀ hk).mpr
    simpa only [mul_one] using mul_le_mul_of_nonpos_left hk₁ (neg_nonpos.mpr hpos)
  have h₁ := add_one_le_exp ((w-z)/k)
  have h₂ := mul_le_mul_of_nonneg_left h₁ (exp_pos (-w/k)).le
  rw [←exp_add,show -w/k+(w-z)/k = -z/k by ring] at h₂
  let A := x*exp (-z/k)
  let B := x*exp (-w/k)
  have hB : 0≤B := mul_nonneg hx.le (exp_pos _).le
  have hBA : B≤A := mul_le_mul_of_nonneg_left (exp_le_exp.mpr
    (div_le_div_of_nonneg_right (neg_le_neg hw.le) hk.le)) hx.le
  have hA : A≤1/2 := (mul_le_of_le_one_right hx.le (exp_le_one_iff.mpr
    (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hz) hk.le))).trans hsmall
  apply le_trans _ (chord_gap hB hBA hA)
  have h₃ := mul_le_mul_of_nonneg_right he (div_nonneg (sub_nonneg.mpr hw.le) hk.le)
  have h₄ := mul_le_mul_of_nonneg_left (show exp (-w)*((w-z)/k)≤exp (-z/k)-exp (-w/k) by
    linarith only [h₂,h₃]) hx.le
  dsimp only [A,B]
  change x*exp (-w)*(w-z)/k≤_
  calc _ = x*(exp (-w)*((w-z)/k)) := by ring
       _ ≤ x*(exp (-z/k)-exp (-w/k)) := h₄
       _ = _ := mul_sub ..

#print axioms depth_cutoff_gap
end
end GaloisForLFunctions.HTGeometry.ReturnSpacing.PhysicalComponents.Depth
