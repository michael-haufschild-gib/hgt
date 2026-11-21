import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.FluxOccupation.ArcMargins

/-! # Time and accuracy scales for one product step at fixed physical error -/
open Real
namespace GaloisForLFunctions.HTGeometry.FluxOccupation
noncomputable section

/-- Erosion by x/(2D) pays for a whole one-step interval. Its length
is also below the minimum gap between consecutive entries. -/
theorem scale_choice {D : ℕ} (hD : 2≤D) {x M : ℝ} (hx : 0<x) (hx' : x≤1/4) (hM : 0<M) :
    let y := x-x/(2*(D:ℝ))
    let h := x*sqrt (D:ℝ)/(2*(D:ℝ)*M)
    0<y ∧ y<x ∧ 0<h ∧ h*(M/π) ≤ 1-2*y ∧
      zeroGateArcTolerance y+M^2*h^2 ≤ zeroGateArcTolerance x := by
  intro y h
  have hD' : (2:ℝ)≤D := by exact_mod_cast hD
  have hd : (0:ℝ)<D := by linarith only [hD']
  have hL := Real.sq_sqrt hd.le
  have hL' : sqrt (D:ℝ) ≤ (D:ℝ) := by
    nlinarith only [hL,Real.sqrt_nonneg (D:ℝ),hD',sq_nonneg ((D:ℝ)-1)]
  have hy : 0<y := by
    apply sub_pos.mpr
    rw [div_lt_iff₀ (by positivity)]
    nlinarith only [mul_le_mul_of_nonneg_left hD' hx.le,hx]
  have hyx : y<x := sub_lt_self _ (by positivity)
  have hh : 0<h := by dsimp only [h]; positivity
  refine ⟨hy,hyx,hh,?_,?_⟩
  · have he : h*(M/π)=x*sqrt (D:ℝ)/(2*(D:ℝ)*π) := by dsimp only [h]; field_simp
    have hsmall : h*(M/π) ≤ 1/4 := by
      rw [he,div_le_iff₀ (by positivity)]
      have h1 := mul_le_mul_of_nonneg_left hL' hx.le
      have h2 := mul_le_mul_of_nonneg_right hx' hd.le
      have h3 := mul_le_mul_of_nonneg_left Real.pi_gt_three.le hd.le
      linarith only [h1,h2,h3]
    linarith only [hsmall,hyx,hx']
  · have herr : M^2*h^2=x^2/(4*(D:ℝ)) := by
      dsimp only [h]
      rw [div_pow,mul_pow,hL]
      field_simp
      ring
    have hM' : M^2*h^2 ≤ x-y := by
      rw [herr,show x-y=x/(2*(D:ℝ)) by dsimp only [y]; ring]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hxx := mul_le_mul_of_nonneg_left (show x≤2 by linarith only [hx']) hx.le
      nlinarith only [mul_le_mul_of_nonneg_right hxx hd.le]
    exact (add_le_add (le_refl (zeroGateArcTolerance y)) hM').trans
      (chord_margin hy.le hyx.le (by linarith only [hx']))

/-- After canceling coefficient mass, the deterministic spectral flux
gives a gain of at least √D/(64πJ) relative to scalar occupation. -/
theorem flux_gain {D : ℕ} (hD : 2≤D) {x M J R : ℝ}
    (hx : 0<x) (hM : 0<M) (hJ : 0≤J) (hR : 0≤R)
    (hgap : (D:ℝ)^2*M ≤ 4*π*J*R) :
    let y := x-x/(2*(D:ℝ))
    let h := x*sqrt (D:ℝ)/(2*(D:ℝ)*M)
    sqrt (D:ℝ)*((D:ℝ)*x^(D-1)) ≤ 64*π*J*(h*(y^(D-2)*R)/4) := by
  intro y h
  have hDN : 0 < D := by omega
  have hd : (0:ℝ)<D := Nat.cast_pos.mpr hDN
  have hh : 0≤h := by dsimp only [h]; positivity
  have hy := retain_arc_power hDN (Nat.sub_le D 2) hx.le
  have hxpow : x^(D-1)=x^(D-2)*x := by rw [←pow_succ]; congr 1; omega
  calc
    _ = (x^(D-2)*((D:ℝ)^2*M))*(2*h) := by
      rw [hxpow]
      dsimp only [h]
      field_simp
      ring
    _ ≤ (x^(D-2)*(4*π*J*R))*(2*h) := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hgap (pow_nonneg hx.le _)) (by positivity)
    _ ≤ ((2*y^(D-2))*(4*π*J*R))*(2*h) := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith only [hy]) (by positivity)) (by positivity)
    _ = _ := by ring

#print axioms scale_choice
#print axioms flux_gain
end
end GaloisForLFunctions.HTGeometry.FluxOccupation
