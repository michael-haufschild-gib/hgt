import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.PhysicalTolerance

/-! # Eroding a short enclosing arc while retaining a constant fraction of its mass -/
open Set Real
namespace GaloisForLFunctions.HTGeometry.FluxOccupation
noncomputable section

/-- Increasing the angular width of a subsemicircle by h turns buys at
least h in projective operator error. -/
theorem chord_margin {y x : ℝ} (hy : 0≤y) (hxy : y≤x) (hx : x≤1/2) :
    zeroGateArcTolerance y+(x-y) ≤ zeroGateArcTolerance x := by
  let a := (π*x/2+π*y/2)/2
  let b := (π*x/2-π*y/2)/2
  have hx0 := hy.trans hxy
  have h1 := mul_le_mul_of_nonneg_left hxy Real.pi_pos.le
  have h2 := mul_le_mul_of_nonneg_left hx Real.pi_pos.le
  have hpX := mul_nonneg Real.pi_pos.le hx0
  have hpY := mul_nonneg Real.pi_pos.le hy
  have ha : a ∈ Icc 0 π := by dsimp only [a]; constructor <;> linarith only [h1,h2,hpX,hpY,Real.pi_pos]
  have hthird : a ≤ π/3 := by dsimp only [a]; linarith only [h1,h2,Real.pi_pos]
  have hcos := Real.antitoneOn_cos ha (show π/3 ∈ Icc 0 π from ⟨by positivity,by linarith only [Real.pi_pos]⟩) hthird
  rw [Real.cos_pi_div_three] at hcos
  have hb : 0 ≤ b := by dsimp only [b]; linarith only [h1]
  have hb' : b≤π/2 := by dsimp only [b]; linarith only [h2,hpY,Real.pi_pos]
  have hs := Real.mul_le_sin hb hb'
  have hn : 0 ≤ 2/π*b := by positivity
  have h := mul_le_mul hcos hs hn (by linarith only [hcos])
  have he : sin (π*x/2)-sin (π*y/2)=2*cos a*sin b := by
    rw [Real.sin_sub_sin]
    change 2*sin b*cos a=2*cos a*sin b
    ring
  have hscale : 4*((1/2:ℝ)*(2/π*b))=x-y := by dsimp only [b]; field_simp; ring
  unfold zeroGateArcTolerance
  linarith only [h,he,hscale]

/-- Removing one half of a 1/D share of arc width loses at most half
the box mass in all dimensions n≤D. -/
theorem retain_arc_power {D n : ℕ} (hD : 0 < D) (hn : n≤D) {x : ℝ} (hx : 0≤x) :
    x^n/2 ≤ (x-x/(2*(D:ℝ)))^n := by
  let u := 1/(2*(D:ℝ))
  have hD' : (0:ℝ)<D := Nat.cast_pos.mpr hD
  have hD1 : (1:ℝ)≤D := by exact_mod_cast hD
  have hu : 0≤u := by dsimp only [u]; positivity
  have hu' : u≤1/2 := by
    dsimp only [u]
    apply one_div_le_one_div_of_le (by norm_num)
    linarith only [hD1]
  have hh := one_add_mul_le_pow (a := -u) (by linarith only [hu']) n
  have hm := mul_le_mul_of_nonneg_right (show (n:ℝ)≤D by exact_mod_cast hn) hu
  have hd : (D:ℝ)*u=1/2 := by dsimp only [u]; field_simp
  have hp : 1/2 ≤ (1-u)^n := by
    rw [←sub_eq_add_neg] at hh
    linarith only [hh,hm,hd]
  rw [show x-x/(2*(D:ℝ))=x*(1-u) by dsimp only [u]; ring,mul_pow]
  linarith only [mul_le_mul_of_nonneg_left hp (pow_nonneg hx n)]

#print axioms chord_margin
#print axioms retain_arc_power
end
end GaloisForLFunctions.HTGeometry.FluxOccupation
