import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AngularError.ChordDiameter

/-! # Unequal chord tolerances and the antipodal threshold -/
open Real
namespace GaloisForLFunctions.HTGeometry.AngularError
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The distance deficit comes from the projection of the sum of the two
endpoints on their common reference direction. It is positive exactly
when the squared input tolerances sum to less than four. -/
def chordBound (e f : ℝ) := sqrt (4-(2-(e^2+f^2)/2)^2)

theorem chordBound_lt_two {e f : ℝ} (h : e^2+f^2<4) : chordBound e f < 2 := by
  apply (sqrt_lt' (by norm_num : (0:ℝ)<2)).mpr
  nlinarith only [sq_pos_of_pos (by linarith only [h] : 0<2-(e^2+f^2)/2)]

theorem common_unequal_chord {x y z : E} {e f : ℝ} (he : 0≤e) (hf : 0≤f)
    (h : e^2+f^2<4) (hx : ‖x‖=‖y‖) (hz : ‖z‖=‖y‖)
    (hxy : ‖x-y‖≤e*‖y‖) (hzy : ‖z-y‖≤f*‖y‖) :
    ‖x-z‖≤chordBound e f*‖y‖ := by
  by_cases hy : ‖y‖=0
  · simp only [norm_eq_zero.mp (hx.trans hy),norm_eq_zero.mp (hz.trans hy),hy,sub_zero,norm_zero,mul_zero,le_refl]
  have hR := lt_of_le_of_ne (norm_nonneg y) (Ne.symm hy)
  let c := 2-(e^2+f^2)/2
  have hc : 0<c := by dsimp only [c]; linarith only [h]
  have hc₂ : c≤2 := by dsimp only [c]; linarith only [sq_nonneg e,sq_nonneg f]
  have hrad : 0≤4-c^2 := by nlinarith only [pow_le_pow_left₀ hc.le hc₂ 2]
  have proj (v : E) (a : ℝ) (ha : 0≤a) (hv : ‖v‖=‖y‖) (hd : ‖v-y‖≤a*‖y‖) :
      (1-a^2/2)*‖y‖^2≤inner ℝ v y := by
    have hs := pow_le_pow_left₀ (norm_nonneg _) hd 2
    rw [norm_sub_sq_real,hv,mul_pow] at hs
    linarith only [hs]
  have hm := real_inner_le_norm (x+z) y
  rw [inner_add_left] at hm
  have hmid : c*‖y‖≤‖x+z‖ := by
    apply le_of_mul_le_mul_right (a:=‖y‖) _ hR
    dsimp only [c]
    linarith only [proj x e he hx hxy,proj z f hf hz hzy,hm]
  have hsq := pow_le_pow_left₀ (mul_nonneg hc.le hR.le) hmid 2
  have hp := parallelogram_law_with_norm_mul (𝕜:=ℝ) x z
  rw [hx,hz] at hp
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (sqrt_nonneg _) hR.le)).mp
  change ‖x-z‖^2≤(sqrt (4-c^2)*‖y‖)^2
  rw [mul_pow,sq_sqrt hrad]
  nlinarith only [hsq,hp]

#print axioms common_unequal_chord
end GaloisForLFunctions.HTGeometry.AngularError
