import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! # Lower chord slope on the first quarter circle -/
open Real Set
namespace GaloisForLFunctions.HTGeometry.FirstAscent

/-- Sine has slope at least one half throughout the initial quarter circle. -/
theorem sine_chord_floor {x y : ℝ} (hx : 0≤x) (hxy : x≤y) (hy : y≤π/4) :
    y-x ≤ 2*(sin y-sin x) := by
  rcases hxy.eq_or_lt with rfl | h
  · simp
  obtain ⟨c,hc,hd⟩ := exists_hasDerivAt_eq_slope sin cos h continuous_sin.continuousOn
    (fun u _ => hasDerivAt_sin u)
  have hcos := cos_le_cos_of_nonneg_of_le_pi (hx.trans hc.1.le)
    (show π/3≤π by linarith only [pi_pos]) (show c≤π/3 by linarith only [hc.2,hy,pi_pos])
  rw [cos_pi_div_three,hd] at hcos
  linarith only [(le_div_iff₀ (sub_pos.mpr h)).mp hcos]

end GaloisForLFunctions.HTGeometry.FirstAscent
