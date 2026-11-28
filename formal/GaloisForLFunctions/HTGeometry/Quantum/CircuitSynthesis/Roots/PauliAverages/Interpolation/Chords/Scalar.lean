import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.Roots.PauliAverages.Interpolation.Packets
import GaloisForLFunctions.HTGeometry.QuantitativeMonomialWallCrossingLaw
import GaloisForLFunctions.HTGeometry.HyperbolicLevyKhintchine

/-! # The chord between two unit phases in the interpolating phase frame -/

open Real
namespace GaloisForLFunctions.HTGeometry.CircuitSynthesis.PauliAverages.Interpolation.Chords
noncomputable section

def chord (u x : ℝ) : ℂ :=
  ((1-u:ℝ):ℂ)*phaseValue (-u*x)+(u:ℂ)*phaseValue ((1-u)*x)

private theorem sine_cubic (x : ℝ) : |sin x-x| ≤ |x|^3/6 := by
  by_cases h : x=0
  · simp [h]
  have he : sin x-x=x*(sinc x-1) := by rw [sinc_of_ne_zero h]; field_simp
  rw [he,abs_mul]
  calc
    _ ≤ |x|*(x^2/6) := mul_le_mul_of_nonneg_left (abs_real_sinc_sub_one_le_sq_div_six x) (abs_nonneg _)
    _ = _ := by rw [pow_succ |x| 2,sq_abs]; ring

/-- Linear imaginary terms cancel, leaving a cubic error; the real
deficit is quadratic and nonnegative. -/
theorem chord_components {u : ℝ} (hu : 0 ≤ u) (hu' : u ≤ 1) (x : ℝ) :
    0 ≤ 1-(chord u x).re ∧ 1-(chord u x).re ≤ x^2/8 ∧ |(chord u x).im| ≤ |x|^3/48 := by
  let v := 1-u
  have hv : 0 ≤ v := sub_nonneg.mpr hu'
  have huv : u+v=1 := by dsimp [v]; ring
  have hq : u*v ≤ 1/4 := by dsimp [v]; nlinarith only [sq_nonneg (u-1/2)]
  have h₂ : u*v*(u^2+v^2) ≤ 1/8 := by
    have hid : u*v*(u^2+v^2)=u*v-2*(u*v)^2 := by dsimp [v]; ring
    rw [hid]
    nlinarith only [sq_nonneg (u*v-1/4)]
  have hr : 1-(chord u x).re=v*(1-cos (-u*x))+u*(1-cos (v*x)) := by
    simp [chord,phaseValue,Complex.exp_mul_I,v,Complex.add_re,Complex.mul_re_ofReal]
    ring
  have hi : (chord u x).im=v*(sin (-u*x)-(-u*x))+u*(sin (v*x)-v*x) := by
    simp [chord,phaseValue,Complex.exp_mul_I,v,Complex.add_im,Complex.mul_im_ofReal]
    ring
  rw [hr,hi]
  refine ⟨add_nonneg (mul_nonneg hv (sub_nonneg.mpr (cos_le_one _)))
    (mul_nonneg hu (sub_nonneg.mpr (cos_le_one _))),?_,?_⟩
  · calc
      _ ≤ v*((-u*x)^2/2)+u*((v*x)^2/2) := add_le_add
        (mul_le_mul_of_nonneg_left (_root_.HTGeometry.one_sub_cos_le_sq_div_two _) hv)
        (mul_le_mul_of_nonneg_left (_root_.HTGeometry.one_sub_cos_le_sq_div_two _) hu)
      _ = (u*v)*(x^2/2) := by dsimp [v]; ring
      _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_right hq (sq_nonneg x)]
  · apply (abs_add_le ..).trans
    rw [abs_mul,abs_mul,abs_of_nonneg hu,abs_of_nonneg hv]
    calc
      _ ≤ v*(|-u*x|^3/6)+u*(|v*x|^3/6) := add_le_add
        (mul_le_mul_of_nonneg_left (sine_cubic _) hv) (mul_le_mul_of_nonneg_left (sine_cubic _) hu)
      _ = (u*v*(u^2+v^2))*(|x|^3/6) := by
        rw [abs_mul,abs_neg,abs_of_nonneg hu,abs_mul,abs_of_nonneg hv]; ring
      _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_right h₂ (pow_nonneg (abs_nonneg x) 3)]

end
end GaloisForLFunctions.HTGeometry.CircuitSynthesis.PauliAverages.Interpolation.Chords
