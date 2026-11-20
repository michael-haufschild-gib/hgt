import GaloisForLFunctions.goldbach.LiLiu.ModelConvolution
import Mathlib.Analysis.MellinTransform

/-! # Normalization of the additive sum and difference convolutions

Fix a positive argument r of one weight and write the other as ru.
The sum then has y = r(1+u), and the positive difference has y = r(1−u).
-/

namespace GaloisForLFunctions.Goldbach.LiLiu
open MeasureTheory Set _root_.Complex
noncomputable section

def shapeDomain (d : ℝ) := {u : ℝ | 0 < u ∧ 0 < 1+d*u}

theorem measurableSet_shapeDomain (d : ℝ) : MeasurableSet (shapeDomain d) :=
  measurableSet_Ioi.inter (measurableSet_lt measurable_const (measurable_const.add (measurable_const.mul measurable_id)))

theorem shapeDomain_add : shapeDomain 1 = Ioi 0 := by
  ext u
  change (0 < u ∧ 0 < 1+1*u) ↔ 0 < u
  exact ⟨And.left, fun h => ⟨h, by linarith only [h]⟩⟩

theorem shapeDomain_sub : shapeDomain (-1) = Ioo 0 1 := by
  ext u
  change (0 < u ∧ 0 < 1+ -1*u) ↔ (0 < u ∧ u < 1)
  constructor <;> rintro ⟨h,h'⟩ <;> exact ⟨h, by linarith only [h']⟩

private theorem affine_integral (f : ℝ → ℂ) {r d : ℝ} (hr : 0 < r) (hd : d^2 = 1) :
    (∫ y : ℝ, f y) = (r : ℂ) * ∫ u : ℝ, f (r*(1+d*u)) := by
  have hs := Measure.integral_comp_mul_left f r
  rw [abs_of_pos (inv_pos.mpr hr), Complex.real_smul, ofReal_inv] at hs
  have hscale : (∫ y : ℝ, f y) = (r : ℂ) * ∫ u : ℝ, f (r*u) := by
    rw [hs, ← mul_assoc, mul_inv_cancel₀ (ofReal_ne_zero.mpr hr.ne'), one_mul]
  rw [hscale]
  congr 1
  rcases sq_eq_one_iff.mp hd with rfl | rfl
  · simpa only [one_mul] using (integral_add_left_eq_self (fun u : ℝ => f (r*u)) 1).symm
  · simpa only [neg_one_mul, ← sub_eq_add_neg] using
      (integral_sub_left_eq_self (fun u : ℝ => f (r*u)) volume 1).symm

/-- The Jacobian contributes one full power of r to the Mellin weight. -/
theorem oriented_weight_integral (φ : TestWeight) {r d : ℝ} (hr : 0 < r) (hd : d^2 = 1) (w : ℂ) :
    (∫ y in Ioi (0:ℝ), (y:ℂ)^(w-1) * (φ (d*(y-r)) : ℂ)) =
      (r:ℂ)^w * ∫ u in shapeDomain d, ((1+d*u:ℝ):ℂ)^(w-1) * (φ (r*u):ℂ) := by
  let f (y : ℝ) := (y:ℂ)^(w-1) * (φ (d*(y-r)):ℂ)
  let g (u : ℝ) := ((1+d*u:ℝ):ℂ)^(w-1) * (φ (r*u):ℂ)
  have hscale (u : ℝ) : d*(r*(1+d*u)-r) = r*u := by linear_combination (r*u)*hd
  have ht (u : ℝ) : (Ioi (0:ℝ)).indicator f (r*(1+d*u)) =
      (r:ℂ)^(w-1) * (shapeDomain d).indicator g u := by
    by_cases h : 0 < 1+d*u
    · have hy : r*(1+d*u) ∈ Ioi (0:ℝ) := mul_pos hr h
      rw [indicator_of_mem hy]
      by_cases hu : 0 < u
      · rw [indicator_of_mem (show u ∈ shapeDomain d from ⟨hu,h⟩)]
        simp only [f,g,hscale,ofReal_mul,mul_cpow_ofReal_nonneg hr.le h.le,mul_assoc]
      · have hz : φ (r*u) = 0 := by
          by_contra! hn
          have H := (φ.supported hn).1
          linarith only [H,mul_nonpos_of_nonneg_of_nonpos hr.le (le_of_not_gt hu)]
        rw [indicator_of_notMem (show u ∉ shapeDomain d from fun H => hu H.1)]
        simp [f,hscale,hz]
    · have hy : r*(1+d*u) ∉ Ioi (0:ℝ) := not_lt.mpr (mul_nonpos_of_nonneg_of_nonpos hr.le (le_of_not_gt h))
      rw [indicator_of_notMem hy,indicator_of_notMem (show u ∉ shapeDomain d from fun H => h H.2),mul_zero]
  change (∫ y in Ioi (0:ℝ), f y) = (r:ℂ)^w * ∫ u in shapeDomain d, g u
  rw [← integral_indicator measurableSet_Ioi, affine_integral _ hr hd]
  simp_rw [ht]
  have he := cpow_add (1:ℂ) (w-1) (ofReal_ne_zero.mpr hr.ne')
  rw [show 1+(w-1)=w by ring,cpow_one] at he
  rw [integral_const_mul, integral_indicator (measurableSet_shapeDomain d), ← mul_assoc, ← he]

#print axioms oriented_weight_integral
end
end GaloisForLFunctions.Goldbach.LiLiu
