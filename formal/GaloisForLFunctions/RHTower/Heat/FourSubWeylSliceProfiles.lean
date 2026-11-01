import GaloisForLFunctions.ArithmeticHarmonicAnalysis.SubWeylZetaProfiles
import GaloisForLFunctions.RHTower.Heat.SizeOnlyRepairNearTheWeylFloor

/-! # Four sub-Weyl size profiles for the xi slice

Interpolation at the four proved zeta source points gives four affine
slice exponents. Their slopes lie between zero and one.
-/

noncomputable section
open Complex MeasureTheory Filter Topology Metric
open scoped ComplexOrder
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.ArithmeticHarmonicAnalysis

namespace RHTower

/-- The final slice slope, obtained from the `5/6` source point. -/
def subWeylGain (η : ℝ) : ℝ := 1 - 2 * (2 / 53 + η) / (1 / 6 + η)

theorem subWeylGain_nonneg {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1 / 20) :
    0 ≤ subWeylGain η := by
  unfold subWeylGain
  rw [sub_nonneg, div_le_one (by positivity)]
  linarith only [hη1]

theorem subWeylGain_le_one {η : ℝ} (hη : 0 < η) : subWeylGain η ≤ 1 := by
  unfold subWeylGain
  have h : 0 ≤ 2 * (2 / 53 + η) / (1 / 6 + η) := by positivity
  linarith only [h]

private theorem mul_le_sum_four {K S P K₁ K₂ K₃ K₄ P₁ P₂ P₃ P₄ : ℝ}
    (hS : 0 ≤ S) (hP : 0 ≤ P) (hK : 0 ≤ K)
    (hKs : K ≤ K₁ + K₂ + K₃ + K₄) (hPs : P ≤ P₁ + P₂ + P₃ + P₄) :
    K * S * P ≤ (K₁ + K₂ + K₃ + K₄) * S * (P₁ + P₂ + P₃ + P₄) :=
  mul_le_mul (mul_le_mul_of_nonneg_right hKs hS) hPs hP (mul_nonneg (hK.trans hKs) hS)

/-- Four actual size profiles for the xi slice throughout the inner strip. -/
theorem exists_norm_xiSliceProduct_le_four_subWeyl_profiles {η R₁ : ℝ}
    (hη : 0 < η) (hη1 : η ≤ 1 / 20) (hR₁ : 1 ≤ R₁) :
    ∃ C : ℝ, 0 < C ∧ ∀ t a c : ℝ, 32 * R₁ + 16 ≤ t → |c| ≤ R₁ → |a| < 1 / 2 + η →
      ‖xiSliceProduct t ((a : ℂ) + (c : ℂ) * I)‖ ≤ C * xiSliceReal t (1 / 2 + 2 * η) *
        (t ^ (-(31 / 200 + 3 / 100 * (1 / 2 - |a|)))
          + t ^ (-(1 / 13 + 3 / 13 * (1 / 2 - |a|)))
          + t ^ (-(1 / 53 + 23 / 53 * (1 / 2 - |a|)))
          + t ^ (-(η + subWeylGain η * (1 / 2 + η - |a|)))) := by
  obtain ⟨C₁, hC₁, h₁⟩ := exists_norm_riemannZeta_le_subWeyl_profile_one hη hη1
  obtain ⟨C₂, hC₂, h₂⟩ := exists_norm_riemannZeta_le_profile_ee_two hη (by linarith only [hη1])
  obtain ⟨C₃, hC₃, h₃⟩ := exists_norm_riemannZeta_le_subWeyl_profile_three hη hη1
  obtain ⟨C₄, hC₄, h₄⟩ := exists_norm_riemannZeta_le_subWeyl_profile_four hη hη1
  obtain ⟨K₁, hK₁⟩ : ∃ K₁,
      K₁ = Real.exp 1 * (2 * (2 * Real.pi) ^ R₁) * (C₁ * (1 + 1 / (2 * η))) ^ 2 := ⟨_, rfl⟩
  obtain ⟨K₂, hK₂⟩ : ∃ K₂,
      K₂ = Real.exp 1 * (2 * (2 * Real.pi) ^ R₁) * (C₂ * (1 + 1 / (2 * η))) ^ 2 := ⟨_, rfl⟩
  obtain ⟨K₃, hK₃⟩ : ∃ K₃,
      K₃ = Real.exp 1 * (2 * (2 * Real.pi) ^ R₁) * (C₃ * (1 + 1 / (2 * η))) ^ 2 := ⟨_, rfl⟩
  obtain ⟨K₄, hK₄⟩ : ∃ K₄,
      K₄ = Real.exp 1 * (2 * (2 * Real.pi) ^ R₁) * (C₄ * (1 + 1 / (2 * η))) ^ 2 := ⟨_, rfl⟩
  have hK₁0 : 0 ≤ K₁ := by rw [hK₁]; positivity
  have hK₂0 : 0 ≤ K₂ := by rw [hK₂]; positivity
  have hK₃0 : 0 ≤ K₃ := by rw [hK₃]; positivity
  have hK₄0 : 0 ≤ K₄ := by rw [hK₄]; positivity
  refine ⟨K₁ + K₂ + K₃ + K₄, by rw [hK₁, hK₂, hK₃, hK₄]; positivity, fun t a c ht hc ha => ?_⟩
  have ht0 : 0 < t := by linarith only [ht, hR₁]
  have hS := xiSliceReal_nonneg t (1 / 2 + 2 * η)
  have hη4 : η ≤ 1 / 4 := by linarith only [hη1]
  have ha2 : |a| ≤ 1 / 2 + 2 * η := by linarith only [ha, hη]
  have hp1 : 0 ≤ t ^ (-(31 / 200 + 3 / 100 * (1 / 2 - |a|))) := by positivity
  have hp2 : 0 ≤ t ^ (-(1 / 13 + 3 / 13 * (1 / 2 - |a|))) := by positivity
  have hp3 : 0 ≤ t ^ (-(1 / 53 + 23 / 53 * (1 / 2 - |a|))) := by positivity
  have hp4 : 0 ≤ t ^ (-(η + subWeylGain η * (1 / 2 + η - |a|))) := by positivity
  have hzt : ∀ c' : ℝ, |c'| ≤ R₁ → 8 ≤ t + c' ∧ t + c' ≤ 2 * t := by
    intro c' hc'
    have h := abs_le.mp hc'
    constructor <;> linarith only [h.1, h.2, ht, hR₁]
  rcases le_or_gt |a| (1 / 9) with hsmall | hmid
  · have he0 : 0 ≤ 33 / 200 + η - 97 / 200 * |a| := by linarith only [hsmall, hη]
    have hb := norm_xiSliceProduct_le_of_zeta_exponent (Cz := C₁)
      (e := 33 / 200 + η - 97 / 200 * |a|) (t := t) (a := a) (c := c)
      hη hη4 hR₁ (by linarith only [hη1, abs_nonneg a]) ht hc
      ha2 (fun c' hc' => by
        obtain ⟨h8, h2t⟩ := hzt c' hc'
        refine (h₁ _ _ (by linarith only [abs_nonneg a]) (by linarith only [hsmall]) h8).trans ?_
        rw [show 33 / 200 + η - 97 / 200 * (1 / 2 + |a| - 1 / 2) =
          33 / 200 + η - 97 / 200 * |a| by ring]
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (by linarith only [h8]) h2t he0) hC₁.le)
    rw [← hK₁] at hb
    have he : 2 * (33 / 200 + η - 97 / 200 * |a|) - (1 / 2 + 2 * η - |a|) =
        -(31 / 200 + 3 / 100 * (1 / 2 - |a|)) := by ring
    rw [he] at hb
    exact hb.trans (mul_le_sum_four hS hp1 hK₁0
      (by linarith only [hK₁0, hK₂0, hK₃0, hK₄0])
      (by linarith only [hp1, hp2, hp3, hp4]))
  rcases le_or_gt |a| (3 / 14) with hsmall | hmid'
  · have he0 : 0 ≤ 1 / 9 + η - 5 / 13 * (|a| - 1 / 9) := by linarith only [hsmall, hη]
    have hb := norm_xiSliceProduct_le_of_zeta_exponent (Cz := C₂)
      (e := 1 / 9 + η - 5 / 13 * (|a| - 1 / 9)) (t := t) (a := a) (c := c)
      hη hη4 hR₁ (by linarith only [hη1, hmid]) ht hc ha2 (fun c' hc' => by
        obtain ⟨h8, h2t⟩ := hzt c' hc'
        refine (h₂ _ _ (by linarith only [hmid]) (by linarith only [hsmall]) h8).trans ?_
        rw [show 1 / 9 + η - 5 / 13 * (1 / 2 + |a| - 11 / 18) =
          1 / 9 + η - 5 / 13 * (|a| - 1 / 9) by ring]
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (by linarith only [h8]) h2t he0) hC₂.le)
    rw [← hK₂] at hb
    have he : 2 * (1 / 9 + η - 5 / 13 * (|a| - 1 / 9)) - (1 / 2 + 2 * η - |a|) =
        -(1 / 13 + 3 / 13 * (1 / 2 - |a|)) := by ring
    rw [he] at hb
    exact hb.trans (mul_le_sum_four hS hp2 hK₂0
      (by linarith only [hK₁0, hK₂0, hK₃0, hK₄0])
      (by linarith only [hp1, hp2, hp3, hp4]))
  rcases le_or_gt |a| (1 / 3) with hsmall | hbig
  · have he0 : 0 ≤ 1 / 14 + η - 15 / 53 * (|a| - 3 / 14) := by linarith only [hsmall, hη]
    have hb := norm_xiSliceProduct_le_of_zeta_exponent (Cz := C₃)
      (e := 1 / 14 + η - 15 / 53 * (|a| - 3 / 14)) (t := t) (a := a) (c := c)
      hη hη4 hR₁ (by linarith only [hη1, hmid']) ht hc ha2 (fun c' hc' => by
        obtain ⟨h8, h2t⟩ := hzt c' hc'
        refine (h₃ _ _ (by linarith only [hmid']) (by linarith only [hsmall]) h8).trans ?_
        rw [show 1 / 14 + η - 15 / 53 * (1 / 2 + |a| - 5 / 7) =
          1 / 14 + η - 15 / 53 * (|a| - 3 / 14) by ring]
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (by linarith only [h8]) h2t he0) hC₃.le)
    rw [← hK₃] at hb
    have he : 2 * (1 / 14 + η - 15 / 53 * (|a| - 3 / 14)) - (1 / 2 + 2 * η - |a|) =
        -(1 / 53 + 23 / 53 * (1 / 2 - |a|)) := by ring
    rw [he] at hb
    exact hb.trans (mul_le_sum_four hS hp3 hK₃0
      (by linarith only [hK₁0, hK₂0, hK₃0, hK₄0])
      (by linarith only [hp1, hp2, hp3, hp4]))
  · have hd : 0 < 1 / 6 + η := by positivity
    have he0 : 0 ≤ (2 / 53 + η) * (1 / 2 + η - |a|) / (1 / 6 + η) :=
      div_nonneg (mul_nonneg (by positivity) (by linarith only [ha])) hd.le
    have he1 : 2 * ((2 / 53 + η) * (1 / 2 + η - |a|) / (1 / 6 + η)) ≤ 1 := by
      rw [mul_div_assoc', div_le_one hd]
      have hdist : 1 / 2 + η - |a| ≤ 1 / 6 + η := by linarith only [hbig]
      have hm := mul_le_mul_of_nonneg_left hdist (show 0 ≤ 2 * (2 / 53 + η) by positivity)
      have hc : 2 * (2 / 53 + η) ≤ 1 := by linarith only [hη1]
      have hm' := mul_le_mul_of_nonneg_right hc hd.le
      nlinarith only [hm, hm']
    have hb := norm_xiSliceProduct_le_of_zeta_exponent (Cz := C₄)
      (e := (2 / 53 + η) * (1 / 2 + η - |a|) / (1 / 6 + η))
      (t := t) (a := a) (c := c) hη hη4 hR₁ he1 ht hc
      ha2 (fun c' hc' => by
        obtain ⟨h8, h2t⟩ := hzt c' hc'
        refine (h₄ _ _ (by linarith only [hbig]) (by linarith only [ha]) h8).trans ?_
        rw [show 1 + η - (1 / 2 + |a|) = 1 / 2 + η - |a| by ring]
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (by linarith only [h8]) h2t he0) hC₄.le)
    rw [← hK₄] at hb
    have he : 2 * ((2 / 53 + η) * (1 / 2 + η - |a|) / (1 / 6 + η)) -
        (1 / 2 + 2 * η - |a|) = -(η + subWeylGain η * (1 / 2 + η - |a|)) := by
      unfold subWeylGain
      ring
    rw [he] at hb
    exact hb.trans (mul_le_sum_four hS hp4 hK₄0
      (by linarith only [hK₁0, hK₂0, hK₃0, hK₄0])
      (by linarith only [hp1, hp2, hp3, hp4]))

end RHTower

#print axioms RHTower.exists_norm_xiSliceProduct_le_four_subWeyl_profiles
