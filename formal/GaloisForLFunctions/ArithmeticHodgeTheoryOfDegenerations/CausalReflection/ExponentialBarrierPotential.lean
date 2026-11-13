import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ConfiningHalfLineArithmeticBounds

/-!
# Absorption of exponential barrier rows

Every exponential of order below eight is absorbed by the actual confining
potential up to a constant. The admissible barrier interval is exactly the
one for which its growing prime row has order below eight.
-/

set_option autoImplicit false
noncomputable section
open Filter Topology
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

/-- A faster positive exponential absorbs a slower positive exponential on the positive ray. -/
theorem exists_exponential_absorption {a c p q : ℝ}
    (ha : 0 < a) (hc : 0 ≤ c) (hp : 0 ≤ p) (hpq : p < q) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ, 0 ≤ x → c * Real.exp (p * x) ≤ a * Real.exp (q * x) + B := by
  have hdecay : Tendsto (fun x : ℝ => c * Real.exp (-((q - p) * x))) atTop (𝓝 0) := by
    have hscale : Tendsto (fun x : ℝ => (q - p) * x) atTop atTop :=
      tendsto_id.const_mul_atTop (sub_pos.mpr hpq)
    simpa only [Function.comp_def, mul_zero] using
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp hscale).const_mul c
  obtain ⟨Y, hYsmall⟩ := (hdecay.eventually (gt_mem_nhds ha)).exists
  refine ⟨c * Real.exp (p * Y), mul_nonneg hc (Real.exp_pos _).le, ?_⟩
  intro x _hx
  by_cases hxy : x ≤ Y
  · have hb := mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hxy hp)) hc
    exact hb.trans (le_add_of_nonneg_left (mul_nonneg ha.le (Real.exp_pos _).le))
  · have hyx : Y ≤ x := (lt_of_not_ge hxy).le
    have hexp : Real.exp (-((q - p) * x)) ≤ Real.exp (-((q - p) * Y)) :=
      Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left hyx (sub_pos.mpr hpq).le))
    have hs := (mul_le_mul_of_nonneg_left hexp hc).trans hYsmall.le
    have hm := mul_le_mul_of_nonneg_right hs (Real.exp_pos (q * x)).le
    have he : c * Real.exp (-((q - p) * x)) * Real.exp (q * x) = c * Real.exp (p * x) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    rw [he] at hm
    exact hm.trans (le_add_of_nonneg_right (mul_nonneg hc (Real.exp_pos _).le))

/-- The complete prime-row majorant and both required barrier weights fit below the potential. -/
theorem exists_exponentialBarrier_potentialDominance {a β : ℝ}
    (ha : 0 < a) (hβ : 1 / 2 < β) (hβupper : β < 15 / 2) (V : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ u : ℝ, u ≤ 0 →
      6 * Real.exp (-((β + 1 / 2) * u)) + V + Real.exp (-(β * u)) +
        Real.exp (-((β + 1 / 2) * u)) ≤ a * Real.exp (-(8 * u)) + B := by
  have hp : 0 ≤ β + 1 / 2 := by linarith only [hβ]
  have hpq : β + 1 / 2 < 8 := by linarith only [hβupper]
  obtain ⟨C, hC, hbound⟩ := exists_exponential_absorption ha (by norm_num : (0 : ℝ) ≤ 8) hp hpq
  refine ⟨C + |V|, add_nonneg hC (abs_nonneg _), ?_⟩
  intro u hu
  have hb := hbound (-u) (neg_nonneg.mpr hu)
  have he : Real.exp (-(β * u)) ≤ Real.exp (-((β + 1 / 2) * u)) := by
    apply Real.exp_le_exp.mpr
    nlinarith only [hu]
  simp only [mul_neg] at hb
  linarith only [hb, he, le_abs_self V]

#print axioms exists_exponentialBarrier_potentialDominance
end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
