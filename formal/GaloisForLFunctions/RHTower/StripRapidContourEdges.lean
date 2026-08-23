import GaloisForLFunctions.PNTPlus.ResidueCalcOnRectangles
import GaloisForLFunctions.HTGeometry.LogWeightedPoisson
import GaloisForLFunctions.RHTower.LPropertyStrips

/-!
# Contour edges from strip-rapid decrease

Two generic consequences of Burnol's all-order strip decay are kept in a lightweight module so
unrelated analytic developments can use them without importing the Möbius line-shift stack.
-/

open Complex Set Topology Filter MeasureTheory

namespace RHTower

noncomputable section

/-- Quick decrease on a strip gives integrability on every line of that strip. -/
theorem integrable_line_of_stripRapidDecrease {F : ℂ → ℂ} (hF : HasStripRapidDecrease F)
    {σ : ℝ} (hcont : Continuous fun y : ℝ => F ((σ : ℂ) + (y : ℂ) * I)) :
    Integrable (fun y : ℝ => F ((σ : ℂ) + (y : ℂ) * I)) volume := by
  obtain ⟨T, C, hC0, hbound⟩ := hF σ σ 2
  set T₀ : ℝ := max T 1 with hT₀def
  have hT₀1 : (1 : ℝ) ≤ T₀ := le_max_right _ _
  have hTT₀ : T ≤ T₀ := le_max_left _ _
  obtain ⟨M₀, hM₀⟩ := (isCompact_Icc (a := -T₀) (b := T₀)).exists_bound_of_continuousOn
    hcont.continuousOn
  have hM₀0 : 0 ≤ M₀ := le_trans (norm_nonneg _) (hM₀ 0 (by
    rw [Set.mem_Icc]; constructor <;> linarith))
  set K : ℝ := C + M₀ * (1 + T₀) ^ ((3 : ℝ) / 2) with hKdef
  refine Integrable.mono'
    ((GaloisForLFunctions.HTGeometry.integrable_one_add_abs_rpow_three_halves).const_mul K)
    hcont.aestronglyMeasurable ?_
  filter_upwards with y
  have hbase : (0 : ℝ) < 1 + |y| := by positivity
  have hone : (1 : ℝ) ≤ 1 + |y| := by simp [abs_nonneg]
  have hpos : (0 : ℝ) < (1 + |y|) ^ (-((3 : ℝ) / 2)) := Real.rpow_pos_of_pos hbase _
  rcases le_or_gt |y| T₀ with hy | hy
  · have hval : ‖F ((σ : ℂ) + (y : ℂ) * I)‖ ≤ M₀ := by
      refine hM₀ y ?_
      rw [Set.mem_Icc]
      constructor <;> [linarith [neg_abs_le y]; linarith [le_abs_self y]]
    have hw : (1 : ℝ) ≤
        (1 + |y|) ^ (-((3 : ℝ) / 2)) * (1 + T₀) ^ ((3 : ℝ) / 2) := by
      have h1 : (1 + |y|) ^ ((3 : ℝ) / 2) ≤ (1 + T₀) ^ ((3 : ℝ) / 2) :=
        Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
      have hpos' : (0 : ℝ) < (1 + |y|) ^ ((3 : ℝ) / 2) :=
        Real.rpow_pos_of_pos hbase _
      rw [Real.rpow_neg hbase.le, inv_mul_eq_div, le_div_iff₀ hpos']
      linarith
    calc
      ‖F ((σ : ℂ) + (y : ℂ) * I)‖ ≤ M₀ := hval
      _ = M₀ * 1 := by ring
      _ ≤ M₀ * ((1 + |y|) ^ (-((3 : ℝ) / 2)) * (1 + T₀) ^ ((3 : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_left hw hM₀0
      _ = (M₀ * (1 + T₀) ^ ((3 : ℝ) / 2)) * (1 + |y|) ^ (-((3 : ℝ) / 2)) := by
        ring
      _ ≤ K * (1 + |y|) ^ (-((3 : ℝ) / 2)) := by
        refine mul_le_mul_of_nonneg_right ?_ hpos.le
        rw [hKdef]
        linarith
  · have hyT : T ≤ |y| := le_trans hTT₀ hy.le
    have hre : ((σ : ℂ) + (y : ℂ) * I).re = σ := by simp
    have him : |((σ : ℂ) + (y : ℂ) * I).im| = |y| := by simp
    have hval := hbound ((σ : ℂ) + (y : ℂ) * I) (by rw [hre]) (by rw [hre])
      (by rw [him]; exact hyT)
    rw [him] at hval
    have hmono : (1 + |y|) ^ (-(2 : ℝ)) ≤ (1 + |y|) ^ (-((3 : ℝ) / 2)) :=
      Real.rpow_le_rpow_of_exponent_le hone (by norm_num)
    calc
      ‖F ((σ : ℂ) + (y : ℂ) * I)‖ ≤ C * (1 + |y|) ^ (-((2 : ℕ) : ℝ)) := hval
      _ ≤ C * (1 + |y|) ^ (-((3 : ℝ) / 2)) := by
        refine mul_le_mul_of_nonneg_left ?_ hC0
        simpa using hmono
      _ ≤ K * (1 + |y|) ^ (-((3 : ℝ) / 2)) := by
        refine mul_le_mul_of_nonneg_right ?_ hpos.le
        rw [hKdef]
        have : (0 : ℝ) ≤ M₀ * (1 + T₀) ^ ((3 : ℝ) / 2) := by positivity
        linarith

/-- Strip-rapid decrease kills every bounded horizontal edge along escaping heights. -/
theorem tendsto_hIntegral_of_stripRapidDecrease {F : ℂ → ℂ} (hF : HasStripRapidDecrease F)
    {x₁ x₂ : ℝ} {h : ℕ → ℝ} (hh : Tendsto (fun n : ℕ => |h n|) atTop atTop) :
    Tendsto (fun n : ℕ => HIntegral F x₁ x₂ (h n)) atTop (𝓝 0) := by
  obtain ⟨T, C, hC0, hbound⟩ := hF (min x₁ x₂) (max x₁ x₂) 1
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hmaj : Tendsto
      (fun n : ℕ => C * (1 + |h n|) ^ (-(1 : ℝ)) * |x₂ - x₁|) atTop (𝓝 0) := by
    have hinv : Tendsto (fun n : ℕ => (1 + |h n|) ^ (-(1 : ℝ))) atTop (𝓝 0) := by
      have hgo : Tendsto (fun n : ℕ => 1 + |h n|) atTop atTop :=
        Filter.tendsto_atTop_add_const_left _ 1 hh
      exact (tendsto_rpow_neg_atTop (y := (1 : ℝ)) (by norm_num)).comp hgo
    simpa using (hinv.const_mul C).mul_const |x₂ - x₁|
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmaj
    (Eventually.of_forall fun n => norm_nonneg _) ?_
  filter_upwards [hh.eventually_ge_atTop T] with n hn
  have hpt : ∀ x ∈ Set.uIoc x₁ x₂,
      ‖F ((x : ℂ) + ((h n : ℝ) : ℂ) * I)‖ ≤
        C * (1 + |h n|) ^ (-(1 : ℝ)) := by
    intro x hx
    rw [Set.mem_uIoc] at hx
    have hx1 : min x₁ x₂ ≤ x := by
      rcases hx with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact le_trans (min_le_left _ _) h1.le
      · exact le_trans (min_le_right _ _) h1.le
    have hx2 : x ≤ max x₁ x₂ := by
      rcases hx with ⟨_, h2⟩ | ⟨_, h2⟩
      · exact le_trans h2 (le_max_right _ _)
      · exact le_trans h2 (le_max_left _ _)
    have hre : ((x : ℂ) + ((h n : ℝ) : ℂ) * I).re = x := by simp
    have him : |((x : ℂ) + ((h n : ℝ) : ℂ) * I).im| = |h n| := by simp
    have hval := hbound ((x : ℂ) + ((h n : ℝ) : ℂ) * I)
      (by rw [hre]; exact hx1) (by rw [hre]; exact hx2) (by rw [him]; exact hn)
    rw [him] at hval
    simpa using hval
  exact intervalIntegral.norm_integral_le_of_norm_le_const hpt

end

end RHTower
