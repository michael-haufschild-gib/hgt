import GaloisForLFunctions.HTGeometry.IntervalRiemannSum

/-! # Unit-interval sampling with a quantitative error bound -/

namespace GaloisForLFunctions.HTGeometry
open Filter Topology MeasureTheory
open scoped NNReal
noncomputable section

def unitRiemannSum (f : ℝ → ℂ) (n : ℕ) : ℂ :=
  (1 / ((n : ℝ) + 1) : ℝ) •
    ∑ i ∈ Finset.range (n + 1), f ((i : ℝ) / ((n : ℝ) + 1))

theorem unitRiemannSum_error_le {f : ℝ → ℂ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (n : ℕ) :
    ‖unitRiemannSum f n - ∫ x in (0 : ℝ)..1, f x‖ ≤ K / ((n : ℝ) + 1) := by
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hnode (i : ℕ) : uniformNode 0 1 (n + 1) i = i / ((n : ℝ) + 1) := by
    simp [uniformNode]
  have hstep (i : ℕ) :
      uniformNode 0 1 (n + 1) (i + 1) - uniformNode 0 1 (n + 1) i =
        1 / ((n : ℝ) + 1) := by
    simpa using uniformNode_succ_sub (a := 0) (b := 1) (Nat.succ_pos n) i
  have h := norm_intervalIntegral_sub_uniformRiemannSum_le (a := 0) (b := 1)
    (by norm_num) (Nat.succ_pos n)
    (fun i _ => hf.continuous.intervalIntegrable _ _)
    (show 0 ≤ (K : ℝ) / ((n : ℝ) + 1) by positivity) ?_
  · simpa only [sub_zero, hnode, Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, Finset.smul_sum,
      one_mul, unitRiemannSum, norm_sub_rev] using h
  · intro i _ x hx
    have hle : uniformNode 0 1 (n + 1) i ≤ uniformNode 0 1 (n + 1) (i + 1) := by
      have := hstep i
      have : 0 < 1 / ((n : ℝ) + 1) := by positivity
      linarith [hstep i]
    rw [Set.uIoc_of_le hle] at hx
    have hd : dist x (uniformNode 0 1 (n + 1) i) ≤ 1 / ((n : ℝ) + 1) := by
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hx.1.le)]
      linarith [hstep i, hx.2]
    calc
      ‖f x - f (uniformNode 0 1 (n + 1) i)‖ ≤
          (K : ℝ) * dist x (uniformNode 0 1 (n + 1) i) := by
        simpa only [dist_eq_norm] using hf.dist_le_mul x (uniformNode 0 1 (n + 1) i)
      _ ≤ (K : ℝ) * (1 / ((n : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left hd K.coe_nonneg
      _ = (K : ℝ) / ((n : ℝ) + 1) := by ring

theorem tendsto_unitRiemannSum {f : ℝ → ℂ} {K : ℝ≥0}
    (hf : LipschitzWith K f) :
    Tendsto (unitRiemannSum f) atTop (𝓝 (∫ x in (0 : ℝ)..1, f x)) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop := by
    simpa only [Nat.cast_add, Nat.cast_one, Function.comp_def] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun _ => norm_nonneg _) (unitRiemannSum_error_le hf)
    (tendsto_const_nhds.div_atTop hn)

theorem tendsto_real_unitRiemannSum {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) :
    Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1)) *
      ∑ i ∈ Finset.range (n + 1), f ((i : ℝ) / ((n : ℝ) + 1)))
      atTop (𝓝 (∫ x in (0 : ℝ)..1, f x)) := by
  have hc : LipschitzWith K (fun x => (f x : ℂ)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [Complex.isometry_ofReal.dist_eq] using hf.dist_le_mul x y
  have h := (Complex.continuous_re.tendsto _).comp (tendsto_unitRiemannSum hc)
  simpa only [Function.comp_def, unitRiemannSum, intervalIntegral.integral_ofReal,
    Complex.smul_re, Complex.re_sum, Complex.ofReal_re, smul_eq_mul] using h

end
end GaloisForLFunctions.HTGeometry
