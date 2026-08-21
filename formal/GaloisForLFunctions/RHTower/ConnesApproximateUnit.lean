import GaloisForLFunctions.RHTower.ConnesSobolevWeight
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Connes' approximate units in the Sobolev spaces `L²_δ`

Formalization of the uniform-boundedness half of Lemma 4 of Appendix I of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

Appendix I needs an approximate unit `f_n ∈ 𝒮(ℝ)` with `f̂_n` compactly supported, uniformly bounded
`‖V(f_n)‖ ≤ C`, and `V(f_n) → 1` strongly on the weighted space `L²_δ(ℝ)`.  Connes takes
`f_n(v) = n f(n v)` with `f̂ = 1` on `[-1,1]`, and the uniform bound comes from the estimate (5)

  `‖V(g)‖ ≤ c^{1/2} ∫ |g(v)| ρ(v)^{1/2} dv`,   `ρ(v) = (1 + v²)^{δ/2}`,

together with the elementary monotonicity

  `∫ |f_n(v)| ρ(v)^{1/2} dv = ∫ |f(u)| ρ(u/n)^{1/2} du ≤ ∫ |f(u)| ρ(u)^{1/2} du`   (n ≥ 1).

Both are proved here without hypotheses beyond the integrability that defines the estimate (5).
The operator bound (4) itself is `ConnesSobolevWeight.connesSobolevWeight_lintegral_translate_le`.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section
open MeasureTheory Real

/-- **Appendix I (2), monotonicity form.**  Contracting the argument decreases the weight. -/
theorem connesSobolevWeight_div_le {δ : ℝ} (hδ : 0 ≤ δ) {n : ℝ} (hn : 1 ≤ n) (u : ℝ) :
    connesSobolevWeight δ (u / n) ≤ connesSobolevWeight δ u := by
  have hn0 : (0:ℝ) < n := lt_of_lt_of_le one_pos hn
  have hbase : 1 + (u / n) ^ 2 ≤ 1 + u ^ 2 := by
    have hsq : (u / n) ^ 2 ≤ u ^ 2 := by
      rw [div_pow, div_le_iff₀ (by positivity)]
      nlinarith [sq_nonneg u, sq_nonneg (n - 1)]
    linarith
  exact Real.rpow_le_rpow (by positivity) hbase (by linarith)

/-- **Appendix I (6).**  The `L¹(ρ^{1/2})` mass of the rescaled family `f_n(v) = n f(n v)` is
uniformly bounded by that of `f`. -/
theorem connes_approxUnit_mass_le {δ : ℝ} (hδ : 0 ≤ δ) {n : ℝ} (hn : 1 ≤ n) (f : ℝ → ℂ)
    (hfm : AEStronglyMeasurable f volume)
    (hf : Integrable (fun u : ℝ => ‖f u‖ * Real.sqrt (connesSobolevWeight δ u))) :
    (∫ v : ℝ, n * ‖f (n * v)‖ * Real.sqrt (connesSobolevWeight δ v))
      ≤ ∫ u : ℝ, ‖f u‖ * Real.sqrt (connesSobolevWeight δ u) := by
  have hn0 : (0:ℝ) < n := lt_of_lt_of_le one_pos hn
  set g : ℝ → ℝ := fun u => ‖f u‖ * Real.sqrt (connesSobolevWeight δ (u / n)) with hg
  have hpt : ∀ v : ℝ, n * ‖f (n * v)‖ * Real.sqrt (connesSobolevWeight δ v) = n * g (n * v) := by
    intro v
    have hdiv : n * v / n = v := by field_simp
    rw [hg]
    simp only [hdiv]
    ring
  have hshift : (∫ v : ℝ, g (n * v)) = |n⁻¹| * ∫ u : ℝ, g u := by
    have h := Measure.integral_comp_mul_left g n
    simpa [smul_eq_mul] using h
  have habs : |n⁻¹| = n⁻¹ := abs_of_pos (by positivity)
  have hstep : (∫ v : ℝ, n * ‖f (n * v)‖ * Real.sqrt (connesSobolevWeight δ v))
      = ∫ u : ℝ, g u := by
    simp only [hpt]
    rw [MeasureTheory.integral_const_mul, hshift, habs, ← mul_assoc,
      mul_inv_cancel₀ (ne_of_gt hn0), one_mul]
  rw [hstep]
  refine integral_mono ?_ hf ?_
  · have hweight : Continuous fun u : ℝ => Real.sqrt (connesSobolevWeight δ (u / n)) := by
      refine Real.continuous_sqrt.comp ?_
      refine Continuous.rpow_const ?_ (fun x => Or.inl (by positivity))
      fun_prop
    refine Integrable.mono' hf (hfm.norm.mul hweight.aestronglyMeasurable) ?_
    · filter_upwards with u
      have hsq : Real.sqrt (connesSobolevWeight δ (u / n))
          ≤ Real.sqrt (connesSobolevWeight δ u) :=
        Real.sqrt_le_sqrt (connesSobolevWeight_div_le hδ hn u)
      rw [Real.norm_eq_abs, hg, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left hsq (norm_nonneg _)
  · intro u
    have hsq : Real.sqrt (connesSobolevWeight δ (u / n))
        ≤ Real.sqrt (connesSobolevWeight δ u) :=
      Real.sqrt_le_sqrt (connesSobolevWeight_div_le hδ hn u)
    exact mul_le_mul_of_nonneg_left hsq (norm_nonneg _)

end

end GaloisForLFunctions.RHTower
