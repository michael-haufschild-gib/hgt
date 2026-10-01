import GaloisForLFunctions.RHTower.ChiGradedStationaryEntropy
import GaloisForLFunctions.RHTower.OscillatoryIntegralComplexAmplitude
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

open Complex MeasureTheory Topology
noncomputable section
namespace RHTower

/-- The entropy phase extends continuously through zero. -/
theorem continuous_chiStationaryEntropy_grade (a k : ℝ) :
    Continuous (fun t : ℝ => bourgainOscillation (-k * chiStationaryEntropy a t)) := by
  have he : chiStationaryEntropy a = fun t : ℝ =>
      t * Real.log t - t * Real.log a - t + a := by
    funext t
    unfold chiStationaryEntropy
    ring
  have hd : Continuous (chiStationaryEntropy a) := by
    rw [he]
    exact ((Real.continuous_mul_log.sub
      (continuous_id.mul continuous_const)).sub continuous_id).add continuous_const
  have hc : Continuous (fun x : ℝ => bourgainOscillation (-k * x)) := by
    unfold bourgainOscillation
    fun_prop
  exact hc.comp hd

/-- Positive grading improves the full exterior primitive bound by its
exact reciprocal factor. -/
theorem norm_integral_chiStationaryEntropy_grade_exterior_le {a k h l u : ℝ}
    (ha : 0 < a) (hk : 0 < k) (hh : 0 < h) (hl : a / 2 ≤ l)
    (hlu : l ≤ u) (hu : u ≤ 2 * a) (hside : u ≤ a - h ∨ a + h ≤ l) :
    ‖∫ t in l..u, bourgainOscillation (-k * chiStationaryEntropy a t)‖ ≤
      16 * a / (k * h) := by
  have hside' : k * u ≤ k * a - k * h ∨ k * a + k * h ≤ k * l := by
    rcases hside with hs | hs
    · left
      nlinarith [mul_le_mul_of_nonneg_left hs hk.le]
    · right
      nlinarith [mul_le_mul_of_nonneg_left hs hk.le]
  have hb := norm_integral_chiStationaryEntropy_neg_exterior_le
    (mul_pos hk ha) (mul_pos hk hh)
    (show (k * a) / 2 ≤ k * l by nlinarith [mul_le_mul_of_nonneg_left hl hk.le])
    (mul_le_mul_of_nonneg_left hlu hk.le)
    (show k * u ≤ 2 * (k * a) by nlinarith [mul_le_mul_of_nonneg_left hu hk.le]) hside'
  rw [integral_chiStationaryEntropy_grade_eq ha hk, norm_mul]
  have hn : ‖(k⁻¹ : ℂ)‖ = k⁻¹ := by
    rw [show (k⁻¹ : ℂ) = ((k⁻¹ : ℝ) : ℂ) by norm_cast,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hk)]
  rw [hn]
  calc
    _ ≤ k⁻¹ * (16 * (k * a) / (k * h)) :=
      mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hk.le)
    _ = _ := by field_simp

/-- Complex amplitudes retain the exterior gain, paying their endpoint
value and complete derivative variation. -/
theorem norm_integral_complexAmplitude_mul_entropy_grade_exterior_le
    {a k h l u : ℝ} (ha : 0 < a) (hk : 0 < k) (hh : 0 < h)
    (hl : a / 2 ≤ l) (hlu : l ≤ u) (hu : u ≤ 2 * a)
    (hside : u ≤ a - h ∨ a + h ≤ l) {v v' : ℝ → ℂ}
    (hv : ∀ x ∈ Set.uIcc l u, HasDerivAt v (v' x) x)
    (hv' : IntervalIntegrable v' volume l u) :
    ‖∫ t in l..u, v t * bourgainOscillation (-k * chiStationaryEntropy a t)‖ ≤
      (16 * a / (k * h)) * (‖v u‖ + ∫ t in l..u, ‖v' t‖) := by
  let g : ℝ → ℂ := fun t => bourgainOscillation (-k * chiStationaryEntropy a t)
  let G : ℝ → ℂ := fun x => ∫ t in l..x, g t
  have hg : Continuous g := continuous_chiStationaryEntropy_grade a k
  apply norm_integral_complexAmplitude_mul_deriv_le hlu hv (v := G) (v' := g)
  · intro x _
    exact intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable l x)
      (hg.stronglyMeasurableAtFilter volume (nhds x)) hg.continuousAt
  · exact hv'
  · exact hg.intervalIntegrable l u
  · exact intervalIntegral.integral_same
  · intro x hx
    have hs : x ≤ a - h ∨ a + h ≤ l := by
      rcases hside with hs | hs
      · exact Or.inl (hx.2.trans hs)
      · exact Or.inr hs
    exact norm_integral_chiStationaryEntropy_grade_exterior_le ha hk hh hl hx.1
      (hx.2.trans hu) hs

end RHTower
