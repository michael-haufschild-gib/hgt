import GaloisForLFunctions.HTGeometry.BarnesSingleZetaShiftEquation
import GaloisForLFunctions.HTGeometry.UniformThirdOrderJet

/-! Cubic endpoint subtraction gives the sharp Mellin integrability strip. -/

namespace GaloisForLFunctions.HTGeometry
open Set MeasureTheory
noncomputable section
set_option autoImplicit false

/-- A measurable `O(z³)` endpoint remainder may be multiplied by `z^w` on
`(0,1]` exactly throughout the strip `-4 < Re w`. -/
theorem integrableOn_cpow_mul_of_cubic_bound {F : ℝ → ℂ} {C : ℝ} {w : ℂ}
    (hw : -4 < w.re)
    (hmeas : AEStronglyMeasurable (fun z : ℝ => (z : ℂ) ^ w * F z)
      (volume.restrict (Ioc (0 : ℝ) 1)))
    (hbound : ∀ z ∈ Ioc (0 : ℝ) 1, ‖F z‖ ≤ C * z ^ 3) :
    IntegrableOn (fun z : ℝ => (z : ℂ) ^ w * F z) (Ioc 0 1) := by
  have hbase : IntegrableOn (fun z : ℝ => (z : ℂ) ^ (w + 3)) (Ioc (0 : ℝ) 1) := by
    have hs : 0 < (w + 4).re := by
      norm_num [Complex.add_re]
      linarith
    have h := integrableOn_cpow_Ioc (s := w + 4) hs
    convert h using 1
    all_goals ring_nf
  change Integrable (fun z : ℝ => (z : ℂ) ^ w * F z) (volume.restrict (Ioc 0 1))
  have hmajor : Integrable (fun z : ℝ => C * ‖(z : ℂ) ^ (w + 3)‖)
      (volume.restrict (Ioc 0 1)) := by
    exact hbase.norm.const_mul C
  apply hmajor.mono' hmeas
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with z hz
  have hz0 : 0 < z := hz.1
  have hzn : 0 ≤ z := hz0.le
  have hF := hbound z hz
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hz0]
  calc
    z ^ w.re * ‖F z‖ ≤ z ^ w.re * (C * z ^ 3) :=
      mul_le_mul_of_nonneg_left hF (Real.rpow_nonneg hzn _)
    _ = C * z ^ (w.re + 3) := by
      have hthree : z ^ (3 : ℝ) = z ^ 3 := Real.rpow_natCast z 3
      rw [Real.rpow_add hz0, hthree]
      ring_nf
    _ = C * ‖(z : ℂ) ^ (w + 3)‖ := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hz0]
      congr 1

end
end GaloisForLFunctions.HTGeometry
