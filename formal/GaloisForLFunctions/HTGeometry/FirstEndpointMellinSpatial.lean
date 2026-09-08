import GaloisForLFunctions.HTGeometry.FirstEndpointMellin
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! The restored endpoint continuation has the original moving-endpoint derivative. -/
namespace GaloisForLFunctions.HTGeometry
open Complex Filter Topology MeasureTheory Set
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Taylor subtraction and exact restoration preserve the original upper-endpoint source term. -/
theorem firstEndpointMellin_hasDerivAt {F : ℂ → ℝ → ℂ} {w : ℂ} {b C : ℝ}
    (hb : 0 < b) (hw : -2 < w.re) (hw1 : w+1 ≠ 0) (hm : Measurable (F w))
    (hc : ContinuousAt (F w) b)
    (hC : ∀ t ∈ Ioc (0:ℝ) b, ‖F w t-F w 0‖ ≤ C*t) :
    HasDerivAt (fun t => firstEndpointMellin F t w) ((b:ℂ)^w*F w b) b := by
  let g : ℝ → ℂ := fun t => (t:ℂ)^w*(F w t-F w 0)
  have hi : IntervalIntegrable g volume 0 b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hb.le).mpr
      (firstEndpointMellinRemainder_integrable hb.le hw hm hC)
  have hgm : Measurable g := by dsimp [g]; fun_prop
  have hcut : (b:ℂ) ∈ Complex.slitPlane := by simp [Complex.mem_slitPlane_iff,hb]
  have hp := (Complex.hasStrictDerivAt_cpow_const (c := w) hcut).hasDerivAt.comp_ofReal
  have hgc : ContinuousAt g b := hp.continuousAt.mul (hc.sub continuousAt_const)
  have hr := intervalIntegral.integral_hasDerivAt_right hi
    hgm.stronglyMeasurable.stronglyMeasurableAtFilter hgc
  have hr' : HasDerivAt (fun t => firstEndpointMellinRemainder F t w) (g b) b := by
    apply hr.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hb] with t ht
    exact (intervalIntegral.integral_of_le ht.le).symm
  have hP := (Complex.hasStrictDerivAt_cpow_const (c := w+1) hcut).hasDerivAt.comp_ofReal
  have h := ((hP.const_mul (F w 0)).div_const (w+1)).add hr'
  convert! h using 1
  dsimp [g]
  rw [add_sub_cancel_right]
  field_simp [hw1]
  ring

end
end GaloisForLFunctions.HTGeometry
