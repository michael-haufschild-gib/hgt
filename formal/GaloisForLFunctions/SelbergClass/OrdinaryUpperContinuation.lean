import GaloisForLFunctions.SelbergClass.OrdinaryTaylorContinuation
import GaloisForLFunctions.SelbergClass.OrdinaryExponentialMellin

/-!
# Periodic continuation of the ordinary exponential series

The entire Taylor remainder and the polar term continue the exponential series
to the slit plane. Its imaginary period extends throughout the upper half-plane
by the identity theorem.
-/

noncomputable section
open Complex Filter Topology Set MeasureTheory
open RHTower

namespace GaloisForLFunctions.SelbergClass

def ordinaryContinuation (F : ExtendedSelbergClass) (z : ℂ) : ℂ :=
  ordinaryTaylorFunction F z + ordinaryPolarPart F z

theorem analyticOnNhd_ordinaryContinuation (F : ExtendedSelbergClass)
    (hd0 : 0 < F.gammaData.degree) (hd1 : F.gammaData.degree < 1) :
    AnalyticOnNhd ℂ (ordinaryContinuation F) Complex.slitPlane := by
  intro z hz
  exact (analyticOnNhd_ordinaryTaylorFunction F hd0 hd1 z (mem_univ z)).add
    (analyticOnNhd_ordinaryPolarPart F z hz)

theorem ordinaryContinuation_eq_series (F : ExtendedSelbergClass)
    (hd0 : 0 < F.gammaData.degree) (hd1 : F.gammaData.degree < 1)
    {z : ℂ} (hz : 0 < z.re) :
    ordinaryContinuation F z = ordinaryExponentialSeries F z := by
  apply eqOn_rightHalfPlane_of_eq_on_pos_reals
    (fun w hw => analyticOnNhd_ordinaryContinuation F hd0 hd1 w
      (Complex.mem_slitPlane_iff.mpr (.inl hw)))
    (analyticOnNhd_ordinaryExponentialSeries F) _ hz
  intro x hx
  rw [ordinaryContinuation, ordinaryTaylorFunction_eq_mellin_sub_polar F hd0 hd1 hx,
    ordinaryExponentialSeries_eq_mellin F hx, sub_add_cancel, Complex.real_smul]
  push_cast
  ring

theorem analyticOnNhd_ordinaryContinuation_upper (F : ExtendedSelbergClass)
    (hd0 : 0 < F.gammaData.degree) (hd1 : F.gammaData.degree < 1) :
    AnalyticOnNhd ℂ (ordinaryContinuation F) {z : ℂ | 0 < z.im} := by
  intro z hz
  exact analyticOnNhd_ordinaryContinuation F hd0 hd1 z
    (Complex.mem_slitPlane_iff.mpr (.inr (ne_of_gt hz)))

/-- The imaginary period persists throughout the upper half-plane. -/
theorem ordinaryContinuation_periodic_upper (F : ExtendedSelbergClass)
    (hd0 : 0 < F.gammaData.degree) (hd1 : F.gammaData.degree < 1)
    {z : ℂ} (hz : 0 < z.im) :
    ordinaryContinuation F (z + 2 * (Real.pi : ℂ) * I) = ordinaryContinuation F z := by
  have han := analyticOnNhd_ordinaryContinuation_upper F hd0 hd1
  have hshift : AnalyticOnNhd ℂ
      (fun w => ordinaryContinuation F (w + 2 * (Real.pi : ℂ) * I))
      {w : ℂ | 0 < w.im} := by
    intro w hw
    change 0 < w.im at hw
    refine AnalyticAt.comp (g := ordinaryContinuation F)
      (f := fun v : ℂ => v + 2 * (Real.pi : ℂ) * I) (x := w) (han _ ?_) (by fun_prop)
    change 0 < (w + 2 * (Real.pi : ℂ) * I).im
    have he : (w + 2 * (Real.pi : ℂ) * I).im = w.im + 2 * Real.pi := by simp
    rw [he]
    linarith [Real.pi_pos]
  have hnear : (fun w => ordinaryContinuation F (w + 2 * (Real.pi : ℂ) * I))
      =ᶠ[𝓝 (1 + I : ℂ)] ordinaryContinuation F := by
    have hU : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hU.mem_nhds (by norm_num : (1 + I : ℂ) ∈ {w : ℂ | 0 < w.re})] with w hw
    rw [ordinaryContinuation_eq_series F hd0 hd1 (by simpa using hw),
      ordinaryContinuation_eq_series F hd0 hd1 hw,
      ordinaryExponentialSeries_periodic F w]
  exact hshift.eqOn_of_preconnected_of_eventuallyEq han
    (convex_halfSpace_im_gt 0).isPreconnected
    (by norm_num : (1 + I : ℂ) ∈ {w : ℂ | 0 < w.im}) hnear hz

end GaloisForLFunctions.SelbergClass
