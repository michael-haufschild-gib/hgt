import GaloisForLFunctions.RHTower.ConnesArchLogIdentification
import GaloisForLFunctions.RHTower.ConnesTwistedChartFourier

/-!
# The twisted-chart change of variables of §VII Theorem 4

The logarithmic term of the trace formula of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068, §VII Theorem 4,

is `−∑_q ∫ ĝ_q(u) log|u| du` with `g_q` the twisted chart of §VII (26).  Substituting `x = u − 1`
turns Connes' regularized principal value of `g_q` into the local Weil integral

  `∫'_{ℝ*} f(q u^{-1}) / |1 − u| d^*u`,        `d^*u = du/(2|u|)`,

so the last §V identification (`connes_arch_logPV_identification`) rewrites the logarithmic term
of Theorem 4 exactly as Connes states it.
-/

open MeasureTheory Set Filter Topology Real
open scoped SchwartzMap FourierTransform

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- The twisted local Weil integrand at the real place, `f(q u^{-1}) / |1 − u| d^*u`.
(The name `connesArchWeilIntegrand` is already taken by the one-sided power test of Appendix II.) -/
def connesTwistedWeilIntegrand (f : ℝ → ℂ) (q u : ℝ) : ℂ :=
  f (q * u⁻¹) * ((2 * |u| * |u - 1| : ℝ) : ℂ)⁻¹

theorem connes_measurableSet_weilTail (ε : ℝ) : MeasurableSet {u : ℝ | ε ≤ |u - 1|} :=
  measurableSet_le measurable_const ((measurable_id.sub measurable_const).norm)

/-- **The change of variables `x = u − 1`.**  The multiplicative-Haar tail of the twisted chart is
the Weil tail of `f`. -/
theorem connes_twistedChart_haar_subst (f : ℝ → ℂ) (q ε : ℝ) :
    (∫ x in {x : ℝ | ε ≤ |x|},
        connesTwistedChart f q x * ((connesRealMultHaarDensity x : ℝ) : ℂ))
      = ∫ u in {u : ℝ | ε ≤ |u - 1|}, connesTwistedWeilIntegrand f q u := by
  have hSm : MeasurableSet {x : ℝ | ε ≤ |x|} := measurableSet_le measurable_const measurable_norm
  have hTm : MeasurableSet {u : ℝ | ε ≤ |u - 1|} := connes_measurableSet_weilTail ε
  rw [← MeasureTheory.integral_indicator hSm, ← MeasureTheory.integral_indicator hTm,
    ← integral_sub_right_eq_self
      (fun x : ℝ => Set.indicator {x : ℝ | ε ≤ |x|}
        (fun y : ℝ => connesTwistedChart f q y * ((connesRealMultHaarDensity y : ℝ) : ℂ)) x) 1]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  by_cases hu : ε ≤ |u - 1|
  · have h1 : (u - 1) ∈ {x : ℝ | ε ≤ |x|} := hu
    have h2 : u ∈ {u : ℝ | ε ≤ |u - 1|} := hu
    show Set.indicator {x : ℝ | ε ≤ |x|}
        (fun y : ℝ => connesTwistedChart f q y * ((connesRealMultHaarDensity y : ℝ) : ℂ))
        (u - 1)
        = Set.indicator {u : ℝ | ε ≤ |u - 1|} (connesTwistedWeilIntegrand f q) u
    rw [Set.indicator_of_mem h1, Set.indicator_of_mem h2, connesTwistedChart,
      connesRealMultHaarDensity, connesTwistedWeilIntegrand]
    have h3 : u - 1 + 1 = u := by ring
    rw [h3]
    push_cast
    rw [mul_inv, mul_inv]
    ring
  · have h1 : (u - 1) ∉ {x : ℝ | ε ≤ |x|} := hu
    have h2 : u ∉ {u : ℝ | ε ≤ |u - 1|} := hu
    show Set.indicator {x : ℝ | ε ≤ |x|}
        (fun y : ℝ => connesTwistedChart f q y * ((connesRealMultHaarDensity y : ℝ) : ℂ))
        (u - 1)
        = Set.indicator {u : ℝ | ε ≤ |u - 1|} (connesTwistedWeilIntegrand f q) u
    rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]

/-- **The logarithmic term of §VII Theorem 4, at one lattice element.**  The Fourier log moment of
the twisted chart is Connes' regularized local Weil integral. -/
theorem connes_arch_weil_tendsto (f : ℝ → ℂ) (q : ℝ) (G : 𝓢(ℝ, ℂ))
    (hG : ∀ x : ℝ, (G : ℝ → ℂ) x = connesTwistedChart f q x) :
    Tendsto (fun ε : ℝ =>
        (∫ u in {u : ℝ | ε ≤ |u - 1|}, connesTwistedWeilIntegrand f q u)
          + f q * ((Real.log ε : ℝ) : ℂ)) (𝓝[>] 0)
      (𝓝 (- connesFourierLogMoment G
          - f q * ((Real.eulerMascheroniConstant + Real.log (2 * π) : ℝ) : ℂ))) := by
  have h := connes_arch_logPV_identification G
  have h0 : (G : ℝ → ℂ) 0 = f q := by
    rw [hG 0, connesTwistedChart_zero]
  rw [h0] at h
  refine h.congr fun ε => ?_
  rw [connesRealLogPV, h0, ← connes_twistedChart_haar_subst f q ε]
  congr 1
  refine setIntegral_congr_fun (measurableSet_le measurable_const measurable_norm)
    fun x _ => ?_
  rw [hG x]

end

end GaloisForLFunctions.RHTower

namespace GaloisForLFunctions.RHTower

noncomputable section

open MeasureTheory Set Filter Topology Real
open scoped SchwartzMap FourierTransform

/-- **§VII Theorem 4, the logarithmic term rewritten as Connes' `∫'`.**  With the archimedean
normalization of `∫'` — the tail integral regularized by `f(q)(log ε + γ + log 2π)` — the Fourier
log moment of the twisted chart *is* the local Weil term, with no leftover constant:

    −∫_ℝ 𝓕g_q(u) log|u| du  =  ∫'_{ℝ*} f(q u^{-1}) / |1 − u| d^*u.  -/
theorem connes_arch_weil_regularized (f : ℝ → ℂ) (q : ℝ) (G : 𝓢(ℝ, ℂ))
    (hG : ∀ x : ℝ, (G : ℝ → ℂ) x = connesTwistedChart f q x) :
    Tendsto (fun ε : ℝ =>
        (∫ u in {u : ℝ | ε ≤ |u - 1|}, connesTwistedWeilIntegrand f q u)
          + f q * ((Real.log ε + Real.eulerMascheroniConstant + Real.log (2 * π) : ℝ) : ℂ))
      (𝓝[>] 0) (𝓝 (- connesFourierLogMoment G)) := by
  have h := connes_arch_weil_tendsto f q G hG
  have h2 := h.add_const (f q * ((Real.eulerMascheroniConstant + Real.log (2 * π) : ℝ) : ℂ))
  have hval : (- connesFourierLogMoment G
        - f q * ((Real.eulerMascheroniConstant + Real.log (2 * π) : ℝ) : ℂ))
      + f q * ((Real.eulerMascheroniConstant + Real.log (2 * π) : ℝ) : ℂ)
      = - connesFourierLogMoment G := by ring
  rw [hval] at h2
  refine h2.congr fun ε => ?_
  push_cast
  ring

end

end GaloisForLFunctions.RHTower
