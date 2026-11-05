import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheHalfLineLogarithmicGreenKernelIsExplicit
import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheLogarithmicRenewalAverageReadsTheBoundary
import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheLogarithmicBackwardConvolutionHasBoundaryValues

/-!
# Boundary values of the actual logarithmic Green solutions

The variational inverse has a literal renewal representative. Its normalized
boundary trace is the absolutely convergent backward-convolution readout for
forcing that is square-integrable and essentially bounded near the boundary.
-/

open MeasureTheory Set Filter Topology Complex
open scoped InnerProductSpace
noncomputable section

namespace GaloisForLFunctions.CanonicalSystemOfTheWindowTower
open HTGeometry

/-- The actual half-line adjoint is backward convolution followed by half-line restriction. -/
theorem logarithmicCausalOperator_adjoint_coeFn (f : LogarithmicHalfLineL2) :
    (((logarithmicCausalOperator.adjoint f : LogarithmicHalfLineL2) : RealLineL2) : ℝ → ℂ) =ᵐ[volume]
      (Ici (0 : ℝ)).indicator (logarithmicBackwardConvolution (f : RealLineL2)) := by
  rw [← logarithmicHalfLineSchurKernel_adjoint_op]
  filter_upwards [logarithmicHalfLineSchurKernel.adjoint.op_coeFn (f : RealLineL2)] with x hx
  rw [hx]
  change (∫ y : ℝ, starRingEnd ℂ (logarithmicHalfLineSchurKernel.toFun y x) * (f : RealLineL2) y) = _
  by_cases hx0 : 0 ≤ x
  · rw [indicator_of_mem (s := Ici (0 : ℝ)) hx0]
    apply integral_congr_ae
    filter_upwards with y
    simp only [logarithmicHalfLineSchurKernel_toFun, if_pos hx0, Complex.conj_ofReal]
  · rw [indicator_of_notMem (s := Ici (0 : ℝ)) hx0]
    apply integral_eq_zero_of_ae
    filter_upwards with y
    change starRingEnd ℂ (logarithmicHalfLineSchurKernel.toFun y x) * (f : RealLineL2) y = 0
    rw [logarithmicHalfLineSchurKernel_toFun, if_neg hx0, map_zero, zero_mul]

/-- A literal physical representative of the actual logarithmic Green solution. -/
def logarithmicGreenRepresentative (f : LogarithmicHalfLineL2) (x : ℝ) : ℂ :=
  ∫ t in Ioc (0 : ℝ) x, (logarithmicCausalKernel t : ℂ) *
    logarithmicBackwardConvolution (f : RealLineL2) (x - t)

/-- Translation and causality identify the renewal formula with full causal convolution. -/
theorem logarithmicGreenRepresentative_eq_convolution (f : LogarithmicHalfLineL2) (x : ℝ) :
    logarithmicGreenRepresentative f x = ∫ y : ℝ, (logarithmicCausalKernel (x - y) : ℂ) *
      (Ici (0 : ℝ)).indicator (logarithmicBackwardConvolution (f : RealLineL2)) y := by
  let h : ℝ → ℂ := logarithmicBackwardConvolution (f : RealLineL2)
  change (∫ t in Ioc (0 : ℝ) x, (logarithmicCausalKernel t : ℂ) * h (x - t)) =
    ∫ y : ℝ, (logarithmicCausalKernel (x - y) : ℂ) * (Ici (0 : ℝ)).indicator h y
  rw [← integral_sub_left_eq_self
    (fun y : ℝ => (logarithmicCausalKernel (x - y) : ℂ) * (Ici (0 : ℝ)).indicator h y) volume x]
  rw [← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  filter_upwards with t
  rw [sub_sub_cancel]
  by_cases ht : 0 < t
  · by_cases htx : t ≤ x
    · rw [indicator_of_mem (show t ∈ Ioc (0 : ℝ) x from ⟨ht, htx⟩),
        indicator_of_mem (show x - t ∈ Ici (0 : ℝ) from sub_nonneg.mpr htx)]
    · rw [indicator_of_notMem (s := Ioc (0 : ℝ) x) (fun hs => htx hs.2),
        indicator_of_notMem (s := Ici (0 : ℝ)) (fun hs => htx (sub_nonneg.mp hs)), mul_zero]
  · rw [indicator_of_notMem (s := Ioc (0 : ℝ) x) (fun hs => ht hs.1),
      logarithmicCausalKernel_of_nonpos (le_of_not_gt ht), Complex.ofReal_zero, zero_mul]

theorem measurable_logarithmicGreenRepresentative (f : LogarithmicHalfLineL2) :
    Measurable (logarithmicGreenRepresentative f) := by
  have hh : Measurable ((Ici (0 : ℝ)).indicator (logarithmicBackwardConvolution (f : RealLineL2))) :=
    (measurable_logarithmicBackwardConvolution
    (Lp.stronglyMeasurable (f : RealLineL2)).measurable).indicator measurableSet_Ici
  have hm : Measurable (fun p : ℝ × ℝ => (logarithmicCausalKernel (p.1 - p.2) : ℂ) *
      (Ici (0 : ℝ)).indicator (logarithmicBackwardConvolution (f : RealLineL2)) p.2) :=
    (Complex.continuous_ofReal.measurable.comp
    (measurable_logarithmicCausalKernel.comp (measurable_fst.sub measurable_snd))).mul
      (hh.comp measurable_snd)
  have he : logarithmicGreenRepresentative f = fun x : ℝ =>
      ∫ y : ℝ, (logarithmicCausalKernel (x - y) : ℂ) *
        (Ici (0 : ℝ)).indicator (logarithmicBackwardConvolution (f : RealLineL2)) y :=
    funext (logarithmicGreenRepresentative_eq_convolution f)
  rw [he]
  exact hm.stronglyMeasurable.integral_prod_right.measurable

/-- The renewal representative is the actual variational Green solution almost everywhere. -/
theorem logarithmicHalfLineGreenOperator_eq_representative (f : LogarithmicHalfLineL2) :
    (((logarithmicHalfLineGreenOperator f : LogarithmicHalfLineL2) : RealLineL2) : ℝ → ℂ) =ᵐ[volume]
      logarithmicGreenRepresentative f := by
  filter_upwards [logarithmicConvolution_coeFn
    (logarithmicCausalOperator.adjoint f : RealLineL2)] with x hx
  change (logarithmicConvolution (logarithmicCausalOperator.adjoint f : RealLineL2)) x = _
  rw [hx, logarithmicGreenRepresentative_eq_convolution]
  apply integral_congr_ae
  filter_upwards [logarithmicCausalOperator_adjoint_coeFn f] with y hy
  rw [hy]

/-- The boundary coefficient of the actual solution is an absolutely convergent integral. -/
theorem integrable_logarithmicGreen_boundary_readout (f : LogarithmicHalfLineL2)
    {δ C : ℝ} (hδ : 0 < δ) (hb : ∀ᵐ y ∂volume, y ≤ δ → ‖(f : RealLineL2) y‖ ≤ C) :
    Integrable (fun y : ℝ => (logarithmicCausalKernel y : ℂ) * (f : RealLineL2) y) := by
  simpa only [sub_zero] using integrable_logarithmicBackwardConvolution_of_ae_locally_bounded
    (Lp.stronglyMeasurable (f : RealLineL2)).measurable (Lp.memLp (f : RealLineL2)) hδ hb

/-- Every locally bounded L² forcing has an exact normalized trace for its actual Green solution. -/
theorem logarithmicHalfLineGreenOperator_normalized_boundary_limit (f : LogarithmicHalfLineL2)
    {δ C : ℝ} (hδ : 0 < δ) (hC : 0 ≤ C)
    (hb : ∀ᵐ y ∂volume, y ≤ δ → ‖(f : RealLineL2) y‖ ≤ C) :
    Tendsto (fun x : ℝ => logarithmicGreenRepresentative f x *
      (Real.sqrt (Real.log (1 / x)) : ℂ)) (𝓝[>] (0 : ℝ))
      (nhds (∫ y : ℝ, (logarithmicCausalKernel y : ℂ) * (f : RealLineL2) y)) := by
  have hm := (Lp.stronglyMeasurable (f : RealLineL2)).measurable
  have hc := continuousAt_logarithmicBackwardConvolution_of_ae_locally_bounded
    hm (Lp.memLp (f : RealLineL2)) hδ hC hb
  have hl := tendsto_logarithmicCausalConvolution_normalized
    (measurable_logarithmicBackwardConvolution hm) hc.continuousWithinAt
  simpa only [logarithmicGreenRepresentative, logarithmicBackwardConvolution, sub_zero] using hl

#print axioms logarithmicHalfLineGreenOperator_eq_representative
#print axioms integrable_logarithmicGreen_boundary_readout
#print axioms logarithmicHalfLineGreenOperator_normalized_boundary_limit

end GaloisForLFunctions.CanonicalSystemOfTheWindowTower
