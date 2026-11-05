import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheHalfLineLogarithmicFormHasItsActualInverse
import GaloisForLFunctions.HTGeometry.SchurKernelComposition

/-!
# The explicit half-line logarithmic Green kernel

Compress the causal Schur convolution to positive inputs. Its adjoint gives
the actual half-line adjoint, and Schur composition yields the Green operator.
Causality reduces its kernel to the overlap integral of two copies of the
positive density. The integral is finite off the potentially singular diagonal.
-/

open MeasureTheory Set Filter Topology Complex
open scoped FourierTransform InnerProductSpace
noncomputable section

namespace GaloisForLFunctions.CanonicalSystemOfTheWindowTower
open HTGeometry

/-- The causal density with its input restricted to the positive half-line. -/
def logarithmicHalfLineSchurKernel : SchurKernel (volume : Measure ℝ) := by
  classical
  let K := convolutionKernel (fun x : ℝ => (logarithmicCausalKernel x : ℂ))
    (Complex.continuous_ofReal.measurable.comp measurable_logarithmicCausalKernel)
    integrable_complex_logarithmicCausalKernel
  refine { toFun := fun x y => if 0 ≤ y then K.toFun x y else 0
           measurable := ?_
           bound := K.bound
           row := ?_
           col := ?_ }
  · exact K.measurable.piecewise (measurableSet_le measurable_const measurable_snd) measurable_const
  · intro x
    apply le_trans (lintegral_mono fun y => ?_) (K.row x)
    by_cases hy : 0 ≤ y
    · rw [if_pos hy]
    · rw [if_neg hy, enorm_zero]
      exact zero_le
  · intro y
    by_cases hy : 0 ≤ y
    · simpa only [if_pos hy] using K.col y
    · simp only [if_neg hy, enorm_zero, lintegral_zero]
      exact zero_le

theorem logarithmicHalfLineSchurKernel_toFun (x y : ℝ) :
    logarithmicHalfLineSchurKernel.toFun x y =
      if 0 ≤ y then (logarithmicCausalKernel (x - y) : ℂ) else 0 := rfl

/-- Both legs of the compressed Schur factor act inside the physical half-line. -/
theorem logarithmicHalfLineSchurKernel_op_mem (f : RealLineL2) :
    logarithmicHalfLineSchurKernel.op f ∈ RHTower.halfLineL2 := by
  rw [RHTower.mem_halfLineL2_iff]
  filter_upwards [logarithmicHalfLineSchurKernel.op_coeFn f] with x hx
  intro hxneg
  rw [hx]
  apply integral_eq_zero_of_ae
  filter_upwards with y
  change logarithmicHalfLineSchurKernel.toFun x y * (f : ℝ → ℂ) y = 0
  rw [logarithmicHalfLineSchurKernel_toFun]
  by_cases hy : 0 ≤ y
  · rw [if_pos hy, logarithmicCausalKernel_of_nonpos (by linarith only [hxneg, hy]),
      Complex.ofReal_zero, zero_mul]
  · rw [if_neg hy, zero_mul]

theorem logarithmicHalfLineSchurKernel_adjoint_mem (f : RealLineL2) :
    logarithmicHalfLineSchurKernel.adjoint.op f ∈ RHTower.halfLineL2 := by
  rw [RHTower.mem_halfLineL2_iff]
  filter_upwards [logarithmicHalfLineSchurKernel.adjoint.op_coeFn f] with x hx
  intro hxneg
  rw [hx]
  apply integral_eq_zero_of_ae
  filter_upwards with y
  change starRingEnd ℂ (logarithmicHalfLineSchurKernel.toFun y x) * (f : ℝ → ℂ) y = 0
  rw [logarithmicHalfLineSchurKernel_toFun, if_neg (not_le.mpr hxneg), map_zero, zero_mul]

/-- Restricting the Schur factor recovers the actual causal convolution. -/
theorem logarithmicHalfLineSchurKernel_op (f : LogarithmicHalfLineL2) :
    logarithmicHalfLineSchurKernel.op (f : RealLineL2) =
      ((logarithmicCausalOperator f : LogarithmicHalfLineL2) : RealLineL2) := by
  apply Lp.ext
  filter_upwards [logarithmicHalfLineSchurKernel.op_coeFn f, logarithmicConvolution_coeFn f] with x hx hw
  rw [logarithmicCausalOperator_coe, hw, hx]
  apply integral_congr_ae
  filter_upwards [(RHTower.mem_halfLineL2_iff (f : RealLineL2)).mp f.property] with y hy
  change logarithmicHalfLineSchurKernel.toFun x y * (f : ℝ → ℂ) y = _
  rw [logarithmicHalfLineSchurKernel_toFun]
  by_cases hy0 : 0 ≤ y
  · rw [if_pos hy0]
  · simp only [if_neg hy0, hy (lt_of_not_ge hy0), mul_zero, zero_mul]

/-- The restricted adjoint is the literal adjoint Schur kernel, without an abstract kernel premise. -/
theorem logarithmicHalfLineSchurKernel_adjoint_op (f : LogarithmicHalfLineL2) :
    logarithmicHalfLineSchurKernel.adjoint.op (f : RealLineL2) =
      ((logarithmicCausalOperator.adjoint f : LogarithmicHalfLineL2) : RealLineL2) := by
  let h : LogarithmicHalfLineL2 :=
    ⟨logarithmicHalfLineSchurKernel.adjoint.op f, logarithmicHalfLineSchurKernel_adjoint_mem f⟩
  have hh : h = logarithmicCausalOperator.adjoint f := by
    apply ext_inner_left ℂ
    intro g
    change inner ℂ (g : RealLineL2) (logarithmicHalfLineSchurKernel.adjoint.op (f : RealLineL2)) = _
    rw [← logarithmicHalfLineSchurKernel.adjoint_op]
    rw [logarithmicHalfLineSchurKernel.op.adjoint_inner_right, logarithmicHalfLineSchurKernel_op]
    exact (logarithmicCausalOperator.adjoint_inner_right g f).symm
  exact congrArg (fun v : LogarithmicHalfLineL2 => (v : RealLineL2)) hh

/-- Schur composition is the actual Green operator on the physical half-line. -/
theorem logarithmicHalfLineGreenOperator_eq_schur (f : LogarithmicHalfLineL2) :
    ((logarithmicHalfLineGreenOperator f : LogarithmicHalfLineL2) : RealLineL2) =
      (logarithmicHalfLineSchurKernel.comp logarithmicHalfLineSchurKernel.adjoint).op (f : RealLineL2) := by
  rw [SchurKernel.comp_op, ContinuousLinearMap.comp_apply, logarithmicHalfLineSchurKernel_adjoint_op,
    logarithmicHalfLineSchurKernel_op]
  rfl

/-- The real Green kernel, represented by its literal causal overlap integral. -/
def logarithmicHalfLineGreenKernel (x y : ℝ) : ℝ :=
  ∫ s in Icc (0 : ℝ) (min x y), logarithmicCausalKernel (x - s) * logarithmicCausalKernel (y - s)

/-- Causality truncates the full Schur composition to the overlap of the two positive rays. -/
theorem logarithmicHalfLineGreenKernel_eq_schur (x y : ℝ) :
    (logarithmicHalfLineSchurKernel.comp logarithmicHalfLineSchurKernel.adjoint).toFun x y =
      (logarithmicHalfLineGreenKernel x y : ℂ) := by
  let F : ℝ → ℝ := fun s => logarithmicCausalKernel (x - s) * logarithmicCausalKernel (y - s)
  have hprod (s : ℝ) : logarithmicHalfLineSchurKernel.toFun x s *
      logarithmicHalfLineSchurKernel.adjoint.toFun s y = ((Icc (0 : ℝ) (min x y)).indicator
        (fun s => (F s : ℂ))) s := by
    change logarithmicHalfLineSchurKernel.toFun x s *
      starRingEnd ℂ (logarithmicHalfLineSchurKernel.toFun y s) = _
    simp only [logarithmicHalfLineSchurKernel_toFun]
    by_cases hs0 : 0 ≤ s
    · simp only [if_pos hs0, Complex.conj_ofReal]
      by_cases hs : s ≤ min x y
      · rw [indicator_of_mem (s := Icc (0 : ℝ) (min x y)) ⟨hs0, hs⟩]
        exact (Complex.ofReal_mul _ _).symm
      · rw [indicator_of_notMem (s := Icc (0 : ℝ) (min x y)) (fun h => hs h.2)]
        have hxy : x < s ∨ y < s := by
          have hm : min x y < s := lt_of_not_ge hs
          exact min_lt_iff.mp hm
        rcases hxy with hx | hy
        · rw [logarithmicCausalKernel_of_nonpos (by linarith only [hx]), Complex.ofReal_zero, zero_mul]
        · rw [show logarithmicCausalKernel (y - s) = 0 from
            logarithmicCausalKernel_of_nonpos (by linarith only [hy]), Complex.ofReal_zero, mul_zero]
    · simp only [if_neg hs0, map_zero, zero_mul,
        indicator_of_notMem (s := Icc (0 : ℝ) (min x y)) (fun h => hs0 h.1)]
  rw [SchurKernel.comp_toFun]
  simp_rw [hprod]
  rw [integral_indicator measurableSet_Icc, integral_complex_ofReal]
  rfl

/-- Every actual L² Green solution has the explicit overlap-kernel representation. -/
theorem logarithmicHalfLineGreenOperator_coeFn (f : LogarithmicHalfLineL2) :
    (((logarithmicHalfLineGreenOperator f : LogarithmicHalfLineL2) : RealLineL2) : ℝ → ℂ) =ᵐ[volume]
      fun x => ∫ y : ℝ, (logarithmicHalfLineGreenKernel x y : ℂ) * (f : RealLineL2) y := by
  rw [logarithmicHalfLineGreenOperator_eq_schur]
  filter_upwards [(logarithmicHalfLineSchurKernel.comp logarithmicHalfLineSchurKernel.adjoint).op_coeFn
    (f : RealLineL2)] with x hx
  rw [hx]
  apply integral_congr_ae
  filter_upwards with y
  rw [logarithmicHalfLineGreenKernel_eq_schur]

private theorem integrable_logarithmicGreen_overlap_of_lt {x y : ℝ} (hxy : x < y) :
    IntegrableOn (fun s : ℝ => logarithmicCausalKernel (x - s) * logarithmicCausalKernel (y - s))
      (Icc (0 : ℝ) (min x y)) := by
  have ht : Integrable (fun s : ℝ => logarithmicCausalKernel (x - s)) :=
    logarithmicCausalKernel_mass_one.1.comp_sub_left x
  have hi := (ht.mul_const (logarithmicCausalKernel (y - x))).integrableOn (s := Icc (0 : ℝ) (min x y))
  have hm : Measurable (fun s : ℝ => logarithmicCausalKernel (x - s) * logarithmicCausalKernel (y - s)) :=
    (measurable_logarithmicCausalKernel.comp (measurable_const.sub measurable_id)).mul
      (measurable_logarithmicCausalKernel.comp (measurable_const.sub measurable_id))
  apply hi.mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  have hsx : s ≤ x := hs.2.trans (min_le_left _ _)
  have hpos : 0 < y - x := sub_pos.mpr hxy
  have hys : 0 < y - s := by linarith only [hxy, hsx]
  have hmono : logarithmicCausalKernel (y - s) ≤ logarithmicCausalKernel (y - x) :=
    antitoneOn_logarithmicCausalKernel hpos hys (by linarith only [hsx])
  rw [Real.norm_of_nonneg (mul_nonneg (logarithmicCausalKernel_nonneg _) (logarithmicCausalKernel_nonneg _))]
  exact mul_le_mul_of_nonneg_left hmono (logarithmicCausalKernel_nonneg _)

/-- The overlap integral is genuinely integrable away from its potentially singular diagonal. -/
theorem integrable_logarithmicHalfLineGreenKernel {x y : ℝ} (hxy : x ≠ y) :
    IntegrableOn (fun s : ℝ => logarithmicCausalKernel (x - s) * logarithmicCausalKernel (y - s))
      (Icc (0 : ℝ) (min x y)) := by
  rcases lt_or_gt_of_ne hxy with h | h
  · exact integrable_logarithmicGreen_overlap_of_lt h
  · simpa only [min_comm y x, mul_comm] using integrable_logarithmicGreen_overlap_of_lt h

theorem logarithmicHalfLineGreenKernel_nonneg (x y : ℝ) : 0 ≤ logarithmicHalfLineGreenKernel x y :=
  integral_nonneg fun _ => mul_nonneg (logarithmicCausalKernel_nonneg _) (logarithmicCausalKernel_nonneg _)

theorem logarithmicHalfLineGreenKernel_symm (x y : ℝ) :
    logarithmicHalfLineGreenKernel x y = logarithmicHalfLineGreenKernel y x := by
  unfold logarithmicHalfLineGreenKernel
  rw [min_comm]
  apply integral_congr_ae
  filter_upwards with s
  exact mul_comm _ _

#print axioms logarithmicHalfLineGreenOperator_coeFn
#print axioms integrable_logarithmicHalfLineGreenKernel

end GaloisForLFunctions.CanonicalSystemOfTheWindowTower
