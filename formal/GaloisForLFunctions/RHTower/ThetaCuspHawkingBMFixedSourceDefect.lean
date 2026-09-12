import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFixedSourcePolynomial
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! The actual physical source as a fixed boundary term and one ordinary convergent integral. -/
namespace RHTower.D4BMJointSource
open Complex Set Filter Topology MeasureTheory D4BMLaplaceRadial GaloisForLFunctions.HTGeometry
open scoped Polynomial
noncomputable section
set_option autoImplicit false

def nonstationarySourceDefect (w : ℂ) : ℂ :=
  ∫ x in Ioc (0:ℝ) 1, (x:ℂ)^w*
    nonstationaryCore (nonstationaryWeightStep nonstationarySourceNumerator 8) 10 w x

theorem nonstationarySourceDefect_integrable (w : ℂ) (hw : -2 < w.re) :
    IntegrableOn (fun x : ℝ => (x:ℂ)^w*
      nonstationaryCore (nonstationaryWeightStep nonstationarySourceNumerator 8) 10 w x) (Ioc (0:ℝ) 1) := by
  have h := nonstationaryMoment_remainder_integrable
    (nonstationaryWeightStep nonstationarySourceNumerator 8) 10 w hw
  simpa only [nonstationaryCore,nonstationaryWeight,Complex.ofReal_zero,
    nonstationaryWeightStep_zero,zero_div,mul_zero,sub_zero] using h

theorem nonstationarySourceDefect_eq_moment (w : ℂ) :
    nonstationarySourceDefect w=nonstationaryMoment
      (nonstationaryWeightStep nonstationarySourceNumerator 8) 10 w := by
  have hz : nonstationaryCore (nonstationaryWeightStep nonstationarySourceNumerator 8) 10 w 0=0 := by
    simp only [nonstationaryCore,nonstationaryWeight,Complex.ofReal_zero,
      nonstationaryWeightStep_zero,zero_div,mul_zero]
  simp only [nonstationarySourceDefect,nonstationaryMoment,firstEndpointMellin,hz,
    zero_mul,zero_div,zero_add,firstEndpointMellinRemainder,sub_zero]

theorem nonstationarySourceNumerator_normalized (w : ℂ) (hw : -2 < w.re) (hw1 : w+1 ≠ 0) :
    (w+1)*nonstationaryMoment nonstationarySourceNumerator 8 w=
      (86/625:ℂ)-nonstationarySourceDefect w := by
  have h := nonstationaryMoment_recurrence nonstationarySourceNumerator 8 w hw hw1
  rw [nonstationarySourceWeight_one,← nonstationarySourceDefect_eq_moment] at h
  linear_combination h

/-- The original subtracted pole has a finite normalized value, fixed by the same endpoint weight. -/
theorem nonstationarySourceDefect_neg_one : nonstationarySourceDefect (-1)=(86/625:ℂ)+3/32 := by
  have hp : nonstationaryPrimitive nonstationarySourceNumerator 8 (-1)=
      nonstationaryPrimitiveCore nonstationarySourceNumerator 8 (-1) := by
    funext x
    norm_num [nonstationaryPrimitive,power]
  have hc : ContinuousOn (nonstationaryPrimitive nonstationarySourceNumerator 8 (-1)) (Icc (0:ℝ) 1) := by
    rw [hp]
    intro x hx
    exact (nonstationaryPrimitiveCore_hasDerivAt _ _ _
      (by constructor <;> linarith [hx.1,hx.2])).continuousAt.continuousWithinAt
  have hi := nonstationarySourceDefect_integrable (-1) (by norm_num)
  have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num : (0:ℝ)≤1) hc
    (fun x hx => by simpa using nonstationaryPrimitive_hasDerivAt nonstationarySourceNumerator 8 (-1) ⟨hx.1,hx.2.le⟩)
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ)≤1)).mpr hi)
  have h0 : nonstationaryPrimitive nonstationarySourceNumerator 8 (-1) 0=-(3/32:ℂ) := by
    norm_num [nonstationaryPrimitive,nonstationaryPrimitiveCore,nonstationaryMultiplier,
      nonstationaryWeight,nonstationarySourceNumerator_zero,power]
  rw [nonstationarySourceDefect,← intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),
    hf,nonstationaryPrimitive_one,nonstationarySourceWeight_one,h0]
  ring

/-- Continuity on the entire closed physical strip follows from one common integrable majorant. -/
theorem nonstationarySourceDefect_continuousOn :
    ContinuousOn nonstationarySourceDefect {w : ℂ | w.re ∈ Icc (-(3/2):ℝ) (-1)} := by
  obtain ⟨C,hC0,hC⟩ := nonstationaryWeight_step_bound nonstationarySourceNumerator 8
  let bound : ℝ → ℝ := fun x => 64*C*x^(-(1/2):ℝ)
  have hbi : IntegrableOn bound (Ioc (0:ℝ) 1) := by
    exact (((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ)≤1)).mp
      (intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1:ℝ)< -(1/2)))).const_mul (64*C))
  apply continuousOn_of_dominated (bound := bound)
  · intro w hw
    exact (nonstationarySourceDefect_integrable w (by linarith [hw.1])).aestronglyMeasurable
  · intro w hw
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    calc
      _ = ‖(x:ℂ)^w*power (-4*w) (2-x)‖*
          ‖nonstationaryWeight (nonstationaryWeightStep nonstationarySourceNumerator 8) 10 x‖ := by
            rw [nonstationaryCore,← mul_assoc,norm_mul]
      _ ≤ ‖(x:ℂ)^w*power (-4*w) (2-x)‖*(C*x) :=
        mul_le_mul_of_nonneg_left (hC x hx) (norm_nonneg _)
      _ = C*(‖(x:ℂ)^w*power (-4*w) (2-x)‖*x) := by ring
      _ ≤ C*(64*x^(-(1/2):ℝ)) := mul_le_mul_of_nonneg_left (nonstationaryKernel_bound w hw hx) hC0
      _ = bound x := by dsimp only [bound]; ring
  · exact hbi
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have ha : 0 < 2-x := by linarith [hx.2]
    letI : NeZero (x:ℂ) := ⟨Complex.ofReal_ne_zero.mpr hx.1.ne'⟩
    letI : NeZero ((2-x:ℝ):ℂ) := ⟨Complex.ofReal_ne_zero.mpr ha.ne'⟩
    have hxC := continuous_const_cpow (x:ℂ)
    have hyC : Continuous (fun w : ℂ => ((2-x:ℝ):ℂ)^(-4*w)) :=
      (continuous_const_cpow ((2-x:ℝ):ℂ)).comp (continuous_const.mul continuous_id)
    exact (hxC.mul (hyC.mul continuous_const)).continuousOn

end
end RHTower.D4BMJointSource
