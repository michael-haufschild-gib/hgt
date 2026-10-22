import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMFundamentalMomentPolynomial
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMFundamentalMomentCounterterm

/-! Admission and source-faithful endpoint limits for the polynomial-coordinate moments. -/
namespace RHTower.D4BMJointSource
open Complex Set Filter Topology MeasureTheory D4BMLaplaceRadial GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false

def fundamentalJacobiCoreFirst (n : ℕ) (s : ℂ) (x : ℝ) : ℂ :=
  -(n:ℂ)*(1-(x:ℂ))^(n-1)*power (2*s) (2-x) -
    (1-(x:ℂ))^n*powerFirst (2*s) (2-x)

theorem fundamentalJacobiCore_hasDerivAt (n : ℕ) (s : ℂ) {x : ℝ} (hx : x < 2) :
    HasDerivAt (fundamentalJacobiCore n s) (fundamentalJacobiCoreFirst n s x) x := by
  have hr : HasDerivAt (fun y : ℝ => 1-(y:ℂ)) (-1) x := by
    simpa only [zero_sub,Complex.ofReal_one,id_eq,Pi.sub_apply] using! (hasDerivAt_const x (1:ℂ)).sub (hasDerivAt_id x).ofReal_comp
  have hp : HasDerivAt (fun y : ℝ => power (2*s) (2-y)) (-powerFirst (2*s) (2-x)) x := by
    simpa only [zero_sub,neg_one_smul,Function.comp_apply,Pi.sub_apply,id_eq] using!
      (power_derivatives (2*s) (by linarith : 0 < 2-x)).1.scomp x
        ((hasDerivAt_const x (2:ℝ)).sub (hasDerivAt_id x))
  exact ((hr.pow n).mul hp).congr_deriv (by dsimp only [fundamentalJacobiCoreFirst]; simp only [Pi.pow_apply]; ring)

theorem fundamentalJacobiCoreFirst_continuousAt (n : ℕ) (s : ℂ) {x : ℝ} (hx : x < 2) :
    ContinuousAt (fundamentalJacobiCoreFirst n s) x := by
  have hp := (power_derivatives (2*s) (by linarith : 0 < 2-x)).1.continuousAt.comp
    (continuousAt_const.sub continuousAt_id)
  have hdp := (power_derivatives (2*s) (by linarith : 0 < 2-x)).2.continuousAt.comp
    (continuousAt_const.sub continuousAt_id)
  have hr : ContinuousAt (fun y : ℝ => 1-(y:ℂ)) x :=
    continuousAt_const.sub Complex.continuous_ofReal.continuousAt
  exact (((hr.pow (n-1)).const_mul (-(n:ℂ))).mul hp).sub ((hr.pow n).mul hdp)

/-- A derived global endpoint bound for every polynomial moment, with no supplied estimate. -/
theorem fundamentalJacobiCore_first_bound (n : ℕ) (s : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Ioc (0:ℝ) 1,
      ‖fundamentalJacobiCore n s x-fundamentalJacobiCore n s 0‖ ≤ C*x := by
  have hc : ContinuousOn (fundamentalJacobiCoreFirst n s) (Icc (0:ℝ) 1) :=
    fun x hx => (fundamentalJacobiCoreFirst_continuousAt n s (by linarith [hx.2])).continuousWithinAt
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro x hx
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fundamentalJacobiCore n s) (f' := fundamentalJacobiCoreFirst n s) (s := Icc (0:ℝ) 1)
    (fun y hy => (fundamentalJacobiCore_hasDerivAt n s (by linarith [hy.2] : y < 2)).hasDerivWithinAt)
    (fun y hy => (hC y hy).trans (le_max_left C 0)) (convex_Icc (0:ℝ) 1)
    (by constructor <;> norm_num : (0:ℝ) ∈ Icc (0:ℝ) 1) ⟨hx.1.le,hx.2⟩
  simpa only [sub_zero,Real.norm_eq_abs,abs_of_nonneg hx.1.le] using h

theorem fundamentalJacobiCore_zero (n : ℕ) (s : ℂ) :
    fundamentalJacobiCore n s 0=(2:ℂ)^(2*s) := by
  simp only [fundamentalJacobiCore,Complex.ofReal_zero,sub_zero,one_pow,one_mul,Complex.ofReal_ofNat]

theorem fundamentalJacobiMoment_cutoff (n : ℕ) (w s : ℂ) (hw : -2 < w.re) (hw1 : w+1 ≠ 0) :
    Tendsto (fun e : ℝ => (∫ x in e..1, (x:ℂ)^w*fundamentalJacobiCore n s x)+
      (2:ℂ)^(2*s)*(e:ℂ)^(w+1)/(w+1))
      (𝓝[>] (0:ℝ)) (𝓝 (fundamentalJacobiMoment n w s)) := by
  obtain ⟨C,_,hC⟩ := fundamentalJacobiCore_first_bound n s
  have hm : Measurable (fundamentalJacobiCore n s) := by unfold fundamentalJacobiCore; fun_prop
  have hi := firstEndpointMellinRemainder_integrable (F := fun _ => fundamentalJacobiCore n s)
    (by norm_num : (0:ℝ)≤1) hw hm hC
  have hi' := (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ)≤1)).mpr hi
  simpa only [fundamentalJacobiCore_zero,fundamentalJacobiMoment] using
    firstEndpointMellin_cutoff_of_integrable (fundamentalJacobiCore n s) w hw1 hi'

end
end RHTower.D4BMJointSource
