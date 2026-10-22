import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSmoothOnsetLaplace
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-! Actual time derivatives of the fixed smooth causal source profile. -/
open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMJointSource
noncomputable section
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

/-- Fixed smooth onset carrying the original physical exponential rate. -/
def timeOnset (v : ℂ) (u : ℝ) : ℂ :=
  (Real.smoothTransition u:ℂ)*Complex.exp (v*(u:ℂ))

def timeOnsetFirst (v : ℂ) (u : ℝ) : ℂ :=
  (((deriv Real.smoothTransition u:ℝ):ℂ)+v*(Real.smoothTransition u:ℂ))*Complex.exp (v*(u:ℂ))

def timeOnsetSecond (v : ℂ) (u : ℝ) : ℂ :=
  (((deriv (deriv Real.smoothTransition) u:ℝ):ℂ)+2*v*((deriv Real.smoothTransition u:ℝ):ℂ)+
    v^(2 : ℕ)*(Real.smoothTransition u:ℂ))*Complex.exp (v*(u:ℂ))

/-- Third original-time jet of the fixed smooth causal onset.  This is the first
new source jet needed to upgrade the cap from a first trace to a strong second-order
Goursat candidate. -/
def timeOnsetThird (v : ℂ) (u : ℝ) : ℂ :=
  (((deriv (deriv (deriv Real.smoothTransition)) u:ℝ):ℂ)+
    3*v*((deriv (deriv Real.smoothTransition) u:ℝ):ℂ)+
    3*v^(2 : ℕ)*((deriv Real.smoothTransition u:ℝ):ℂ)+
    v^(3 : ℕ)*(Real.smoothTransition u:ℂ))*Complex.exp (v*(u:ℂ))

private theorem transition_hasDerivAt (u : ℝ) :
    HasDerivAt Real.smoothTransition (deriv Real.smoothTransition u) u :=
  ((Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num)).differentiableAt.hasDerivAt

private theorem transitionFirst_hasDerivAt (u : ℝ) :
    HasDerivAt (deriv Real.smoothTransition) (deriv (deriv Real.smoothTransition) u) u :=
  (Real.smoothTransition.contDiff (n := 2)).differentiable_deriv_two.differentiableAt.hasDerivAt

private theorem transitionSecond_hasDerivAt (u : ℝ) :
    HasDerivAt (deriv (deriv Real.smoothTransition))
      (deriv (deriv (deriv Real.smoothTransition)) u) u := by
  simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using
    ((Real.smoothTransition.contDiff (n := 3)).differentiable_iteratedDeriv 2
      (by norm_num)).differentiableAt.hasDerivAt

theorem timeOnset_hasDerivAt (v : ℂ) (u : ℝ) :
    HasDerivAt (timeOnset v) (timeOnsetFirst v u) u := by
  have hχ := (transition_hasDerivAt u).ofReal_comp
  have hE := ((hasDerivAt_id u).ofReal_comp.const_mul v).cexp
  apply (hχ.mul hE).congr_deriv
  simp only [timeOnsetFirst,Complex.ofReal_one,mul_one,id_eq]
  ring

theorem timeOnsetFirst_hasDerivAt (v : ℂ) (u : ℝ) :
    HasDerivAt (timeOnsetFirst v) (timeOnsetSecond v u) u := by
  have hχ := (transition_hasDerivAt u).ofReal_comp
  have hχ' := (transitionFirst_hasDerivAt u).ofReal_comp
  have hE := ((hasDerivAt_id u).ofReal_comp.const_mul v).cexp
  apply ((hχ'.add (hχ.const_mul v)).mul hE).congr_deriv
  simp only [timeOnsetSecond,Complex.ofReal_one,mul_one,id_eq,Pi.add_apply]
  ring

/-- The third source jet is the literal derivative of the second one. -/
theorem timeOnsetSecond_hasDerivAt (v : ℂ) (u : ℝ) :
    HasDerivAt (timeOnsetSecond v) (timeOnsetThird v u) u := by
  have hχ := (transition_hasDerivAt u).ofReal_comp
  have hχ' := (transitionFirst_hasDerivAt u).ofReal_comp
  have hχ'' := (transitionSecond_hasDerivAt u).ofReal_comp
  have hE := ((hasDerivAt_id u).ofReal_comp.const_mul v).cexp
  apply (((hχ''.add (hχ'.const_mul (2*v))).add (hχ.const_mul (v^(2 : ℕ)))).mul hE).congr_deriv
  simp only [timeOnsetThird,Complex.ofReal_one,mul_one,id_eq,Pi.add_apply]
  ring

theorem timeOnset_derivatives (v : ℂ) :
    deriv (timeOnset v) = timeOnsetFirst v ∧
      deriv (deriv (timeOnset v)) = timeOnsetSecond v := by
  have h := funext (fun u => (timeOnset_hasDerivAt v u).deriv)
  exact ⟨h,by rw [h]; exact funext (fun u => (timeOnsetFirst_hasDerivAt v u).deriv)⟩

/-- Third original-time derivative of the fixed causal onset. -/
theorem timeOnset_third_derivative (v : ℂ) :
    deriv (deriv (deriv (timeOnset v))) = timeOnsetThird v := by
  have hfirst : deriv (timeOnsetFirst v) = timeOnsetSecond v :=
    funext (fun u => (timeOnsetFirst_hasDerivAt v u).deriv)
  rw [(timeOnset_derivatives v).1,hfirst]
  exact funext (fun u => (timeOnsetSecond_hasDerivAt v u).deriv)

theorem timeOnset_zero_of_nonpos (v : ℂ) {u : ℝ} (hu : u ≤ 0) : timeOnset v u = 0 := by
  simp [timeOnset,Real.smoothTransition.zero_of_nonpos hu]

theorem timeOnsetFirst_zero_of_neg (v : ℂ) {u : ℝ} (hu : u < 0) : timeOnsetFirst v u = 0 := by
  rw [timeOnsetFirst,Real.smoothTransition.zero_of_nonpos hu.le,
    deriv_smoothTransition_eq_zero_of_notMem (show u ∉ Icc (0:ℝ) 1 from fun h => not_le_of_gt hu h.1)]
  simp

end
end RHTower.D4BMJointSource
