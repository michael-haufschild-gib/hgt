import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSmoothOnsetLaplace

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
    v^2*(Real.smoothTransition u:ℂ))*Complex.exp (v*(u:ℂ))

private theorem transition_hasDerivAt (u : ℝ) :
    HasDerivAt Real.smoothTransition (deriv Real.smoothTransition u) u :=
  ((Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num)).differentiableAt.hasDerivAt

private theorem transitionFirst_hasDerivAt (u : ℝ) :
    HasDerivAt (deriv Real.smoothTransition) (deriv (deriv Real.smoothTransition) u) u :=
  (Real.smoothTransition.contDiff (n := 2)).differentiable_deriv_two.differentiableAt.hasDerivAt

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

theorem timeOnset_derivatives (v : ℂ) :
    deriv (timeOnset v) = timeOnsetFirst v ∧
      deriv (deriv (timeOnset v)) = timeOnsetSecond v := by
  have h := funext (fun u => (timeOnset_hasDerivAt v u).deriv)
  exact ⟨h,by rw [h]; exact funext (fun u => (timeOnsetFirst_hasDerivAt v u).deriv)⟩

theorem timeOnset_zero_of_nonpos (v : ℂ) {u : ℝ} (hu : u ≤ 0) : timeOnset v u = 0 := by
  simp [timeOnset,Real.smoothTransition.zero_of_nonpos hu]

theorem timeOnsetFirst_zero_of_neg (v : ℂ) {u : ℝ} (hu : u < 0) : timeOnsetFirst v u = 0 := by
  rw [timeOnsetFirst,Real.smoothTransition.zero_of_nonpos hu.le,
    deriv_smoothTransition_eq_zero_of_notMem (show u ∉ Icc (0:ℝ) 1 from fun h => not_le_of_gt hu h.1)]
  simp

end
end RHTower.D4BMJointSource
