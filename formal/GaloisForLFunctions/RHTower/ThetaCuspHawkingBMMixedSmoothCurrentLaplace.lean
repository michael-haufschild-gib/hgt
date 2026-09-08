import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMMixedCurrentLaplace
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMMixedCurrentCutoff
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSmoothOnsetLaplace

/-! Actual smooth-onset current transform and its entire regularization at the
original physical source rate. This is source continuation, not response extinction. -/

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMModularCore
open D4BMHorizon D4BMIngoingCoordinates
set_option autoImplicit false
noncomputable section

/-- The actual switched current evaluated in the ingoing chart, weighted by
the Laplace frequency conjugate to the original static time. -/
def smoothCurrentKernel (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (r : {r : ℝ // 1 < r}) (z : Point) (k : Fin 2) (w : ℂ) (u : ℝ) : ℂ :=
  Complex.exp (-w*((u-tortoise r.val:ℝ):ℂ))*
    switchedOrbitCurrent q branch a z k ![u-tortoise r.val,r.val,z 0,z 1]

/-- The genuine half-line integral of that original switched current. -/
def smoothCurrentLaplace (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (r : {r : ℝ // 1 < r}) (z : Point) (k : Fin 2) (w : ℂ) : ℂ :=
  ∫ u in Ioi (0:ℝ), smoothCurrentKernel q branch a r z k w u

private theorem smooth_kernel_factor (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (r : {r : ℝ // 1 < r}) (z : Point) (k : Fin 2) (w : ℂ) (u : ℝ) :
    smoothCurrentKernel q branch a r z k w u = regularizedCurrent q branch a r z k w*
      ((Real.smoothTransition u:ℂ)*Complex.exp ((currentRate q branch-w)*(u:ℂ))) := by
  have hc : currentCutoff ![u-tortoise r.val,r.val,z 0,z 1] = (Real.smoothTransition u:ℂ) := by
    simp [currentCutoff,ingoingTime]
  unfold smoothCurrentKernel switchedOrbitCurrent
  rw [hc]
  change Complex.exp (-w*((u-tortoise r.val:ℝ):ℂ))*
    ((Real.smoothTransition u:ℂ)*staticCurrent q branch a r z k (u-tortoise r.val)) = _
  rw [staticCurrent_ingoing,sub_add_cancel]
  have he : Complex.exp (-w*((u-tortoise r.val:ℝ):ℂ))*Complex.exp (currentRate q branch*(u:ℂ)) =
      Complex.exp (w*(tortoise r.val:ℂ))*Complex.exp ((currentRate q branch-w)*(u:ℂ)) := by
    rw [← Complex.exp_add,← Complex.exp_add]
    congr 1
    push_cast
    ring
  calc
    _ = (Complex.exp (-w*((u-tortoise r.val:ℝ):ℂ))*Complex.exp (currentRate q branch*(u:ℂ)))*
        ((Real.smoothTransition u:ℂ)*ingoingCurrentAmplitude q branch a r z k) := by ring
    _ = _ := by rw [he]; unfold regularizedCurrent; ring

private theorem smooth_chamber (q : XiZeroCopy) (branch : Bool) {w : ℂ} (hw : 0 < w.re) :
    (currentRate q branch).re < w.re := lt_trans (currentRate_re_lt q branch) (by linarith)

/-- Absolute convergence for the actual smoothly switched original current,
with its full angular source fixed, throughout the right half-plane. -/
theorem smoothCurrentLaplace_integrable (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (r : {r : ℝ // 1 < r}) (z : Point) (k : Fin 2) {w : ℂ} (hw : 0 < w.re) :
    IntegrableOn (smoothCurrentKernel q branch a r z k w) (Ioi (0:ℝ)) := by
  change IntegrableOn (fun u => smoothCurrentKernel q branch a r z k w u) _
  simp_rw [smooth_kernel_factor]
  exact (onsetTransform_integrable _ _ (smooth_chamber q branch hw)).const_mul _

/-- The actual smooth-onset source transform is its original pole plus the
proved entire transition correction, with the radial time-change factor retained. -/
theorem smoothCurrentLaplace_eq (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (r : {r : ℝ // 1 < r}) (z : Point) (k : Fin 2) {w : ℂ} (hw : 0 < w.re) :
    smoothCurrentLaplace q branch a r z k w = regularizedCurrent q branch a r z k w*
      (1/(w-currentRate q branch)+onsetCorrection (currentRate q branch) w) := by
  unfold smoothCurrentLaplace
  simp_rw [smooth_kernel_factor]
  rw [integral_const_mul]
  rw [show (∫ u in Ioi (0:ℝ), (Real.smoothTransition u:ℂ)*
      Complex.exp ((currentRate q branch-w)*(u:ℂ))) = onsetTransform (currentRate q branch) w from rfl,
    onsetTransform_eq _ _ (smooth_chamber q branch hw)]

/-- Entire numerator continuing the actual smooth-onset current transform. -/
def regularizedSmoothCurrent (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (r : {r : ℝ // 1 < r}) (z : Point) (k : Fin 2) (w : ℂ) : ℂ :=
  regularizedCurrent q branch a r z k w*
    (1+(w-currentRate q branch)*onsetCorrection (currentRate q branch) w)

/-- Entire continuation of the regularized actual source, with no source-retuning premise. -/
theorem regularizedSmoothCurrent_entire (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (r : {r : ℝ // 1 < r}) (z : Point) (k : Fin 2) :
    Differentiable ℂ (regularizedSmoothCurrent q branch a r z k) := by
  have hOne : Differentiable ℂ (fun _ : ℂ => (1:ℂ)) := by fun_prop
  exact (regularizedCurrent_entire q branch a r z k).mul
    (hOne.add ((differentiable_id.sub_const _).mul (onsetCorrection_entire _)))

/-- The integral in its genuine convergence chamber equals the explicit
continued quotient. No continuation of a physical inverse is inferred. -/
theorem smoothCurrentLaplace_continuation (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (r : {r : ℝ // 1 < r}) (z : Point) (k : Fin 2) {w : ℂ} (hw : 0 < w.re) :
    smoothCurrentLaplace q branch a r z k w = regularizedSmoothCurrent q branch a r z k w /
      (w-currentRate q branch) := by
  have hn : w-currentRate q branch ≠ 0 := by
    intro h
    have he := congrArg Complex.re (sub_eq_zero.mp h)
    have hv := smooth_chamber q branch hw
    rw [he] at hv
    exact lt_irrefl _ hv
  rw [smoothCurrentLaplace_eq q branch a r z k hw,regularizedSmoothCurrent]
  field_simp [hn]

/-- The source-pole coefficient survives the fixed smooth onset exactly:
the regularized value is the original current at static time zero. -/
theorem regularizedSmoothCurrent_physical (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (r : {r : ℝ // 1 < r}) (z : Point) (k : Fin 2) :
    regularizedSmoothCurrent q branch a r z k (currentRate q branch) = staticCurrent q branch a r z k 0 := by
  simp only [regularizedSmoothCurrent,sub_self,zero_mul,add_zero,mul_one]
  exact regularizedCurrent_physical q branch a r z k

end
end RHTower.D4BMModularCore
