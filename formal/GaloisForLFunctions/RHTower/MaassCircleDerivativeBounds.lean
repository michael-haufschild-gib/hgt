import GaloisForLFunctions.RHTower.MaassCircleTransfer
import GaloisForLFunctions.RHTower.MaassCircleKernel
import GaloisForLFunctions.HTGeometry.CompactSmoothParameterIntegral
import GaloisForLFunctions.RHTower.MaassCongruenceL2

/-!
# All Euler derivatives of the actual Maass source

The actual base-point derivatives move onto a compact annular kernel. Iteration
represents every finite Euler word by another kernel acting on the original
source. Its proved global cusp bound then controls every derivative.
-/

open UpperHalfPlane MeasureTheory Set Filter Topology
open scoped ContDiff
namespace GaloisForLFunctions.RHTower.MaassCircle
open MaassSmooth HTGeometry.SmoothCylinder
noncomputable section

def baseFlow (vertical : Bool) (t : ℝ) (z : ℍ) : ℍ :=
  if vertical then verticalFlow t z else horizontalFlow t z

def euler (vertical : Bool) : Module.End ℂ FunctionSpace :=
  if vertical then MaassSmooth.Y else MaassSmooth.height * directional 1

def radialKernel {a b : ℝ} (vertical : Bool) (k : Kernel a b) : Kernel a b :=
  if vertical then k.cosMul else k.sinMul

def angularKernel {a b : ℝ} (vertical : Bool) (ha : 0 < a) (k : Kernel a b) : Kernel a b :=
  if vertical then (k.cothMul ha).sinMul.neg else (k.cothMul ha).cosMul.add k.neg

def transposeKernel {a b : ℝ} (vertical : Bool) (ha : 0 < a) (k : Kernel a b) : Kernel a b :=
  (((radialKernel vertical k).directional (1,0)).add
    ((angularKernel vertical ha k).directional (0,1))).neg

theorem base_source_deriv (vertical : Bool) (f : FunctionSpace) (z : ℍ) :
    deriv (fun t => f (baseFlow vertical t z)) 0 = euler vertical f z := by
  cases vertical
  · exact horizontal_source_deriv f z
  · exact vertical_source_deriv f z

theorem flow_source_smooth (vertical : Bool) (f : FunctionSpace) (z : ℍ) :
    ContDiff ℝ ∞ (fun q : ℝ × (ℝ × ℝ) =>
      f (circlePoint q.2.1 q.2.2 (baseFlow vertical q.1 z))) := by
  apply circle_source_smooth_family f (fun q : ℝ × (ℝ × ℝ) => baseFlow vertical q.1 z)
    (fun q => q.2.1) (fun q => q.2.2) ?_
    (contDiff_fst.comp contDiff_snd) (contDiff_snd.comp contDiff_snd)
  cases vertical
  · have he : (fun q : ℝ × (ℝ × ℝ) => (baseFlow false q.1 z : ℂ)) =
        fun q => (z : ℂ)+(q.1 : ℂ)*(z.im : ℂ) := by
      funext q
      change (horizontalFlow q.1 z : ℂ) = _
      apply Complex.ext <;> simp [horizontalFlow]
    rw [he]
    exact contDiff_const.add ((Complex.ofRealCLM.contDiff.comp contDiff_fst).mul contDiff_const)
  · have he : (fun q : ℝ × (ℝ × ℝ) => (baseFlow true q.1 z : ℂ)) =
        fun q => (z.re : ℂ)+(Real.exp q.1*z.im : ℝ)*Complex.I := by
      funext q
      change (verticalFlow q.1 z : ℂ) = _
      apply Complex.ext <;>
        simp only [verticalFlow, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
          mul_zero, add_zero, sub_zero, zero_add, mul_one]
    rw [he]
    exact contDiff_const.add ((Complex.ofRealCLM.contDiff.comp
      ((Real.contDiff_exp.comp contDiff_fst).mul contDiff_const)).mul contDiff_const)

theorem weighted_flow_deriv {a b : ℝ} (vertical : Bool) (ha : 0 < a) (k : Kernel a b)
    (f : FunctionSpace) (z : ℍ) (p : ℝ × ℝ) (hp : 0 < p.1) :
    deriv (fun t => k p * f (circlePoint p.1 p.2 (baseFlow vertical t z))) 0 =
      radialKernel vertical k p * fderiv ℝ (fun q : ℝ × ℝ => f (circlePoint q.1 q.2 z)) p (1,0) +
      angularKernel vertical ha k p * fderiv ℝ (fun q : ℝ × ℝ => f (circlePoint q.1 q.2 z)) p (0,1) := by
  have hs := flow_source_smooth vertical f z
  have hF := circle_source_smooth f z
  have hd := ((HTGeometry.CompactSmoothParameterIntegral.slice_hasDerivAt hs 0 p).differentiableAt.hasDerivAt.const_mul (k p)).deriv
  change deriv (fun t => k p * f (circlePoint p.1 p.2 (baseFlow vertical t z))) 0 =
    k p * deriv (fun t => f (circlePoint p.1 p.2 (baseFlow vertical t z))) 0 at hd
  rw [hd]
  cases vertical
  · change k p * deriv (fun t => f (circlePoint p.1 p.2 (horizontalFlow t z))) 0 = _
    rw [horizontal_circle_transfer f z hp,
      (HTGeometry.SmoothAngularAverage.slice_hasDerivAt hF p.1 p.2).deriv,
      (angular_hasDerivAt hF p.1 p.2).deriv]
    simp [radialKernel, angularKernel, Kernel.sinMul, Kernel.cosMul, Kernel.mul,
      Kernel.cothMul, Kernel.add, Kernel.neg, HTGeometry.SmoothAngularAverage.radialPartial,
      Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_one]
    ring
  · change k p * deriv (fun t => f (circlePoint p.1 p.2 (verticalFlow t z))) 0 = _
    rw [vertical_circle_transfer f z hp,
      (HTGeometry.SmoothAngularAverage.slice_hasDerivAt hF p.1 p.2).deriv,
      (angular_hasDerivAt hF p.1 p.2).deriv]
    simp [radialKernel, angularKernel, Kernel.sinMul, Kernel.cosMul, Kernel.mul,
      Kernel.cothMul, Kernel.neg, HTGeometry.SmoothAngularAverage.radialPartial,
      Complex.ofReal_mul]
    ring

/-- An actual base-point derivative moves entirely onto the compact circle kernel. -/
theorem kernelAverage_hasDerivAt {a b : ℝ} (vertical : Bool) (ha : 0 < a) (hab : a ≤ b)
    (k : Kernel a b) (f : FunctionSpace) (z : ℍ) :
    HasDerivAt (fun t => kernelAverage k f (baseFlow vertical t z))
      (kernelAverage (transposeKernel vertical ha k) f z) 0 := by
  have hs := flow_source_smooth vertical f z
  have h := HTGeometry.CompactSmoothParameterIntegral.integral_hasDerivAt
    ((k.smooth.comp contDiff_snd).mul hs) (K := box a b) (isCompact_Icc.prod isCompact_Icc) 0
  change HasDerivAt (fun t => kernelAverage k f (baseFlow vertical t z))
    (boxIntegral a b (fun p => deriv (fun t => k p * f (circlePoint p.1 p.2 (baseFlow vertical t z))) 0)) 0 at h
  apply h.congr_deriv
  calc
    _ = boxIntegral a b (fun p =>
        radialKernel vertical k p * fderiv ℝ (fun q : ℝ × ℝ => f (circlePoint q.1 q.2 z)) p (1,0) +
        angularKernel vertical ha k p * fderiv ℝ (fun q : ℝ × ℝ => f (circlePoint q.1 q.2 z)) p (0,1)) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (isClosed_Icc.measurableSet.prod isClosed_Icc.measurableSet)] with p hp
      exact weighted_flow_deriv vertical ha k f z p (ha.trans_le hp.1.1)
    _ = _ := divergence_identity hab (radialKernel vertical k) (angularKernel vertical ha k)
      (circle_source_smooth f z) (by intro r theta; rw [circlePoint_periodic])

def eulerWord : List Bool → Module.End ℂ FunctionSpace
  | [] => 1
  | d :: w => euler d * eulerWord w

def kernelWord {a b : ℝ} (ha : 0 < a) : List Bool → Kernel a b → Kernel a b
  | [], k => k
  | d :: w, k => transposeKernel d ha (kernelWord ha w k)

theorem word_kernel_representation {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (k : Kernel a b) (f : FunctionSpace) (hrep : ∀ z, kernelAverage k f z = f z)
    (w : List Bool) (z : ℍ) :
    eulerWord w f z = kernelAverage (kernelWord ha w k) f z := by
  induction w generalizing z with
  | nil => exact (hrep z).symm
  | cons d w ih =>
      change euler d (eulerWord w f) z = kernelAverage (transposeKernel d ha (kernelWord ha w k)) f z
      have he : (fun t => eulerWord w f (baseFlow d t z)) =
          fun t => kernelAverage (kernelWord ha w k) f (baseFlow d t z) :=
        funext fun t => ih (baseFlow d t z)
      rw [← base_source_deriv d (eulerWord w f) z, he,
        (kernelAverage_hasDerivAt d ha hab (kernelWord ha w k) f z).deriv]

/-- Every finite Euler word in the actual congruence Maass source is globally bounded. -/
theorem all_euler_words_bounded (N : ℕ) {lam : ℝ} (hlam : 0 < lam)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N+1))) lam)
    (w : List Bool) : ∃ C : ℝ, ∀ z : ℍ, ‖eulerWord w (ofMaass f) z‖ ≤ C := by
  obtain ⟨a,b,ha,hab,k,hrep⟩ := exists_reproducing_kernel hlam f
  obtain ⟨C,hC⟩ := MaassCongruenceL2.source_bounded N f
  refine ⟨(∫ p in box a b, ‖kernelWord ha w k p‖)*C, ?_⟩
  intro z
  rw [word_kernel_representation ha hab.le k (ofMaass f) hrep w z]
  exact norm_boxIntegral_mul_le (kernelWord ha w k)
    (fun p => f.1.1 (circlePoint p.1 p.2 z)) (fun p _ => hC (circlePoint p.1 p.2 z))

end
end GaloisForLFunctions.RHTower.MaassCircle
