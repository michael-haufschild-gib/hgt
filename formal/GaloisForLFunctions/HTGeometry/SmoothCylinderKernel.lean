import GaloisForLFunctions.HTGeometry.SmoothAngularAverage
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Calculus.FDeriv.Const

/-!
# Smooth periodic kernels on a radial annulus

Radial support and angular periodicity are preserved by directional derivatives
and the formal transpose kernels for hyperbolic circle Euler fields. Division
by a radial function is smooth when that function is nonzero on the support;
vanishing in a neighborhood handles all zeros outside the support.
-/

open Set Filter Topology
open scoped ContDiff
namespace GaloisForLFunctions.HTGeometry.SmoothCylinder
noncomputable section

structure Kernel (a b : ℝ) where
  toFun : ℝ × ℝ → ℂ
  smooth : ContDiff ℝ ∞ toFun
  periodic : ∀ r theta, toFun (r,theta+2*Real.pi) = toFun (r,theta)
  vanish : ∀ p, p.1 ∉ Icc a b → toFun p = 0

instance {a b : ℝ} : CoeFun (Kernel a b) (fun _ => ℝ × ℝ → ℂ) := ⟨Kernel.toFun⟩

variable {a b : ℝ}

theorem Kernel.tsupport_subset (k : Kernel a b) :
    tsupport (k : ℝ × ℝ → ℂ) ⊆ {p | p.1 ∈ Icc a b} := by
  apply closure_minimal ?_ (isClosed_Icc.preimage continuous_fst)
  intro p hp
  by_contra h
  exact hp (k.vanish p h)

def Kernel.add (k l : Kernel a b) : Kernel a b where
  toFun p := k p + l p
  smooth := k.smooth.add l.smooth
  periodic r theta := by rw [k.periodic, l.periodic]
  vanish p hp := by rw [k.vanish p hp, l.vanish p hp, add_zero]

def Kernel.neg (k : Kernel a b) : Kernel a b where
  toFun p := -k p
  smooth := k.smooth.neg
  periodic r theta := by rw [k.periodic]
  vanish p hp := by rw [k.vanish p hp, neg_zero]

def Kernel.mul (k : Kernel a b) (A : ℝ × ℝ → ℂ) (hA : ContDiff ℝ ∞ A)
    (hper : ∀ r theta, A (r,theta+2*Real.pi) = A (r,theta)) : Kernel a b where
  toFun p := A p * k p
  smooth := hA.mul k.smooth
  periodic r theta := by rw [hper, k.periodic]
  vanish p hp := by rw [k.vanish p hp, mul_zero]

/-- Division preserves a kernel when the divisor is nonzero throughout its radial support. -/
def Kernel.divRadial (k : Kernel a b) (d : ℝ → ℂ) (hd : ContDiff ℝ ∞ d)
    (hn : ∀ r ∈ Icc a b, d r ≠ 0) : Kernel a b where
  toFun p := k p / d p.1
  smooth := by
    apply contDiff_iff_contDiffAt.mpr
    intro p
    by_cases hp : p.1 ∈ Icc a b
    · simpa only [div_eq_mul_inv, Function.comp_def] using!
        k.smooth.contDiffAt.mul ((hd.contDiffAt.comp p contDiffAt_fst).fun_inv (hn p.1 hp))
    · have hneigh : {q : ℝ × ℝ | q.1 ∉ Icc a b} ∈ 𝓝 p :=
        (isClosed_Icc.preimage continuous_fst).isOpen_compl.mem_nhds hp
      apply contDiffAt_const.congr_of_eventuallyEq
      filter_upwards [hneigh] with q hq
      rw [k.vanish q hq, zero_div]
  periodic r theta := by rw [k.periodic]
  vanish p hp := by rw [k.vanish p hp, zero_div]

def Kernel.directional (v : ℝ × ℝ) (k : Kernel a b) : Kernel a b where
  toFun p := fderiv ℝ (k : ℝ × ℝ → ℂ) p v
  smooth := (k.smooth.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  periodic r theta := by
    have he : (k : ℝ × ℝ → ℂ) ∘ (fun p => p + (0,2*Real.pi)) = k := by
      funext p
      change k (p.1+0,p.2+2*Real.pi) = k (p.1,p.2)
      simpa only [add_zero] using k.periodic p.1 p.2
    have h := (k.smooth.differentiable (by simp) ((r,theta)+(0,2*Real.pi))).hasFDerivAt.comp
      (r,theta) ((hasFDerivAt_id (r,theta)).add_const (0,2*Real.pi))
    simp only [id_eq] at h
    rw [he] at h
    have hv := congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℂ => L v) h.fderiv.symm
    change fderiv ℝ (k : ℝ × ℝ → ℂ) (r+0,theta+2*Real.pi) v =
      fderiv ℝ (k : ℝ × ℝ → ℂ) (r,theta) v at hv
    simpa only [add_zero] using hv
  vanish p hp := by
    have hnot : p ∉ tsupport (k : ℝ × ℝ → ℂ) := fun h => hp (k.tsupport_subset h)
    rw [fderiv_of_notMem_tsupport ℝ hnot]
    rfl

def Kernel.sinMul (k : Kernel a b) : Kernel a b :=
  k.mul (fun p => (Real.sin p.2 : ℂ)) (Complex.ofRealCLM.contDiff.comp (Real.contDiff_sin.comp contDiff_snd))
    (by intro r theta; simp only [Real.sin_add_two_pi])

def Kernel.cosMul (k : Kernel a b) : Kernel a b :=
  k.mul (fun p => (Real.cos p.2 : ℂ)) (Complex.ofRealCLM.contDiff.comp (Real.contDiff_cos.comp contDiff_snd))
    (by intro r theta; simp only [Real.cos_add_two_pi])

theorem Kernel.coth_mul_smooth (ha : 0 < a) (k : Kernel a b) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => (Real.cosh p.1 / Real.sinh p.1 : ℝ) * k p) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  by_cases hz : p.1 = 0
  · have hn : {q : ℝ × ℝ | q.1 < a} ∈ 𝓝 p :=
      (isOpen_lt continuous_fst continuous_const).mem_nhds (by change p.1 < a; rw [hz]; exact ha)
    apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [hn] with q hq
    rw [k.vanish q (fun h => (not_le_of_gt hq) h.1), mul_zero]
  · have hs : Real.sinh p.1 ≠ 0 := Real.sinh_ne_zero.mpr hz
    have hc : ContDiff ℝ ∞ (fun q : ℝ × ℝ => Real.cosh q.1) := by fun_prop
    have hh : ContDiff ℝ ∞ (fun q : ℝ × ℝ => Real.sinh q.1) := by fun_prop
    exact (Complex.ofRealCLM.contDiff.contDiffAt.comp p (hc.contDiffAt.div hh.contDiffAt hs)).mul
      k.smooth.contDiffAt

def Kernel.cothMul (ha : 0 < a) (k : Kernel a b) : Kernel a b where
  toFun p := (Real.cosh p.1 / Real.sinh p.1 : ℝ) * k p
  smooth := k.coth_mul_smooth ha
  periodic r theta := by rw [k.periodic]
  vanish p hp := by rw [k.vanish p hp, mul_zero]

def Kernel.horizontalTranspose (ha : 0 < a) (k : Kernel a b) : Kernel a b :=
  ((k.sinMul.directional (1,0)).add
    (((k.cothMul ha).cosMul.add k.neg).directional (0,1))).neg

def Kernel.verticalTranspose (ha : 0 < a) (k : Kernel a b) : Kernel a b :=
  ((k.cosMul.directional (1,0)).add
    (((k.cothMul ha).sinMul.neg).directional (0,1))).neg

theorem Kernel.boundary_left (k : Kernel a b) (theta : ℝ) : k (a,theta) = 0 := by
  have he : EqOn (fun r => k (r,theta)) (fun _ => 0) (Iio a) :=
    fun r hr => k.vanish (r,theta) (fun h => (not_le_of_gt hr) h.1)
  exact he.closure (k.smooth.continuous.comp (continuous_id.prodMk continuous_const))
    continuous_const (by simp)

theorem Kernel.boundary_right (k : Kernel a b) (theta : ℝ) : k (b,theta) = 0 := by
  have he : EqOn (fun r => k (r,theta)) (fun _ => 0) (Ioi b) :=
    fun r hr => k.vanish (r,theta) (fun h => (not_le_of_gt hr) h.2)
  exact he.closure (k.smooth.continuous.comp (continuous_id.prodMk continuous_const))
    continuous_const (by simp)

end
end GaloisForLFunctions.HTGeometry.SmoothCylinder
