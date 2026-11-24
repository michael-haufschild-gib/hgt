import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! # Linear and quadratic responses of a tilted terminal spin -/
open Complex Filter Topology
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond
noncomputable section

/-- Square of the splitting for longitudinal field 3/5 and transverse field 4/5+t. -/
def base (t : ℂ) := 1+(8/5:ℂ)*t+t^2

def profile (z t : ℂ) := base t ^ z

theorem base_square (t : ℂ) : base t=(3/5:ℂ)^2+(4/5+t)^2 := by unfold base; ring

@[simp] theorem base_zero : base 0=1 := by simp [base]

@[simp] theorem profile_zero (z : ℂ) : profile z 0=1 := by simp [profile]

private theorem base_analytic (t : ℂ) : AnalyticAt ℂ base t :=
  (analyticAt_const.add (analyticAt_const.mul analyticAt_id)).add (analyticAt_id.pow 2)

theorem profile_analytic (z : ℂ) : AnalyticAt ℂ (profile z) 0 :=
  (base_analytic 0).cpow analyticAt_const (by simp only [base_zero,one_mem_slitPlane])

private theorem base_deriv (t : ℂ) : HasDerivAt base (8/5+2*t) t := by
  have h := ((hasDerivAt_const t (1:ℂ)).add ((hasDerivAt_id t).const_mul (8/5:ℂ))).add (hasDerivAt_pow 2 t)
  change HasDerivAt base _ t at h
  simpa only [Nat.cast_ofNat,show (2:ℕ)-1=1 by decide,pow_one,zero_add,mul_one] using h

private theorem profile_deriv (z t : ℂ) (ht : base t∈slitPlane) :
    HasDerivAt (profile z) (z*profile (z-1) t*(8/5+2*t)) t :=
  (base_deriv t).cpow_const ht

/-- The two derivative coefficients for every complex power of the squared splitting. -/
theorem profile_jet (z : ℂ) :
    deriv (profile z) 0=z*(8/5) ∧
    deriv (deriv (profile z)) 0=z*(z-1)*(8/5)^2+2*z := by
  have h₀ : base 0∈slitPlane := by simp only [base_zero,one_mem_slitPlane]
  have hh : ∀ᶠ t : ℂ in 𝓝 0, base t∈slitPlane := (base_analytic 0).continuousAt (isOpen_slitPlane.mem_nhds h₀)
  have he : deriv (profile z) =ᶠ[𝓝 0] fun t => z*profile (z-1) t*(8/5+2*t) :=
    hh.mono fun t ht => (profile_deriv z t ht).deriv
  refine ⟨by simpa only [profile_zero,mul_one,mul_zero,add_zero] using (profile_deriv z 0 h₀).deriv,?_⟩
  have hd := (((profile_deriv (z-1) 0 h₀).const_mul z).mul
    (((hasDerivAt_id (0:ℂ)).const_mul 2).const_add (8/5:ℂ))).deriv
  rw [he.deriv_eq]
  simp only [id_eq,profile_zero,mul_one,mul_zero,add_zero] at hd
  exact hd.trans (by ring)

/-- Fast splitting and fraction of the longitudinal bond seen in its positive sector. -/
def splitting := profile (1/2)
def alignment (t : ℂ) := (3/5:ℂ)*profile (-(1/2)) t

theorem splitting_square (t : ℂ) : splitting t^2=base t := by
  change (base t ^ (1/2:ℂ))^2=base t
  by_cases h : base t=0
  · simp [h]
  · rw [pow_two,←Complex.cpow_add _ _ h,show (1/2:ℂ)+1/2=1 by norm_num,Complex.cpow_one]

theorem alignment_eq_div (t : ℂ) : alignment t=(3/5:ℂ)/splitting t := by
  simp only [splitting,alignment,profile,Complex.cpow_neg,div_eq_mul_inv]

/-- First and second physical derivatives of the splitting both detect the spin sign. -/
theorem splitting_nondegenerate : deriv splitting 0≠0 ∧ deriv (deriv splitting) 0≠0 := by
  obtain ⟨h₁,h₂⟩ := profile_jet (1/2)
  unfold splitting
  rw [h₁,h₂]
  norm_num

#print axioms profile_jet
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond
