import GaloisForLFunctions.HTGeometry.PeriodicLatticeSections

/-!
# Infinitely many ordinary branch points of the periodic parameter

An exact quadratic difference formula gives ramification order two on an
injective integer-indexed family. No growth or derivative estimate enters.
-/

noncomputable section
open Complex Filter Topology

namespace GaloisForLFunctions.HTGeometry.PeriodicLatticeBranching

open PeriodicLatticeSections

def rationalMap (t : ℂ) : ℂ := numerator t/denominator t
def parameterMap (L : ℝ) (s : ℂ) : ℂ := rationalMap (parameter L s)
def criticalPolynomial (t : ℂ) : ℂ := -a*t^2+2*t-a
def criticalValue : ℂ := (1+ReflectedCubicExponentialModel.rootThree/3)/a

theorem criticalValue_root : criticalPolynomial criticalValue=0 := by
  dsimp [criticalPolynomial,criticalValue]
  field_simp [a_ne_zero]
  ring_nf
  rw [ReflectedCubicExponentialModel.rootThree_sq,a_sq]
  ring

theorem criticalValue_ne_zero : criticalValue ≠ 0 := by
  intro h
  have hc := criticalValue_root
  simp [criticalPolynomial,h,a_ne_zero] at hc

theorem denominator_criticalValue_ne_zero : denominator criticalValue ≠ 0 := by
  intro h
  have hab : a*criticalValue=1 := by
    have := sub_eq_zero.mp h
    exact this.symm
  have hc : -(a*criticalValue)^2+2*(a*criticalValue)-a^2=0 := by
    have hh := criticalValue_root
    unfold criticalPolynomial at hh
    linear_combination a*hh
  rw [hab,a_sq] at hc
  norm_num at hc

theorem rationalMap_difference {t : ℂ} (ht : denominator t ≠ 0) :
    rationalMap t-rationalMap criticalValue=(t-criticalValue)^2/denominator t := by
  have hb := denominator_criticalValue_ne_zero
  have hc := criticalValue_root
  dsimp [rationalMap]
  field_simp
  dsimp [numerator,denominator,criticalPolynomial] at *
  linear_combination (t-criticalValue)*hc

theorem parameterMap_analyticAt (L : ℝ) {s : ℂ}
    (hs : denominator (parameter L s) ≠ 0) : AnalyticAt ℂ (parameterMap L) s := by
  unfold parameterMap rationalMap numerator denominator parameter at *
  fun_prop

theorem parameterMap_branch_order {L : ℝ} (hL : L ≠ 0) (k : ℤ) :
    analyticOrderAt
      (fun s => parameterMap L s-parameterMap L (point L criticalValue k))
      (point L criticalValue k)=2 := by
  let s := point L criticalValue k
  let u : ℂ → ℂ := fun z => parameter L z-criticalValue
  let v : ℂ → ℂ := fun z => (denominator (parameter L z))⁻¹
  have ht : parameter L s=criticalValue := parameter_point hL criticalValue_ne_zero k
  have hd : denominator (parameter L s) ≠ 0 := by
    rw [ht]
    exact denominator_criticalValue_ne_zero
  have hu : AnalyticAt ℂ u s := by unfold u parameter; fun_prop
  have hv : AnalyticAt ℂ v s := by
    unfold v
    apply AnalyticAt.inv
    · unfold denominator parameter
      fun_prop
    · exact hd
  have hL' : (L : ℂ) ≠ 0 := by exact_mod_cast hL
  have hdu : HasDerivAt u (criticalValue*((L : ℂ)/12)) s := by
    simpa only [ht] using (parameter_deriv L s).sub_const criticalValue
  have hou : analyticOrderAt u s=1 :=
    hu.analyticOrderAt_eq_one_of_zero_deriv_ne_zero (by simp [u,ht])
      (by rw [hdu.deriv]; exact mul_ne_zero criticalValue_ne_zero (div_ne_zero hL' (by norm_num)))
  have hov : analyticOrderAt v s=0 :=
    hv.analyticOrderAt_eq_zero.mpr (inv_ne_zero hd)
  have hdcont : ContinuousAt (fun z => denominator (parameter L z)) s := by
    unfold denominator parameter
    fun_prop
  have hde : ∀ᶠ z in 𝓝 s, denominator (parameter L z) ≠ 0 := hdcont.eventually_ne hd
  have he : (fun z => parameterMap L z-parameterMap L s) =ᶠ[𝓝 s] u^2*v := by
    filter_upwards [hde] with z hz
    simp only [Pi.mul_apply,Pi.pow_apply,u,v,parameterMap,ht]
    rw [rationalMap_difference hz,div_eq_mul_inv]
  rw [analyticOrderAt_congr he,analyticOrderAt_mul (hu.pow 2) hv,
    analyticOrderAt_pow hu,hou,hov]
  norm_num [nsmul_eq_mul]

/-- Every point in this explicit infinite family has local ramification order exactly two. -/
theorem infinitely_many_simple_branch_points :
    ∃ ρ : ℤ → ℂ, Function.Injective ρ ∧ ∀ k,
      AnalyticAt ℂ (parameterMap (Real.log 2)) (ρ k) ∧
      analyticOrderAt (fun s => parameterMap (Real.log 2) s-
        parameterMap (Real.log 2) (ρ k)) (ρ k)=2 := by
  have hL : Real.log 2 ≠ 0 := Real.log_ne_zero.mpr (by norm_num)
  refine ⟨point (Real.log 2) criticalValue,point_injective hL _,fun k => ⟨?_,?_⟩⟩
  · apply parameterMap_analyticAt
    rw [parameter_point hL criticalValue_ne_zero]
    exact denominator_criticalValue_ne_zero
  · exact parameterMap_branch_order hL k

end GaloisForLFunctions.HTGeometry.PeriodicLatticeBranching
