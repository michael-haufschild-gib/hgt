import GaloisForLFunctions.HTGeometry.ChronologicalTensor.RecoverySurgeryDomain

/-!
# Faithful polynomial observations on every surgery domain

An explicit rectangle lies in the inscribed core. Repeated univariate root
rigidity therefore proves injectivity of full two-variable polynomial
evaluation. The observed cusp algebra is exactly the image of the same
abstract cusp algebra; its available observations cannot acquire new relations.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section
open Polynomial Set

theorem recoverySurgeryDomain_rectangle (n : ℕ) (u c : ℝ)
    (hu : u ∈ Icc (recoverySurgeryCoreScale n) (5*recoverySurgeryCoreScale n/4))
    (hc : c ∈ Icc (recoverySurgeryCoreScale n/2) (3*recoverySurgeryCoreScale n/4)) :
    (u,c) ∈ recoverySurgeryDomain n := by
  have hq := recoverySurgeryCoreScale_positive n
  have hcp : 0 < c := by linarith [hc.1]
  have hr : u/c ∈ Icc (1 : ℝ) 3 := by
    constructor
    · apply (le_div_iff₀ hcp).mpr
      linarith [hu.1,hc.2]
    · apply (div_le_iff₀ hcp).mpr
      linarith [hu.2,hc.1]
  have h := recoverySurgeryDomain_core_param n (u/c) c hr
    ⟨le_of_lt hcp,by linarith [hc.2]⟩
  have he : c*(u/c)=u := by field_simp
  simpa only [he] using h

theorem recoverySurgeryDomain_polynomial_faithful (n : ℕ) (P : Polynomial (Polynomial ℝ))
    (hP : ∀ p ∈ recoverySurgeryDomain n, recoveryPlaneEval P p=0) : P=0 := by
  have hq := recoverySurgeryCoreScale_positive n
  apply Polynomial.ext
  intro j
  rw [coeff_zero]
  apply Polynomial.eq_zero_of_infinite_isRoot
  apply (Set.Icc_infinite (show recoverySurgeryCoreScale n<5*recoverySurgeryCoreScale n/4 by linarith)).mono
  intro u hu
  have hc : P.map (Polynomial.evalRingHom u)=0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply (Set.Icc_infinite (show recoverySurgeryCoreScale n/2<3*recoverySurgeryCoreScale n/4 by linarith)).mono
    intro c hc
    change (P.map (Polynomial.evalRingHom u)).eval c=0
    rw [eval_map]
    exact hP (u,c) (recoverySurgeryDomain_rectangle n u c hu hc)
  have h := congrArg (fun R : ℝ[X] => R.coeff j) hc
  change (P.coeff j).eval u=0
  simpa only [coeff_map, coe_evalRingHom, coeff_zero] using h

def recoverySurgeryEvaluation (n : ℕ) :
    Polynomial (Polynomial ℝ) →ₐ[ℝ] (recoverySurgeryDomain n → ℝ) where
  toFun P p := recoveryPlaneEval P p.val
  map_zero' := by funext p; simp only [recoveryPlaneEval,eval₂_zero,Pi.zero_apply]
  map_one' := by funext p; simp only [recoveryPlaneEval,eval₂_one,Pi.one_apply]
  map_add' P Q := by funext p; simp only [recoveryPlaneEval,eval₂_add,Pi.add_apply]
  map_mul' P Q := by funext p; simp only [recoveryPlaneEval,eval₂_mul,Pi.mul_apply]
  commutes' r := by
    funext p
    change recoveryPlaneEval (C (C r)) p.val=r
    simp only [recoveryPlaneEval,eval₂_C,coe_evalRingHom,eval_C]

theorem recoverySurgeryEvaluation_injective (n : ℕ) : Function.Injective (recoverySurgeryEvaluation n) := by
  intro P Q he
  apply sub_eq_zero.mp
  apply recoverySurgeryDomain_polynomial_faithful n (P-Q)
  intro p hp
  have h := congrFun he ⟨p,hp⟩
  change recoveryPlaneEval P p=recoveryPlaneEval Q p at h
  change Polynomial.eval₂ (Polynomial.evalRingHom p.1) p.2 (P-Q)=0
  rw [eval₂_sub]
  exact sub_eq_zero.mpr h

def recoverySurgeryObservedCusp (n : ℕ) : Subalgebra ℝ (recoverySurgeryDomain n → ℝ) :=
  cubicCuspAlgebra.map (recoverySurgeryEvaluation n)

theorem recoverySurgeryObservedCusp_membership (n : ℕ) (P : Polynomial (Polynomial ℝ)) :
    recoverySurgeryEvaluation n P ∈ recoverySurgeryObservedCusp n ↔ P ∈ cubicCuspAlgebra := by
  constructor
  · rintro ⟨Q,hQ,he⟩
    have h := recoverySurgeryEvaluation_injective n he
    rwa [← h]
  · intro hP
    exact ⟨P,hP,rfl⟩

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
