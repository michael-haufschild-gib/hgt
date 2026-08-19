import Mathlib
import GaloisForLFunctions.HTGeometry.DifferentialTaylorMorphism
import GaloisForLFunctions.HTGeometry.AffineTranslationStabilizerRigidity

/-!
# Constant vector fields and translation of an ideal

In characteristic zero the translation of affine space by a constant vector `h` is the exponential
of the constant vector field `Σ h i ∂/∂X i`.  The exponential is the Taylor morphism of the
polynomial ring viewed as a differential ring for that vector field, evaluated at the parameter
value one, and it is a finite sum because the vector field lowers total degree.

The consequence used by horizon arguments is the infinitesimal criterion: an ideal stable under the
constant vector field is stable under the corresponding translation.  Combined with translation
rigidity this says that a constant tangent direction at a generic point of an affine locus is a
translation symmetry of that locus.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {C ι : Type*} [Field C] [CharZero C]

/-- The constant vector field `Σ h i ∂/∂X i` on affine space. -/
def constVectorField (h : ι → C) :
    Derivation C (MvPolynomial ι C) (MvPolynomial ι C) :=
  MvPolynomial.mkDerivation C fun i => MvPolynomial.C (h i)

omit [CharZero C] in
@[simp] theorem constVectorField_X (h : ι → C) (i : ι) :
    constVectorField h (MvPolynomial.X i) = MvPolynomial.C (h i) :=
  MvPolynomial.mkDerivation_X _ _ _

omit [CharZero C] in
@[simp] theorem constVectorField_C (h : ι → C) (a : C) :
    constVectorField h (MvPolynomial.C a) = 0 := by
  have hC : (MvPolynomial.C a : MvPolynomial ι C) = algebraMap C (MvPolynomial ι C) a := rfl
  rw [hC]
  exact (constVectorField h).map_algebraMap a

/-- The parametrized translation `P ↦ P (X + T h)`, a polynomial in the translation parameter. -/
def translationParameterized (h : ι → C) :
    MvPolynomial ι C →ₐ[C] Polynomial (MvPolynomial ι C) :=
  MvPolynomial.aeval fun i =>
    Polynomial.C (MvPolynomial.X i) + Polynomial.C (MvPolynomial.C (h i)) * Polynomial.X

omit [CharZero C] in
@[simp] theorem translationParameterized_X (h : ι → C) (i : ι) :
    translationParameterized h (MvPolynomial.X i)
      = Polynomial.C (MvPolynomial.X i) + Polynomial.C (MvPolynomial.C (h i)) * Polynomial.X := by
  simp [translationParameterized]

omit [CharZero C] in
/-- At parameter one the parametrized translation is the ordinary translation. -/
theorem eval_one_translationParameterized (h : ι → C) (P : MvPolynomial ι C) :
    Polynomial.eval (1 : MvPolynomial ι C) (translationParameterized h P)
      = mvPolynomialBaseTranslation h P := by
  have hcomp : (Polynomial.evalRingHom (1 : MvPolynomial ι C)).comp
        (translationParameterized h).toRingHom
      = (mvPolynomialBaseTranslation h).toAlgHom.toRingHom := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
    · have hC : (MvPolynomial.C a : MvPolynomial ι C) = algebraMap C (MvPolynomial ι C) a := rfl
      simp [translationParameterized, hC, AlgEquiv.commutes]
    · simp [translationParameterized, mvPolynomialBaseTranslation]
  exact congrArg (fun f : MvPolynomial ι C →+* MvPolynomial ι C => f P) hcomp

/-- **Every coefficient of the parametrized translation is a jet of the constant vector field.** -/
theorem coeff_translationParameterized (h : ι → C) (P : MvPolynomial ι C) (k : ℕ) :
    (translationParameterized h P).coeff k
      = invFactorialCast (MvPolynomial ι C) k * (⇑(constVectorField h))^[k] P := by
  letI : Differential (MvPolynomial ι C) :=
    ⟨Derivation.restrictScalars ℤ (constVectorField h)⟩
  have hderiv : ∀ Q : MvPolynomial ι C, Q′ = constVectorField h Q := fun _ => rfl
  have hCzero : ∀ a : C, (MvPolynomial.C a : MvPolynomial ι C)′ = 0 := by
    intro a; rw [hderiv]; exact constVectorField_C h a
  have hX : ∀ i : ι, differentialTaylor (MvPolynomial.X i : MvPolynomial ι C)
      = PowerSeries.C (MvPolynomial.X i)
        + PowerSeries.C (MvPolynomial.C (h i)) * PowerSeries.X := by
    intro i
    have h1 : differentialJet 1 (MvPolynomial.X i : MvPolynomial ι C)
        = MvPolynomial.C (h i) := by
      rw [differentialJet_succ, differentialJet_zero, hderiv, constVectorField_X]
    have h2 : ∀ n : ℕ, differentialJet (n + 2) (MvPolynomial.X i : MvPolynomial ι C) = 0 := by
      intro n
      have : differentialJet 2 (MvPolynomial.X i : MvPolynomial ι C) = 0 := by
        rw [show (2 : ℕ) = 1 + 1 from rfl, differentialJet_succ, h1, hCzero]
      exact differentialJet_eq_zero_of_le this (by omega)
    ext n
    match n with
    | 0 => simp
    | 1 => rw [coeff_differentialTaylor, h1, invFactorialCast_one, one_mul]; simp
    | (n + 2) =>
        rw [coeff_differentialTaylor, h2 n, mul_zero]
        simp
  have hring : ((Polynomial.coeToPowerSeries.ringHom (R := MvPolynomial ι C)).comp
        ((translationParameterized h).toRingHom))
      = differentialTaylorHom (MvPolynomial ι C) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
    · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, differentialTaylorHom_apply]
      rw [differentialTaylor_of_deriv_eq_zero (hCzero a)]
      simp [translationParameterized]
    · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, differentialTaylorHom_apply, translationParameterized_X, hX i,
        Polynomial.coeToPowerSeries.ringHom_apply]
      push_cast
      ring
  have hco := congrArg (fun f : MvPolynomial ι C →+* PowerSeries (MvPolynomial ι C) => f P) hring
  simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    differentialTaylorHom_apply] at hco
  have hcok := congrArg (PowerSeries.coeff k) hco
  rw [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coeff_coe,
    coeff_differentialTaylor] at hcok
  exact hcok

/-- **The infinitesimal criterion for translation invariance.**  An ideal stable under a constant
vector field is stable under the corresponding translation. -/
theorem mvPolynomialBaseTranslation_mem_of_constVectorField_mem
    (I : Ideal (MvPolynomial ι C)) (h : ι → C)
    (hI : ∀ P ∈ I, constVectorField h P ∈ I) {P : MvPolynomial ι C} (hP : P ∈ I) :
    mvPolynomialBaseTranslation h P ∈ I := by
  classical
  have hjet : ∀ k, (⇑(constVectorField h))^[k] P ∈ I := by
    intro k
    induction k with
    | zero => simpa using hP
    | succ k ih => rw [Function.iterate_succ_apply']; exact hI _ ih
  have hcoeff : ∀ k, (translationParameterized h P).coeff k ∈ I := by
    intro k
    rw [coeff_translationParameterized]
    exact Ideal.mul_mem_left _ _ (hjet k)
  rw [← eval_one_translationParameterized, Polynomial.eval_eq_sum_range]
  refine Ideal.sum_mem _ fun k _ => ?_
  simpa using hcoeff k

end

end GaloisForLFunctions.HTGeometry
