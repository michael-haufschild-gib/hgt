import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Substituting linearly independent linear forms

Sending each indeterminate to a linear form is injective on polynomials as soon as the forms are
linearly independent over the base field: an injective linear map of vector spaces splits, and the
retraction induces the inverse substitution on the generators.  This is the algebraic step behind
the constant-coefficient operator-rank law, where the forms are the shifted operator rows.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

noncomputable section

variable {R : Type*} [CommRing R] [Algebra ℂ R] {B : Type*}

/-- The linear form with prescribed complex coefficients. -/
def linForm (R : Type*) [CommRing R] [Algebra ℂ R] {B : Type*} :
    (B →₀ ℂ) →ₗ[ℂ] MvPolynomial B R :=
  Finsupp.linearCombination ℂ fun b : B => (X b : MvPolynomial B R)

@[simp] theorem linForm_single (b : B) (c : ℂ) :
    linForm R (Finsupp.single b c) = c • (X b : MvPolynomial B R) := by
  simp [linForm]

/-- The coefficient of a single indeterminate in a linear form. -/
theorem coeff_linForm (s : B →₀ ℂ) (b : B) :
    MvPolynomial.coeff (Finsupp.single b 1) (linForm R s) = algebraMap ℂ R (s b) := by
  classical
  induction s using Finsupp.induction_linear with
  | zero => simp
  | add s t hs ht => simp [hs, ht]
  | single b' c =>
      rw [linForm_single, Algebra.smul_def,
        IsScalarTower.algebraMap_apply ℂ R (MvPolynomial B R), algebraMap_eq, coeff_C_mul,
        coeff_X, Finsupp.single_apply]
      by_cases h : b' = b
      · subst h
        simp
      · rw [if_neg fun hc => h (Finsupp.single_left_injective one_ne_zero hc), if_neg h]
        simp

/-- A linear form determines its coefficient vector. -/
theorem linForm_injective (halg : Function.Injective (algebraMap ℂ R)) :
    Function.Injective (linForm R : (B →₀ ℂ) →ₗ[ℂ] MvPolynomial B R) := by
  intro s t hst
  ext b
  exact halg (by rw [← coeff_linForm (R := R) s b, ← coeff_linForm (R := R) t b, hst])

/-- **Substituting linearly independent linear forms is injective.** -/
theorem injective_aeval_linForm {A : Type*} (v : A → (B →₀ ℂ)) (hv : LinearIndependent ℂ v) :
    Function.Injective
      (MvPolynomial.aeval (fun a => linForm R (v a)) : MvPolynomial A R →ₐ[R] MvPolynomial B R) := by
  classical
  have hker : (Finsupp.linearCombination ℂ v).ker = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    exact hv
  obtain ⟨w, hw⟩ := (Finsupp.linearCombination ℂ v).exists_leftInverse_of_injective hker
  set Ψ : MvPolynomial B R →ₐ[R] MvPolynomial A R :=
    MvPolynomial.aeval (fun b => linForm R (w (Finsupp.single b 1))) with hΨ
  have hΨsmul : ∀ (c : ℂ) (p : MvPolynomial B R), Ψ (c • p) = c • Ψ p := by
    intro c p
    exact (Ψ.restrictScalars ℂ).toLinearMap.map_smul c p
  have key : ∀ s : B →₀ ℂ, Ψ (linForm R s) = linForm R (w s) := by
    intro s
    induction s using Finsupp.induction_linear with
    | zero => simp
    | add s t hs ht => simp [hs, ht]
    | single b c =>
        rw [linForm_single, hΨsmul, hΨ, aeval_X]
        have hsm : Finsupp.single b c = c • (Finsupp.single b (1 : ℂ)) := by
          rw [Finsupp.smul_single, smul_eq_mul, mul_one]
        rw [hsm, map_smul, map_smul]
  have hcomp : Ψ.comp (MvPolynomial.aeval (fun a => linForm R (v a)) :
      MvPolynomial A R →ₐ[R] MvPolynomial B R) = AlgHom.id R (MvPolynomial A R) := by
    refine MvPolynomial.algHom_ext fun a => ?_
    have hva : w (v a) = Finsupp.single a 1 := by
      have := congrArg (fun f : (A →₀ ℂ) →ₗ[ℂ] (A →₀ ℂ) => f (Finsupp.single a 1)) hw
      simpa [Finsupp.linearCombination_single] using this
    simp only [AlgHom.comp_apply, aeval_X, AlgHom.id_apply]
    rw [key, hva, linForm_single, one_smul]
  intro p q hpq
  have hp := congrArg Ψ hpq
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply, hcomp] at hp
  simpa using hp

end

end GaloisForLFunctions.HTGeometry
