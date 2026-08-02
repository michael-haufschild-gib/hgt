import GaloisForLFunctions.HTGeometry.PrimeClockPolynomialSaturation

/-!
# Cyclic orbit freeness in the finite-ray clock quotient

Polynomial clock saturation says that a nonzero clock polynomial cannot make a nonlocal profile
local.  This file extracts its exact module-theoretic consequence: every nonzero quotient class
generates a free cyclic polynomial-clock module.

The statement is abstract in the ray set and clock spectrum.  It is the source-side freeness
criterion consumed by exact analytic prime-clock correspondence.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

noncomputable section

/-- Complete monomial clock orbit of a profile in the quotient by finite-ray profiles. -/
def rayClockPolynomialOrbit {Ω P : Type*}
    (ray : Ω → P) (weight : Ω → ℂ) (a : Ω → ℂ) (k : ℕ) :
    (Ω → ℂ) ⧸ rayLocalSubmodule ray :=
  (rayLocalSubmodule ray).mkQ (polynomialClockApply weight (X ^ k) a)

/-- **Cyclic clock-orbit freeness.**  A profile nonlocal in ray space has a linearly independent
complete monomial orbit under every injective diagonal clock. -/
theorem rayClockPolynomialOrbit_linearIndependent_of_not_local
    {Ω P : Type*} (ray : Ω → P) (weight : Ω → ℂ)
    (hweight : Function.Injective weight) (a : Ω → ℂ)
    (ha : ¬ RayLocal ray a) :
    LinearIndependent ℂ (rayClockPolynomialOrbit ray weight a) := by
  rw [linearIndependent_iff]
  intro l hl
  by_contra hlne
  let Q : ℂ[X] := ⟨AddMonoidAlgebra.ofCoeff l⟩
  have hQ : Q ≠ 0 := by
    intro hzero
    apply hlne
    apply Finsupp.ext
    intro n
    have hcoeff := congrArg (Polynomial.coeff · n) hzero
    simpa [Q, Polynomial.coeff_ofFinsupp] using hcoeff
  have hprofile :
      Finsupp.linearCombination ℂ
          (fun k => polynomialClockApply weight (X ^ k) a) l =
        polynomialClockApply weight Q a := by
    funext x
    rw [Finsupp.linearCombination_apply]
    rw [Finsupp.sum]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      polynomialClockApply, Polynomial.eval_pow, Polynomial.eval_X]
    rw [Polynomial.eval_eq_sum]
    change
      (∑ i ∈ l.support, l i * (weight x ^ i * a x)) =
        (∑ i ∈ l.support, l i * weight x ^ i) * a x
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hclass :
      (rayLocalSubmodule ray).mkQ (polynomialClockApply weight Q a) = 0 := by
    rw [← hprofile]
    rw [Finsupp.linearCombination_apply]
    rw [map_finsuppSum]
    simpa [rayClockPolynomialOrbit, Finsupp.linearCombination_apply,
      Submodule.mkQ_apply] using hl
  have hlocal : RayLocal ray (polynomialClockApply weight Q a) := by
    change polynomialClockApply weight Q a ∈ rayLocalSubmodule ray
    exact (Submodule.Quotient.mk_eq_zero (rayLocalSubmodule ray)).mp hclass
  exact ha ((rayLocal_polynomialClockApply_iff
    ray weight hweight Q hQ a).mp hlocal)

end

end GaloisForLFunctions.HTGeometry
