import GaloisForLFunctions.HTGeometry.DifferentialFieldSolution
import GaloisForLFunctions.HTGeometry.DifferentialPolynomialOver

/-!
# Consistent differential systems have solutions in differential field extensions

A system of differential polynomials over a differential field whose radical differential ideal is
proper has a solution point in some differential field extension: the weak differential
Nullstellensatz applied to the differential polynomial ring, whose derivation differentiates the
coefficients and shifts the jets.  Reading the images of the variables off the resulting map gives
the point, and the map is the evaluation at it because both agree on constants and on jets.

This is the step a differential closure is assembled from.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Differential
open GaloisForLFunctions

/-- The total differential structure on differential polynomials over a differential base. -/
@[reducible] def differentialPolynomialOverDifferential (ι K : Type*) [CommRing K]
    [Differential K] : Differential (DifferentialPolynomial ι K) :=
  ⟨differentialPolynomialOverDerivation ι K⟩

/-- **A consistent differential system has a solution in a differential field extension.**  If the
differential polynomials of a system generate a proper radical differential ideal, then some
differential field extension of the base carries a solution. -/
theorem exists_solution_of_ne_top {F ι : Type u} [Field F] [Algebra ℚ F] [Differential F]
    {I : Ideal (DifferentialPolynomial ι F)} (hrad : I.IsRadical)
    (hδ : ∀ x ∈ I, differentialPolynomialOverDerivation ι F x ∈ I) (hne : I ≠ ⊤) :
    ∃ (L : Type u) (_ : Field L) (_ : Differential L) (f : DifferentialPolynomial ι F →+* L),
      (∀ x, f (differentialPolynomialOverDerivation ι F x) = Differential.deriv (f x)) ∧
        (∀ x ∈ I, f x = 0) := by
  letI : Differential (DifferentialPolynomial ι F) := differentialPolynomialOverDifferential ι F
  have hδ' : ∀ x ∈ I, Differential.deriv x ∈ I := hδ
  obtain ⟨L, hLfield, hLdiff, f, hfδ, hfI⟩ :=
    exists_differentialField_hom_of_ne_top (R := DifferentialPolynomial ι F) hrad hδ' hne
  exact ⟨L, hLfield, hLdiff, f, hfδ, hfI⟩

/-- The jet variables are the iterated derivatives of the base variables. -/
theorem differentialPolynomial_X_eq_jet {ι K : Type*} [CommRing K] [Differential K]
    (i : ι) (n : ℕ) :
    letI := differentialPolynomialOverDifferential ι K
    (MvPolynomial.X (i, n) : DifferentialPolynomial ι K)
      = differentialJet n (MvPolynomial.X (i, 0)) := by
  letI := differentialPolynomialOverDifferential ι K
  induction n with
  | zero => simp
  | succ n ih =>
      rw [differentialJet_succ, ← ih]
      show MvPolynomial.X (i, n + 1)
        = differentialPolynomialOverDerivation ι K (MvPolynomial.X (i, n))
      rw [differentialPolynomialOverDerivation_X]

/-- **A consistent differential system has a solution point in a differential field extension.** -/
theorem exists_point_of_ne_top {F ι : Type u} [Field F] [Algebra ℚ F] [Differential F]
    {I : Ideal (DifferentialPolynomial ι F)} (hrad : I.IsRadical)
    (hδ : ∀ x ∈ I, differentialPolynomialOverDerivation ι F x ∈ I) (hne : I ≠ ⊤) :
    ∃ (L : Type u) (_ : Field L) (_ : Differential L) (_ : Algebra F L),
      (∀ a : F, Differential.deriv (algebraMap F L a) = algebraMap F L (Differential.deriv a)) ∧
      ∃ y : ι → L, ∀ p ∈ I, differentialPolynomialEvalOver (K := F) y p = 0 := by
  classical
  obtain ⟨L, hLfield, hLdiff, f, hfδ, hfI⟩ := exists_solution_of_ne_top hrad hδ hne
  letI := hLfield
  letI := hLdiff
  letI : Algebra F L := (f.comp (MvPolynomial.C : F →+* DifferentialPolynomial ι F)).toAlgebra
  have halg : ∀ a : F, algebraMap F L a = f (MvPolynomial.C a) := fun a => rfl
  refine ⟨L, hLfield, hLdiff, inferInstance, ?_, fun i => f (MvPolynomial.X (i, 0)), ?_⟩
  · intro a
    rw [halg, halg, ← hfδ, differentialPolynomialOverDerivation_C]
  · intro p hp
    have hfeval : ∀ q : DifferentialPolynomial ι F,
        differentialPolynomialEvalOver (K := F) (fun i => f (MvPolynomial.X (i, 0))) q = f q := by
      intro q
      induction q using MvPolynomial.induction_on with
      | C a => rw [differentialPolynomialEvalOver_C, halg]
      | add q r hq hr => rw [map_add, map_add, hq, hr]
      | mul_X q s hq =>
          rw [map_mul, map_mul, hq, differentialPolynomialEvalOver_X]
          congr 1
          letI := differentialPolynomialOverDifferential ι F
          have hjet : ∀ n : ℕ, ∀ i : ι,
              f (MvPolynomial.X (i, n)) = differentialJet n (f (MvPolynomial.X (i, 0))) := by
            intro n
            induction n with
            | zero => intro i; simp
            | succ n ihn =>
                intro i
                rw [differentialJet_succ, ← ihn i, ← hfδ]
                congr 1
                show MvPolynomial.X (i, n + 1)
                  = differentialPolynomialOverDerivation ι F (MvPolynomial.X (i, n))
                rw [differentialPolynomialOverDerivation_X]
          exact (hjet s.2 s.1).symm
    rw [hfeval p]
    exact hfI p hp

end

end GaloisForLFunctions.HTGeometry
