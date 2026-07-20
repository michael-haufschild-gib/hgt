import GaloisForLFunctions.HTGeometry.MvPolynomialAlgHomBaseChange
import GaloisForLFunctions.HTGeometry.SimpleZeroBellHorizon

/-!
# Complete-Bell coordinate change after scalar extension

The finite complete-Bell substitution is already a polynomial automorphism over `ℂ`.  The general
scalar-extension law upgrades it to a polynomial automorphism over every commutative complex
algebra.  This is stronger than value-level invertibility over `ℂ`: it discharges the coefficient
base interface needed to transport Gamma pole coordinates to the rational pole-position field
`ℂ(n)`.
-/

open MvPolynomial

namespace GaloisForLFunctions.HTGeometry

/-- The complete-Bell polynomial automorphism as a complex algebra equivalence. -/
noncomputable def bellCoefficientAlgEquiv (n : ℕ) :
    MvPolynomial (Fin (n + 1)) ℂ ≃ₐ[ℂ] MvPolynomial (Fin (n + 1)) ℂ where
  toRingEquiv := bellCoefficientEquiv n
  commutes' c := by
    change bellCoefficientEquiv n (MvPolynomial.C c) = MvPolynomial.C c
    rw [bellCoefficientEquiv_apply]
    simp [bellCoefficientMap]

/-- Complete-Bell coordinate equivalence after extending the coefficient algebra. -/
noncomputable def bellCoefficientAlgEquivBaseChange
    {K : Type*} [CommSemiring K] [Algebra ℂ K] (n : ℕ) :
    MvPolynomial (Fin (n + 1)) K ≃ₐ[K] MvPolynomial (Fin (n + 1)) K :=
  GaloisForLFunctions.mvPolynomialAlgEquivBaseChange
    (K := K) (bellCoefficientAlgEquiv n)

/-- Complete-Bell substitution after extending the coefficient algebra. -/
noncomputable def bellCoefficientMapBaseChange
    {K : Type*} [CommSemiring K] [Algebra ℂ K] (n : ℕ) :
    MvPolynomial (Fin (n + 1)) K →ₐ[K] MvPolynomial (Fin (n + 1)) K :=
  (bellCoefficientAlgEquivBaseChange (K := K) n).toAlgHom

theorem bellCoefficientMapBaseChange_injective
    {K : Type*} [CommSemiring K] [Algebra ℂ K] (n : ℕ) :
    Function.Injective (bellCoefficientMapBaseChange (K := K) n) :=
  (bellCoefficientAlgEquivBaseChange (K := K) n).injective

@[simp] theorem bellCoefficientMapBaseChange_C
    {K : Type*} [CommSemiring K] [Algebra ℂ K]
    (n : ℕ) (c : K) :
    bellCoefficientMapBaseChange (K := K) n (MvPolynomial.C c) =
      MvPolynomial.C c :=
  GaloisForLFunctions.mvPolynomialAlgHomBaseChange_C _ _

@[simp] theorem bellCoefficientMapBaseChange_X
    {K : Type*} [CommSemiring K] [Algebra ℂ K]
    (n : ℕ) (j : Fin (n + 1)) :
    bellCoefficientMapBaseChange (K := K) n (MvPolynomial.X j) =
      MvPolynomial.map (algebraMap ℂ K)
        (bellAt n ((j : ℕ) + 1) j.isLt) := by
  change GaloisForLFunctions.mvPolynomialAlgHomBaseChange
      (K := K) (bellCoefficientAlgEquiv n).toAlgHom (MvPolynomial.X j) = _
  rw [GaloisForLFunctions.mvPolynomialAlgHomBaseChange_X]
  congr 1
  simp [bellCoefficientAlgEquiv, bellCoefficientEquiv_apply,
    bellCoefficientMap]

end GaloisForLFunctions.HTGeometry
