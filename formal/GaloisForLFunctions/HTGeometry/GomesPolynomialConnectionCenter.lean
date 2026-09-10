import GaloisForLFunctions.HTGeometry.GomesPolynomialConnectionMatrixCommutant
import Mathlib.Data.Matrix.Basis

/-!
# Recovering polynomial evolution from the center of the symmetry algebra

The full connection commutant is a matrix algebra, whose center consists of scalar
polynomial matrices. Thus the symmetries commuting with every symmetry are exactly
polynomials in the connection itself. The polynomial is unique.
-/

noncomputable section
open Polynomial

namespace GaloisForLFunctions.HTGeometry

/-- A symmetry is central exactly when it is polynomial evolution in the connection. -/
theorem gomesPolynomialConnectionCommutant_center_iff
    (A : GomesNonconstantPolynomialCoefficient) (E : GomesPolynomialConnectionCommutant A.val) :
    (∀ F : GomesPolynomialConnectionCommutant A.val, E * F = F * E) ↔
      ∃ P : ℝ[X], E = gomesPolynomialConnectionPolynomialSymmetry A.val P := by
  let e := gomesPolynomialConnectionCommutantMatrixEquiv A
  constructor
  · intro h
    have hc : e E ∈ Set.center (Matrix (Fin A.val.natDegree) (Fin A.val.natDegree) ℝ[X]) := by
      rw [Semigroup.mem_center_iff]
      intro M
      obtain ⟨F, rfl⟩ := e.surjective M
      simpa only [map_mul] using congrArg e (h F).symm
    rw [Matrix.center_eq_range] at hc
    obtain ⟨P, hP⟩ := hc
    refine ⟨P, e.injective ?_⟩
    change gomesPolynomialConnectionCommutantMatrixEquiv A E =
      gomesPolynomialConnectionCommutantMatrixEquiv A
        (gomesPolynomialConnectionPolynomialSymmetry A.val P)
    rw [gomesPolynomialConnectionPolynomialSymmetry_matrix]
    exact hP.symm
  · rintro ⟨P, rfl⟩ F
    apply e.injective
    simp only [map_mul]
    change gomesPolynomialConnectionCommutantMatrixEquiv A
        (gomesPolynomialConnectionPolynomialSymmetry A.val P) * e F =
      e F * gomesPolynomialConnectionCommutantMatrixEquiv A
        (gomesPolynomialConnectionPolynomialSymmetry A.val P)
    rw [gomesPolynomialConnectionPolynomialSymmetry_matrix]
    have hc : Matrix.scalar (Fin A.val.natDegree) P ∈
        Set.center (Matrix (Fin A.val.natDegree) (Fin A.val.natDegree) ℝ[X]) := by
      rw [Matrix.center_eq_range]
      exact ⟨P, rfl⟩
    exact ((Semigroup.mem_center_iff).mp hc (e F)).symm

/-- Central symmetry determines one unique operator polynomial. -/
theorem gomesPolynomialConnectionCommutant_center_unique_iff
    (A : GomesNonconstantPolynomialCoefficient) (E : GomesPolynomialConnectionCommutant A.val) :
    (∀ F : GomesPolynomialConnectionCommutant A.val, E * F = F * E) ↔
      ∃! P : ℝ[X], E = gomesPolynomialConnectionPolynomialSymmetry A.val P := by
  rw [gomesPolynomialConnectionCommutant_center_iff]
  constructor
  · rintro ⟨P, hP⟩
    refine ⟨P, hP, ?_⟩
    intro Q hQ
    exact gomesPolynomialConnectionPolynomialSymmetry_injective A (hQ.symm.trans hP)
  · rintro ⟨P, hP, _⟩
    exact ⟨P, hP⟩

/-- Polynomial evolution commutes with the entire symmetry algebra, in every positive degree. -/
theorem gomesPolynomialConnectionPolynomialSymmetry_central
    (A : GomesNonconstantPolynomialCoefficient) (P : ℝ[X])
    (E : GomesPolynomialConnectionCommutant A.val) :
    gomesPolynomialConnectionPolynomialSymmetry A.val P * E =
      E * gomesPolynomialConnectionPolynomialSymmetry A.val P :=
  (gomesPolynomialConnectionCommutant_center_iff A _).mpr ⟨P, rfl⟩ E

/-- The center can be read as the range of the faithful polynomial operator representation. -/
theorem gomesPolynomialConnectionCommutant_center_range
    (A : GomesNonconstantPolynomialCoefficient) :
    Set.center (GomesPolynomialConnectionCommutant A.val) =
      Set.range (gomesPolynomialConnectionPolynomialSymmetry A.val) := by
  ext E
  rw [Semigroup.mem_center_iff]
  constructor
  · intro h
    obtain ⟨P, hP⟩ := (gomesPolynomialConnectionCommutant_center_iff A E).mp
      (fun F => (h F).symm)
    exact ⟨P, hP.symm⟩
  · rintro ⟨P, rfl⟩ F
    exact (gomesPolynomialConnectionPolynomialSymmetry_central A P F).symm

end GaloisForLFunctions.HTGeometry
