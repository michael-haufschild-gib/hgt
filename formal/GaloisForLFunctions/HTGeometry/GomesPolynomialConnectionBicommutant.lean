import GaloisForLFunctions.HTGeometry.GomesPolynomialConnectionMatrixUnits

/-!
# Algebraic reconstruction from all connection symmetries

Even among all real-linear endomorphisms, commuting with every connection symmetry
forces an endomorphism to be a unique polynomial in the connection. This is an exact
algebraic bicommutant theorem; it uses no topology or closure operation.
-/

noncomputable section
open Polynomial

namespace GaloisForLFunctions.HTGeometry

/-- The algebraic bicommutant of a nonconstant connection is its polynomial operator algebra. -/
theorem gomesPolynomialConnection_bicommutant_iff
    (A : GomesNonconstantPolynomialCoefficient) (F : ℝ[X] →ₗ[ℝ] ℝ[X]) :
    (∀ E : ℝ[X] →ₗ[ℝ] ℝ[X], E ∈ gomesPolynomialConnectionCommutantAlgebra A.val →
      F.comp E = E.comp F) ↔
        ∃ P : ℝ[X], F = (Polynomial.aeval (gomesPolynomialFirstOrderLinearMap A.val)) P := by
  constructor
  · intro h
    have ht : gomesPolynomialFirstOrderLinearMap A.val ∈
        gomesPolynomialConnectionCommutantAlgebra A.val := by
      apply (gomesPolynomialConnectionCommutant_mem_iff A.val _).mpr
      rfl
    have hf : F ∈ gomesPolynomialConnectionCommutantAlgebra A.val :=
      (gomesPolynomialConnectionCommutant_mem_iff A.val F).mpr (h _ ht)
    let f : GomesPolynomialConnectionCommutant A.val := ⟨F, hf⟩
    have hc : ∀ E : GomesPolynomialConnectionCommutant A.val, f * E = E * f := by
      intro E
      exact Subtype.ext (h E.val E.property)
    obtain ⟨P, hP⟩ := (gomesPolynomialConnectionCommutant_center_iff A f).mp hc
    exact ⟨P, congrArg Subtype.val hP⟩
  · rintro ⟨P, rfl⟩ E hE
    exact congrArg Subtype.val
      (gomesPolynomialConnectionPolynomialSymmetry_central A P ⟨E, hE⟩)

/-- Reconstructing a real-linear map from all connection symmetries determines a unique polynomial. -/
theorem gomesPolynomialConnection_bicommutant_unique_iff
    (A : GomesNonconstantPolynomialCoefficient) (F : ℝ[X] →ₗ[ℝ] ℝ[X]) :
    (∀ E : ℝ[X] →ₗ[ℝ] ℝ[X], E ∈ gomesPolynomialConnectionCommutantAlgebra A.val →
      F.comp E = E.comp F) ↔
        ∃! P : ℝ[X], F = (Polynomial.aeval (gomesPolynomialFirstOrderLinearMap A.val)) P := by
  rw [gomesPolynomialConnection_bicommutant_iff]
  constructor
  · rintro ⟨P, hP⟩
    refine ⟨P, hP, ?_⟩
    intro Q hQ
    exact gomesPolynomialConnection_aeval_injective A (hQ.symm.trans hP)
  · rintro ⟨P, hP, _⟩
    exact ⟨P, hP⟩

/-- Every coefficient of degree greater than one supplies a nonzero square-zero symmetry. -/
theorem gomesPolynomialConnection_higher_degree_nilpotent_symmetry
    (A : {A : GomesNonconstantPolynomialCoefficient // 1 < A.val.natDegree}) :
    ∃ E : GomesPolynomialConnectionCommutant A.val.val, E ≠ 0 ∧ E * E = 0 := by
  let i : Fin A.val.val.natDegree := ⟨0, gomesNonconstantPolynomialCoefficient_degree_pos A.val⟩
  let j : Fin A.val.val.natDegree := ⟨1, A.property⟩
  refine ⟨gomesPolynomialConnectionMatrixUnit A.val i j,
    gomesPolynomialConnectionMatrixUnit_ne_zero A.val i j, ?_⟩
  apply (gomesPolynomialConnectionMatrixUnit_square_zero_iff A.val i j).mpr
  intro h
  exact Nat.zero_ne_one (congrArg Fin.val h)

/-- Every coefficient of degree greater than one supplies two noncommuting genuine symmetries. -/
theorem gomesPolynomialConnection_higher_degree_noncommuting_symmetries
    (A : {A : GomesNonconstantPolynomialCoefficient // 1 < A.val.natDegree}) :
    ∃ E F : GomesPolynomialConnectionCommutant A.val.val, E * F ≠ F * E := by
  let i : Fin A.val.val.natDegree := ⟨0, gomesNonconstantPolynomialCoefficient_degree_pos A.val⟩
  let j : Fin A.val.val.natDegree := ⟨1, A.property⟩
  refine ⟨gomesPolynomialConnectionMatrixUnit A.val i j,
    gomesPolynomialConnectionMatrixUnit A.val j i, ?_⟩
  intro h
  have hij := (gomesPolynomialConnectionMatrixUnit_opposite_commute_iff A.val i j).mp h
  exact Nat.zero_ne_one (congrArg Fin.val hij)

end GaloisForLFunctions.HTGeometry
