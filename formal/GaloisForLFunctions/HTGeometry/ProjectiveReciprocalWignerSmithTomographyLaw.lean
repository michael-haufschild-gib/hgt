import GaloisForLFunctions.HTGeometry.MatrixWignerSmithReciprocity
import GaloisForLFunctions.HTGeometry.ProjectiveWignerSmithDifferentialField

/-!
# Projective reciprocity-reduced Wigner--Smith tomography

Lorentz reciprocity makes `S Q` symmetric.  Removing the scalar trace gauge from `Q` changes this
tangent only by a scalar multiple of the symmetric scattering matrix, so `S Q₀` remains symmetric.
Consequently the unordered reciprocal tangent panel gives a nonredundant tomography of every
ordered entry of the projective traceless Wigner--Smith connection over the scattering field.
-/

open scoped Differential Matroid Matrix

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Set

noncomputable section

universe u

/-- Reciprocal tangent of the projective, trace-free Wigner--Smith connection. -/
def projectiveReciprocalWignerSmithTangent
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    [Differential E] [CharZero E] {n : ℕ}
    (iota : F) (S : Matrix (Fin (n + 1)) (Fin (n + 1)) E) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) E :=
  S * matrixTracelessPartField (matrixWignerSmith iota S)

/-- Trace-gauge removal preserves reciprocal symmetry. -/
theorem projectiveReciprocalWignerSmithTangent_isSymm
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    [Differential E] [CharZero E] {n : ℕ}
    (iota : F) (S : Matrix (Fin (n + 1)) (Fin (n + 1)) E)
    (hS : S.IsSymm) (hdet : S.det ≠ 0) :
    (projectiveReciprocalWignerSmithTangent iota S).IsSymm := by
  have hreciprocal := reciprocalWignerSmithTangent_isSymm iota S hS hdet
  rw [projectiveReciprocalWignerSmithTangent, matrixTracelessPartField,
    Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one]
  exact hreciprocal.add (hS.smul _)

/-- The projective connection obeys the same reciprocity identity as the full Wigner--Smith
connection. -/
theorem matrixTracelessWignerSmith_transpose_mul_eq_mul
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    [Differential E] [CharZero E] {n : ℕ}
    (iota : F) (S : Matrix (Fin (n + 1)) (Fin (n + 1)) E)
    (hS : S.IsSymm) (hdet : S.det ≠ 0) :
    Matrix.transpose (matrixTracelessPartField (matrixWignerSmith iota S)) * S =
      S * matrixTracelessPartField (matrixWignerSmith iota S) := by
  have hT := projectiveReciprocalWignerSmithTangent_isSymm iota S hS hdet
  change Matrix.transpose
      (S * matrixTracelessPartField (matrixWignerSmith iota S)) =
    S * matrixTracelessPartField (matrixWignerSmith iota S) at hT
  simpa [Matrix.transpose_mul, hS.eq] using hT

/-- **Projective reciprocity-reduced generated-field tomography.**  Over the scattering field,
the unordered entries of `S Q₀` generate exactly the same differential field as all ordered
entries of the traceless projective connection `Q₀`. -/
theorem differentialAdjoin_projectiveReciprocalWignerSmithReporter_eq_entries
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E]
    [CharZero E] {n : ℕ}
    (iota : F) (S : Matrix (Fin (n + 1)) (Fin (n + 1)) E)
    (hS : S.IsSymm) (hdet : S.det ≠ 0) :
    differentialAdjoin F
        (Set.range (fun p : Fin (n + 1) × Fin (n + 1) => S p.1 p.2) ∪
          Set.range (symmetricMatrixReporter
            (projectiveReciprocalWignerSmithTangent iota S)
            (projectiveReciprocalWignerSmithTangent_isSymm iota S hS hdet))) =
      differentialAdjoin F
        (Set.range (fun p : Fin (n + 1) × Fin (n + 1) => S p.1 p.2) ∪
          Set.range (fun p : Fin (n + 1) × Fin (n + 1) =>
            matrixTracelessPartField (matrixWignerSmith iota S) p.1 p.2)) := by
  exact differentialAdjoin_scattering_union_symmetricTangent_eq
    S (projectiveReciprocalWignerSmithTangent iota S)
      (matrixTracelessPartField (matrixWignerSmith iota S)) hdet
      (projectiveReciprocalWignerSmithTangent_isSymm iota S hS hdet) rfl

/-- **Projective reciprocity relative-rank law.**  After contracting scattering entries, the
unordered projective reciprocal panel and the full ordered traceless connection have identical
differential-matroid rank. -/
theorem projectiveReciprocalWignerSmithReporter_contract_eRk_eq_entries
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E]
    [CharZero E] {n : ℕ}
    (iota : F) (S : Matrix (Fin (n + 1)) (Fin (n + 1)) E)
    (hS : S.IsSymm) (hdet : S.det ≠ 0) :
    (differentialMatroid F E ／
        Set.range (fun p : Fin (n + 1) × Fin (n + 1) => S p.1 p.2)).eRk
          (Set.range (symmetricMatrixReporter
            (projectiveReciprocalWignerSmithTangent iota S)
            (projectiveReciprocalWignerSmithTangent_isSymm iota S hS hdet))) =
      (differentialMatroid F E ／
        Set.range (fun p : Fin (n + 1) × Fin (n + 1) => S p.1 p.2)).eRk
          (Set.range (fun p : Fin (n + 1) × Fin (n + 1) =>
            matrixTracelessPartField (matrixWignerSmith iota S) p.1 p.2)) := by
  exact differentialMatroid_contract_scattering_symmetricTangent_eRk_eq
    S (projectiveReciprocalWignerSmithTangent iota S)
      (matrixTracelessPartField (matrixWignerSmith iota S)) hdet
      (projectiveReciprocalWignerSmithTangent_isSymm iota S hS hdet) rfl

end

end GaloisForLFunctions.HTGeometry
