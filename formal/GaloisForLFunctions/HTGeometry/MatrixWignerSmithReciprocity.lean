import GaloisForLFunctions.HTGeometry.MatrixWignerSmithReporterField
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Matrix.Symmetric

/-!
# Reciprocity-reduced Wigner--Smith tomography

Lorentz reciprocity makes a scattering matrix symmetric.  Its derivative is therefore symmetric,
and the reciprocal tangent `S * Q = -ι S'` is determined by one scalar for each unordered channel
pair.  This file proves that the resulting `N(N+1)/2` panel generates, over the scattering field,
exactly the same differential field as all `N²` Wigner--Smith entries.  It also proves the matching
universal lower bound for linear reporters that distinguish arbitrary symmetric tangents.

The result is an unconditional finite-dimensional bridge.  It does not assert that an analytic
scattering realization of a zeta source exists.
-/

open scoped Differential Matroid

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Set

noncomputable section

universe u v w

/-- The nonredundant scalar panel of a symmetric matrix, indexed by unordered pairs. -/
def symmetricMatrixReporter
    {E : Type u} {I : Type v} (T : Matrix I I E) (hT : T.IsSymm) : Sym2 I → E :=
  Sym2.lift ⟨fun i j => T i j, fun i j => hT.apply j i⟩

@[simp]
theorem symmetricMatrixReporter_mk
    {E : Type u} {I : Type v} (T : Matrix I I E) (hT : T.IsSymm) (i j : I) :
    symmetricMatrixReporter T hT s(i, j) = T i j :=
  rfl

/-- The unordered reporter panel has exactly the same range as all ordered entries of a symmetric
matrix. -/
theorem range_symmetricMatrixReporter_eq_entries
    {E : Type u} {I : Type v} (T : Matrix I I E) (hT : T.IsSymm) :
    Set.range (symmetricMatrixReporter T hT) =
      Set.range (fun p : I × I => T p.1 p.2) := by
  apply Set.Subset.antisymm
  · rintro x ⟨p, rfl⟩
    refine p.ind ?_
    intro i j
    exact ⟨(i, j), rfl⟩
  · rintro x ⟨⟨i, j⟩, rfl⟩
    exact ⟨s(i, j), rfl⟩

/-- The reciprocal Wigner--Smith tangent `S Q`. -/
def reciprocalWignerSmithTangent
    {F E : Type u} [Field F] [Field E] [Algebra F E] [Differential E] {n : ℕ}
    (ι : F) (S : Matrix (Fin (n + 1)) (Fin (n + 1)) E) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) E :=
  S * matrixWignerSmith ι S

/-- For invertible `S`, the reciprocal tangent is the scalar multiple `-ι S'`. -/
theorem reciprocalWignerSmithTangent_eq_smul_matrixDifferential
    {F E : Type u} [Field F] [Field E] [Algebra F E] [Differential E] {n : ℕ}
    (ι : F) (S : Matrix (Fin (n + 1)) (Fin (n + 1)) E) (hdet : S.det ≠ 0) :
    reciprocalWignerSmithTangent ι S =
      (-algebraMap F E ι) • matrixDifferential S := by
  have hunit : IsUnit S.det := isUnit_iff_ne_zero.mpr hdet
  rw [reciprocalWignerSmithTangent, matrixWignerSmith, Matrix.mul_smul,
    ← Matrix.mul_assoc, Matrix.mul_nonsing_inv S hunit, Matrix.one_mul]

/-- Entrywise differentiation preserves matrix symmetry. -/
theorem matrixDifferential_isSymm
    {E : Type u} [Field E] [Differential E] {n : ℕ}
    (S : Matrix (Fin (n + 1)) (Fin (n + 1)) E) (hS : S.IsSymm) :
    (matrixDifferential S).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  change (S j i)′ = (S i j)′
  rw [hS.apply]

/-- Lorentz reciprocity makes the reciprocal Wigner--Smith tangent symmetric. -/
theorem reciprocalWignerSmithTangent_isSymm
    {F E : Type u} [Field F] [Field E] [Algebra F E] [Differential E] {n : ℕ}
    (ι : F) (S : Matrix (Fin (n + 1)) (Fin (n + 1)) E)
    (hS : S.IsSymm) (hdet : S.det ≠ 0) :
    (reciprocalWignerSmithTangent ι S).IsSymm := by
  rw [reciprocalWignerSmithTangent_eq_smul_matrixDifferential ι S hdet]
  exact (matrixDifferential_isSymm S hS).smul _

/-- The algebraic Wigner--Smith reciprocity identity `Qᵀ S = S Q`. -/
theorem matrixWignerSmith_transpose_mul_eq_mul
    {F E : Type u} [Field F] [Field E] [Algebra F E] [Differential E] {n : ℕ}
    (ι : F) (S : Matrix (Fin (n + 1)) (Fin (n + 1)) E)
    (hS : S.IsSymm) (hdet : S.det ≠ 0) :
    Matrix.transpose (matrixWignerSmith ι S) * S = S * matrixWignerSmith ι S := by
  have hT := reciprocalWignerSmithTangent_isSymm ι S hS hdet
  change Matrix.transpose (S * matrixWignerSmith ι S) = S * matrixWignerSmith ι S at hT
  simpa [Matrix.transpose_mul, hS.eq] using hT

/-- Multiplication by an invertible scattering matrix preserves the differential field generated
by a matrix family after the scattering entries are placed in the base.  Symmetry reduces the
tangent side to unordered pairs. -/
theorem differentialAdjoin_scattering_union_symmetricTangent_eq
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E]
    {n : ℕ}
    (S T Q : Matrix (Fin (n + 1)) (Fin (n + 1)) E)
    (hdet : S.det ≠ 0) (hT : T.IsSymm) (hTmul : T = S * Q) :
    differentialAdjoin F
        (Set.range (fun p : Fin (n + 1) × Fin (n + 1) => S p.1 p.2) ∪
          Set.range (symmetricMatrixReporter T hT)) =
      differentialAdjoin F
        (Set.range (fun p : Fin (n + 1) × Fin (n + 1) => S p.1 p.2) ∪
          Set.range (fun p : Fin (n + 1) × Fin (n + 1) => Q p.1 p.2)) := by
  let sSet : Set E :=
    Set.range (fun p : Fin (n + 1) × Fin (n + 1) => S p.1 p.2)
  let tSet : Set E := Set.range (symmetricMatrixReporter T hT)
  let qSet : Set E :=
    Set.range (fun p : Fin (n + 1) × Fin (n + 1) => Q p.1 p.2)
  let BT := differentialAdjoin F (sSet ∪ tSet)
  let BQ := differentialAdjoin F (sSet ∪ qSet)
  have hS_BQ : ∀ i j, S i j ∈ BQ := fun i j =>
    subset_differentialAdjoin F (sSet ∪ qSet) (Or.inl ⟨(i, j), rfl⟩)
  have hQ_BQ : ∀ i j, Q i j ∈ BQ := fun i j =>
    subset_differentialAdjoin F (sSet ∪ qSet) (Or.inr ⟨(i, j), rfl⟩)
  have hS_BT : ∀ i j, S i j ∈ BT := fun i j =>
    subset_differentialAdjoin F (sSet ∪ tSet) (Or.inl ⟨(i, j), rfl⟩)
  have hT_BT : ∀ i j, T i j ∈ BT := by
    intro i j
    have h := subset_differentialAdjoin F (sSet ∪ tSet)
      (Or.inr (show symmetricMatrixReporter T hT s(i, j) ∈ tSet from ⟨s(i, j), rfl⟩))
    simpa using h
  apply le_antisymm
  · apply differentialAdjoin_le F
    · rintro x (hx | hx)
      · rcases hx with ⟨⟨i, j⟩, rfl⟩
        exact hS_BQ i j
      · rcases hx with ⟨p, rfl⟩
        refine p.ind ?_
        intro i j
        have hij := congrArg (fun M => M i j) hTmul
        change T i j = (S * Q) i j at hij
        rw [symmetricMatrixReporter_mk, hij, Matrix.mul_apply]
        exact BQ.sum_mem fun k _ => BQ.mul_mem (hS_BQ i k) (hQ_BQ k j)
    · exact derivationClosed_differentialAdjoin F _
  · have hunit : IsUnit S.det := isUnit_iff_ne_zero.mpr hdet
    have hQeq : Q = S⁻¹ * T := by
      calc
        Q = 1 * Q := (Matrix.one_mul Q).symm
        _ = (S⁻¹ * S) * Q := by rw [Matrix.nonsing_inv_mul S hunit]
        _ = S⁻¹ * (S * Q) := by rw [Matrix.mul_assoc]
        _ = S⁻¹ * T := by rw [← hTmul]
    have hbase : differentialAdjoin F sSet ≤ BT := by
      apply differentialAdjoin_le F
      · intro x hx
        exact subset_differentialAdjoin F (sSet ∪ tSet) (Or.inl hx)
      · exact derivationClosed_differentialAdjoin F _
    have hInv_BT : ∀ i j, S⁻¹ i j ∈ BT := fun i j =>
      hbase (matrix_inv_entry_mem_differentialAdjoin S i j)
    apply differentialAdjoin_le F
    · rintro x (hx | hx)
      · rcases hx with ⟨⟨i, j⟩, rfl⟩
        exact hS_BT i j
      · rcases hx with ⟨⟨i, j⟩, rfl⟩
        have hij := congrArg (fun M => M i j) hQeq
        change Q i j = (S⁻¹ * T) i j at hij
        change Q i j ∈ BT
        rw [hij, Matrix.mul_apply]
        exact BT.sum_mem fun k _ => BT.mul_mem (hInv_BT i k) (hT_BT k j)
    · exact derivationClosed_differentialAdjoin F _

/-- **Reciprocity-reduced generated-field tomography.** Over the differential field generated by
the scattering entries, the unordered reciprocal-tangent reporters and all ordered Wigner--Smith
entries generate exactly the same field. -/
theorem differentialAdjoin_reciprocalWignerSmithReporter_eq_entries
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E]
    {n : ℕ}
    (ι : F) (S : Matrix (Fin (n + 1)) (Fin (n + 1)) E)
    (hS : S.IsSymm) (hdet : S.det ≠ 0) :
    differentialAdjoin F
        (Set.range (fun p : Fin (n + 1) × Fin (n + 1) => S p.1 p.2) ∪
          Set.range (symmetricMatrixReporter (reciprocalWignerSmithTangent ι S)
            (reciprocalWignerSmithTangent_isSymm ι S hS hdet))) =
      differentialAdjoin F
        (Set.range (fun p : Fin (n + 1) × Fin (n + 1) => S p.1 p.2) ∪
          Set.range (fun p : Fin (n + 1) × Fin (n + 1) =>
            matrixWignerSmith ι S p.1 p.2)) := by
  exact differentialAdjoin_scattering_union_symmetricTangent_eq
    S (reciprocalWignerSmithTangent ι S) (matrixWignerSmith ι S) hdet
      (reciprocalWignerSmithTangent_isSymm ι S hS hdet) rfl

/-- The unordered tangent panel and the ordered matrix family have equal extended rank after the
scattering entries are contracted.  This is the literal relative differential-matroid form of the
generated-field equality. -/
theorem differentialMatroid_contract_scattering_symmetricTangent_eRk_eq
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    {n : ℕ}
    (S T Q : Matrix (Fin (n + 1)) (Fin (n + 1)) E)
    (hdet : S.det ≠ 0) (hT : T.IsSymm) (hTmul : T = S * Q) :
    (differentialMatroid F E ／
        Set.range (fun p : Fin (n + 1) × Fin (n + 1) => S p.1 p.2)).eRk
          (Set.range (symmetricMatrixReporter T hT)) =
      (differentialMatroid F E ／
        Set.range (fun p : Fin (n + 1) × Fin (n + 1) => S p.1 p.2)).eRk
          (Set.range (fun p : Fin (n + 1) × Fin (n + 1) => Q p.1 p.2)) := by
  let sSet : Set E :=
    Set.range (fun p : Fin (n + 1) × Fin (n + 1) => S p.1 p.2)
  let tSet : Set E := Set.range (symmetricMatrixReporter T hT)
  let qSet : Set E :=
    Set.range (fun p : Fin (n + 1) × Fin (n + 1) => Q p.1 p.2)
  let M := differentialMatroid F E
  let MC := M ／ sSet
  have hfield : differentialAdjoin F (sSet ∪ tSet) =
      differentialAdjoin F (sSet ∪ qSet) := by
    exact differentialAdjoin_scattering_union_symmetricTangent_eq S T Q hdet hT hTmul
  have hfield' : differentialAdjoin F (tSet ∪ sSet) =
      differentialAdjoin F (qSet ∪ sSet) := by
    simpa [Set.union_comm] using hfield
  have hunionClosure : M.closure (tSet ∪ sSet) = M.closure (qSet ∪ sSet) := by
    ext x
    rw [differentialMatroid_mem_closure_iff_differentialAlgebraicOver_differentialAdjoin,
      differentialMatroid_mem_closure_iff_differentialAlgebraicOver_differentialAdjoin,
      hfield']
  have hcontractClosure : MC.closure tSet = MC.closure qSet := by
    change (M ／ sSet).closure tSet = (M ／ sSet).closure qSet
    rw [Matroid.contract_closure_eq, Matroid.contract_closure_eq, hunionClosure]
  change MC.eRk tSet = MC.eRk qSet
  calc
    MC.eRk tSet = MC.eRk (MC.closure tSet) := (MC.eRk_closure_eq tSet).symm
    _ = MC.eRk (MC.closure qSet) := congrArg MC.eRk hcontractClosure
    _ = MC.eRk qSet := MC.eRk_closure_eq qSet

/-- **Relative Kolchin-rank reciprocity law.** Contracting the scattering entries, the
`N(N+1)/2` reciprocal-tangent panel has exactly the rank of all `N²` Wigner--Smith entries. -/
theorem reciprocalWignerSmithReporter_contract_eRk_eq_entries
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    {n : ℕ}
    (ι : F) (S : Matrix (Fin (n + 1)) (Fin (n + 1)) E)
    (hS : S.IsSymm) (hdet : S.det ≠ 0) :
    (differentialMatroid F E ／
        Set.range (fun p : Fin (n + 1) × Fin (n + 1) => S p.1 p.2)).eRk
          (Set.range (symmetricMatrixReporter (reciprocalWignerSmithTangent ι S)
            (reciprocalWignerSmithTangent_isSymm ι S hS hdet))) =
      (differentialMatroid F E ／
        Set.range (fun p : Fin (n + 1) × Fin (n + 1) => S p.1 p.2)).eRk
          (Set.range (fun p : Fin (n + 1) × Fin (n + 1) =>
            matrixWignerSmith ι S p.1 p.2)) := by
  exact differentialMatroid_contract_scattering_symmetricTangent_eRk_eq
    S (reciprocalWignerSmithTangent ι S) (matrixWignerSmith ι S) hdet
      (reciprocalWignerSmithTangent_isSymm ι S hS hdet) rfl

/-- The canonical linear embedding of unordered-pair coordinates into symmetric matrices. -/
def sym2CoordinateMatrixLinearMap
    (K : Type u) [Field K] (I : Type v) :
    (Sym2 I → K) →ₗ[K] Matrix I I K where
  toFun f := fun i j => f s(i, j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem sym2CoordinateMatrixLinearMap_isSymm
    (K : Type u) [Field K] (I : Type v) (f : Sym2 I → K) :
    (sym2CoordinateMatrixLinearMap K I f).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  change f s(j, i) = f s(i, j)
  rw [Sym2.eq_swap]

theorem sym2CoordinateMatrixLinearMap_injective
    (K : Type u) [Field K] (I : Type v) :
    Function.Injective (sym2CoordinateMatrixLinearMap K I) := by
  intro f g hfg
  funext p
  refine p.ind ?_
  intro i j
  have h := congrArg (fun M => M i j) hfg
  exact h

/-- Any linear reporter family that distinguishes every symmetric matrix needs at least one scalar
for each unordered channel pair. -/
theorem card_sym2_le_of_linearReporter_injective
    (K : Type u) [Field K] (I : Type v) (J : Type w)
    [Fintype I] [Fintype J]
    (R : Matrix I I K →ₗ[K] (J → K))
    (hR : Function.Injective (R.comp (sym2CoordinateMatrixLinearMap K I))) :
    Fintype.card (Sym2 I) ≤ Fintype.card J := by
  have hdim := LinearMap.finrank_le_finrank_of_injective hR
  simpa only [Module.finrank_fintype_fun_eq_card] using hdim

/-- An `N`-channel reciprocal tangent has exactly `N(N+1)/2` unordered-pair coordinates. -/
theorem card_sym2_fin_eq (N : ℕ) :
    Fintype.card (Sym2 (Fin N)) = N * (N + 1) / 2 := by
  rw [Sym2.card, Fintype.card_fin, Nat.choose_two_right]
  simp [Nat.mul_comm]

end

end GaloisForLFunctions.HTGeometry
