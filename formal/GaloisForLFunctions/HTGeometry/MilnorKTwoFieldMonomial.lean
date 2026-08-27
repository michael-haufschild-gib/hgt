import GaloisForLFunctions.HTGeometry.MilnorKTwoWeylUnconditional


/-!
# Full determinant-one monomial group

This constructs Milnor's rank-four monomial target `M` over an arbitrary field. Every element
factors as a determinant-one diagonal matrix times an element of the signed Weyl subgroup `M₀`.
The factorization is structural: adjacent transpositions lift every permutation, then the residual
matrix is proved diagonal with determinant one.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry
namespace MilnorDiagonalExtension

variable {F : Type*} [Field F]

def IsFieldMonomialUnit
    (A : (Matrix (Fin 4) (Fin 4) F)ˣ) : Prop :=
  ∃ (sigma : Equiv.Perm (Fin 4)) (c : Fin 4 → Fˣ),
    (A : Matrix (Fin 4) (Fin 4) F) = signedMonomialMatrix sigma c

def fieldMonomialSubgroup :
    Subgroup (Matrix (Fin 4) (Fin 4) F)ˣ where
  carrier := {A | IsFieldMonomialUnit A}
  one_mem' := ⟨1, fun _ => 1, signedMonomialMatrix_one_field.symm⟩
  mul_mem' {A B} hA hB := by
    obtain ⟨sigma, c, hA⟩ := hA
    obtain ⟨tau, d, hB⟩ := hB
    refine ⟨sigma * tau, fun p => c (tau p) * d p, ?_⟩
    change (A : Matrix (Fin 4) (Fin 4) F) *
      (B : Matrix (Fin 4) (Fin 4) F) = _
    rw [hA, hB, signedMonomialMatrix_mul]
    rfl
  inv_mem' {A} hA := by
    obtain ⟨sigma, c, hA⟩ := hA
    exact ⟨sigma.symm, fun p => (c (sigma.symm p))⁻¹,
      signedMonomialMatrix_inv_data_field A sigma c hA⟩

/-- Full determinant-one monomial group `M` in rank four. -/
def fieldDetOneMonomialSubgroup :
    Subgroup (Matrix (Fin 4) (Fin 4) F)ˣ where
  carrier := {A | IsFieldMonomialUnit A ∧
    Matrix.det (A : Matrix (Fin 4) (Fin 4) F) = 1}
  one_mem' := ⟨fieldMonomialSubgroup.one_mem, by simp⟩
  mul_mem' {A B} hA hB := by
    refine ⟨fieldMonomialSubgroup.mul_mem hA.1 hB.1, ?_⟩
    rw [Units.val_mul, Matrix.det_mul, hA.2, hB.2, one_mul]
  inv_mem' {A} hA := by
    refine ⟨fieldMonomialSubgroup.inv_mem hA.1, ?_⟩
    have hdet := congrArg Matrix.det A.inv_val
    rw [Matrix.det_mul, hA.2, Matrix.det_one, mul_one] at hdet
    change Matrix.det A.inv = 1
    simpa only [mul_one] using hdet

def fieldSignedWeylToDetOneMonomial :
    fieldSignedWeylSubgroup (F := F) →*
      fieldDetOneMonomialSubgroup (F := F) :=
  (fieldSignedWeylSubgroup (F := F)).subtype.codRestrict
    (fieldDetOneMonomialSubgroup (F := F)) (fun A =>
      ⟨by
        obtain ⟨sigma, c, _, hA⟩ := fieldSignedWeylSubgroup_isSignedMonomial A
        exact ⟨sigma, c, hA⟩,
       fieldSignedWeylSubgroup_det_one A⟩)

def detOneDiagonalToFieldMonomial :
    detOneDiagonalUnits F 4 →* fieldDetOneMonomialSubgroup (F := F) :=
  (detOneDiagonalMatrixUnitHom (F := F)).codRestrict
    (fieldDetOneMonomialSubgroup (F := F)) (fun u =>
      ⟨⟨1, u.1, detOneDiagonalMatrixUnitHom_matrix u⟩, by
        rw [detOneDiagonalMatrixUnitHom_matrix,
          det_signedMonomialMatrix_one_field]
        exact congrArg Units.val u.property⟩)

def milnorDiagonalToFieldMonomial :
    MilnorDiagonalExtension F 4 →* fieldDetOneMonomialSubgroup (F := F) :=
  (detOneDiagonalToFieldMonomial (F := F)).comp proj

private theorem exists_fieldMonomialData
    (A : fieldDetOneMonomialSubgroup (F := F)) :
    ∃ q : Equiv.Perm (Fin 4) × (Fin 4 → Fˣ),
      (A.1 : Matrix (Fin 4) (Fin 4) F) =
        signedMonomialMatrix q.1 q.2 := by
  obtain ⟨sigma, c, hA⟩ := A.property.1
  exact ⟨(sigma, c), hA⟩

/-- Unique permutation and column-scale data of a determinant-one monomial matrix. -/
noncomputable def fieldMonomialData
    (A : fieldDetOneMonomialSubgroup (F := F)) :
    Equiv.Perm (Fin 4) × (Fin 4 → Fˣ) :=
  Classical.choose (exists_fieldMonomialData A)

theorem fieldMonomialData_matrix
    (A : fieldDetOneMonomialSubgroup (F := F)) :
    (A.1 : Matrix (Fin 4) (Fin 4) F) =
      signedMonomialMatrix (fieldMonomialData A).1
        (fieldMonomialData A).2 :=
  Classical.choose_spec (exists_fieldMonomialData A)

theorem fieldMonomialData_eq
    {A : fieldDetOneMonomialSubgroup (F := F)}
    {sigma : Equiv.Perm (Fin 4)} {c : Fin 4 → Fˣ}
    (hA : (A.1 : Matrix (Fin 4) (Fin 4) F) =
      signedMonomialMatrix sigma c) :
    (fieldMonomialData A).1 = sigma ∧
      (fieldMonomialData A).2 = c := by
  apply signedMonomialMatrix_data_injective
  rw [← fieldMonomialData_matrix A, hA]

/-- Permutation quotient of Milnor's full determinant-one monomial group. -/
noncomputable def fieldMonomialPermutationHom :
    fieldDetOneMonomialSubgroup (F := F) →* Equiv.Perm (Fin 4) where
  toFun A := (fieldMonomialData A).1
  map_one' :=
    (fieldMonomialData_eq
      (A := (1 : fieldDetOneMonomialSubgroup (F := F)))
      (sigma := 1) (c := fun _ => 1) (by
        simp [signedMonomialMatrix_one_field])).1
  map_mul' A B := by
    let c := (fieldMonomialData A).2
    let d := (fieldMonomialData B).2
    have hAB : (((A * B).1 :
        (Matrix (Fin 4) (Fin 4) F)ˣ) : Matrix (Fin 4) (Fin 4) F) =
        signedMonomialMatrix
          ((fieldMonomialData A).1 * (fieldMonomialData B).1)
          (fun p => c ((fieldMonomialData B).1 p) * d p) := by
      change (A.1 : Matrix (Fin 4) (Fin 4) F) *
        (B.1 : Matrix (Fin 4) (Fin 4) F) = _
      rw [fieldMonomialData_matrix A, fieldMonomialData_matrix B,
        signedMonomialMatrix_mul]
      rfl
    exact (fieldMonomialData_eq hAB).1

def HasFieldSignedLift (sigma : Equiv.Perm (Fin 4)) : Prop :=
  ∃ (A : fieldSignedWeylSubgroup (F := F)) (c : Fin 4 → Fˣ),
    (∀ p, c p = 1 ∨ c p = -1) ∧
      (A.1 : Matrix (Fin 4) (Fin 4) F) = signedMonomialMatrix sigma c

theorem hasFieldSignedLift_one :
    HasFieldSignedLift (F := F) (1 : Equiv.Perm (Fin 4)) := by
  refine ⟨1, fun _ => 1, fun _ => Or.inl rfl, ?_⟩
  simp [signedMonomialMatrix_one_field]

theorem HasFieldSignedLift.mul {sigma tau : Equiv.Perm (Fin 4)}
    (hsigma : HasFieldSignedLift (F := F) sigma)
    (htau : HasFieldSignedLift (F := F) tau) :
    HasFieldSignedLift (F := F) (sigma * tau) := by
  obtain ⟨A, c, hc, hA⟩ := hsigma
  obtain ⟨B, d, hd, hB⟩ := htau
  refine ⟨A * B, fun p => c (tau p) * d p, ?_, ?_⟩
  · intro p
    rcases hc (tau p) with hc' | hc' <;>
      rcases hd p with hd' | hd' <;> simp [hc', hd']
  · change (A.1 : Matrix (Fin 4) (Fin 4) F) *
      (B.1 : Matrix (Fin 4) (Fin 4) F) = _
    rw [hA, hB, signedMonomialMatrix_mul]
    rfl

theorem hasFieldSignedLift_adjacent (i : Fin 3) :
    HasFieldSignedLift (F := F) (Equiv.swap i.castSucc i.succ) := by
  have hij : (i.castSucc : Fin 4) ≠ i.succ := Fin.ne_of_lt i.castSucc_lt_succ
  let A := fieldWeylMatrixGenerator (F := F) (i.castSucc : Fin 4) i.succ hij
  have hA : A ∈ fieldSignedWeylSubgroup :=
    Subgroup.subset_closure ⟨i.castSucc, i.succ, hij, rfl⟩
  refine ⟨⟨A, hA⟩,
    steinbergWeylRootScale (i := (i.castSucc : Fin 4)) (j := i.succ) (1 : Fˣ),
    ?_, ?_⟩
  · intro p
    by_cases hpi : p = (i.castSucc : Fin 4)
    · subst p
      simp [steinbergWeylRootScale]
    · simp [steinbergWeylRootScale, hpi]
  · rw [fieldWeylMatrixGenerator_val,
      weylMatrix_eq_signedMonomial hij]

theorem hasFieldSignedLift_all (sigma : Equiv.Perm (Fin 4)) :
    HasFieldSignedLift (F := F) sigma := by
  have hmem : sigma ∈ Submonoid.closure
      (Set.range fun i : Fin 3 => Equiv.swap i.castSucc i.succ) := by
    rw [Equiv.Perm.mclosure_swap_castSucc_succ 3]
    exact Submonoid.mem_top sigma
  induction hmem using Submonoid.closure_induction with
  | mem sigma hsigma =>
      obtain ⟨i, rfl⟩ := hsigma
      exact hasFieldSignedLift_adjacent i
  | one => exact hasFieldSignedLift_one
  | mul sigma tau _ _ hsigma htau => exact hsigma.mul htau

theorem fieldDetOneMonomial_factorization
    (A : fieldDetOneMonomialSubgroup (F := F)) :
    ∃ (u : detOneDiagonalUnits F 4)
      (B : fieldSignedWeylSubgroup (F := F)),
      A = detOneDiagonalToFieldMonomial u *
        fieldSignedWeylToDetOneMonomial B := by
  obtain ⟨sigma, c, hA⟩ := A.property.1
  obtain ⟨B, d, hd, hB⟩ := hasFieldSignedLift_all (F := F) sigma
  let e : Fin 4 → Fˣ := fun p => c (sigma.symm p) * (d (sigma.symm p))⁻¹
  have hAB : ((A.1 * B.1⁻¹ : (Matrix (Fin 4) (Fin 4) F)ˣ) :
      Matrix (Fin 4) (Fin 4) F) = signedMonomialMatrix 1 e := by
    change (A.1 : Matrix (Fin 4) (Fin 4) F) *
      ((B.1⁻¹ : (Matrix (Fin 4) (Fin 4) F)ˣ) :
        Matrix (Fin 4) (Fin 4) F) = _
    rw [hA, signedMonomialMatrix_inv_data_field B.1 sigma d hB,
      signedMonomialMatrix_mul]
    have hperm : sigma.symm.trans sigma = 1 := by
      apply Equiv.ext
      intro p
      exact sigma.apply_symm_apply p
    rw [hperm]
  have heprod : ∏ p, e p = 1 := by
    apply Units.ext
    have hdetA := A.property.2
    have hdetB := fieldSignedWeylSubgroup_det_one B
    have hdetAB : Matrix.det
        (((A.1 * B.1⁻¹ : (Matrix (Fin 4) (Fin 4) F)ˣ) :
          Matrix (Fin 4) (Fin 4) F)) = 1 := by
      rw [Units.val_mul, Matrix.det_mul]
      have hdetBinv := congrArg Matrix.det B.1.inv_val
      rw [Matrix.det_mul, hdetB, Matrix.det_one, mul_one] at hdetBinv
      have hdetBinv' : Matrix.det
          (((B.1⁻¹ : (Matrix (Fin 4) (Fin 4) F)ˣ) :
            Matrix (Fin 4) (Fin 4) F)) = 1 := by
        change Matrix.det B.1.inv = 1
        simpa only [mul_one] using hdetBinv
      rw [hdetA, hdetBinv', one_mul]
    rw [hAB, det_signedMonomialMatrix_one_field] at hdetAB
    exact hdetAB
  let u : detOneDiagonalUnits F 4 := ⟨e, heprod⟩
  refine ⟨u, B, ?_⟩
  apply Subtype.ext
  apply Units.ext
  have hD : ((detOneDiagonalMatrixUnitHom u :
      (Matrix (Fin 4) (Fin 4) F)ˣ) : Matrix (Fin 4) (Fin 4) F) =
      ((A.1 * B.1⁻¹ : (Matrix (Fin 4) (Fin 4) F)ˣ) :
        Matrix (Fin 4) (Fin 4) F) := by
    rw [detOneDiagonalMatrixUnitHom_matrix, hAB]
  change (A.1 : Matrix (Fin 4) (Fin 4) F) =
    (detOneDiagonalMatrixUnitHom u : Matrix (Fin 4) (Fin 4) F) *
      (B.1 : Matrix (Fin 4) (Fin 4) F)
  rw [hD]
  simp

end MilnorDiagonalExtension
end GaloisForLFunctions.HTGeometry

end
