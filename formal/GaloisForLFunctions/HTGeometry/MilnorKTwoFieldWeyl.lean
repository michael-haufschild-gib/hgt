import GaloisForLFunctions.HTGeometry.MilnorKTwoSpinWeylClassification
import GaloisForLFunctions.HTGeometry.SteinbergWeylSquare

/-!
# Field-valued Weyl matrices and Milnor's zero-symbol branch

This constructs Milnor's ordinary signed-monomial group `M₀` over the source field, including
characteristic two where `-1 = 1`. Its permutation kernel is exactly the diagonal image of `H₀`.
When `{-1,-1}_m = 0`, that common-subgroup map is faithful. This field-valued construction avoids
the spurious real sign kernel that would occur in characteristic two.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

namespace MilnorDiagonalExtension

variable {F : Type*} [Field F]

/-- Determinant-one diagonal units as invertible diagonal matrices. -/
def detOneDiagonalMatrixUnitHom :
    detOneDiagonalUnits F 4 →* (Matrix (Fin 4) (Fin 4) F)ˣ where
  toFun u :=
    { val := Matrix.diagonal fun p => (u.1 p : F)
      inv := Matrix.diagonal fun p => ((u.1 p)⁻¹ : Fˣ)
      val_inv := by
        ext r s
        by_cases hrs : r = s
        · subst r
          simp
        · simp [hrs]
      inv_val := by
        ext r s
        by_cases hrs : r = s
        · subst r
          simp
        · simp [hrs] }
  map_one' := by
    apply Units.ext
    ext r s
    by_cases hrs : r = s
    · subst r
      simp
    · simp [hrs]
  map_mul' u v := by
    apply Units.ext
    ext r s
    by_cases hrs : r = s
    · subst r
      simp
    · simp [hrs]

theorem detOneDiagonalMatrixUnitHom_injective :
    Function.Injective (detOneDiagonalMatrixUnitHom (F := F)) := by
  intro u v huv
  apply Subtype.ext
  funext p
  apply Units.ext
  have h := congrArg Units.val huv
  have hpp := congrFun (congrFun h p) p
  simpa [detOneDiagonalMatrixUnitHom] using hpp

theorem detOneDiagonalMatrixUnitHom_matrix
    (u : detOneDiagonalUnits F 4) :
    (detOneDiagonalMatrixUnitHom u : Matrix (Fin 4) (Fin 4) F) =
      signedMonomialMatrix 1 u.1 := by
  ext r s
  by_cases hrs : r = s
  · subst s
    simp [detOneDiagonalMatrixUnitHom, signedMonomialMatrix]
  · simp [detOneDiagonalMatrixUnitHom, signedMonomialMatrix, hrs]

/-- Field-valued matrix of one canonical signed Weyl generator. -/
def fieldWeylMatrixGenerator (i j : Fin 4) (hij : i ≠ j) :
    (Matrix (Fin 4) (Fin 4) F)ˣ :=
  steinbergToGL (steinbergWeyl hij (1 : Fˣ))

@[simp] theorem fieldWeylMatrixGenerator_val (i j : Fin 4) (hij : i ≠ j) :
    (fieldWeylMatrixGenerator (F := F) i j hij :
      Matrix (Fin 4) (Fin 4) F) = weylMatrix i j (1 : Fˣ) :=
  steinbergToGL_weyl hij 1

/-- Milnor's field-valued ordinary signed-monomial group `M₀`. -/
def fieldSignedWeylSubgroup :
    Subgroup (Matrix (Fin 4) (Fin 4) F)ˣ :=
  Subgroup.closure {A | ∃ (i j : Fin 4) (hij : i ≠ j),
    A = fieldWeylMatrixGenerator i j hij}

def IsFieldSignedMonomialUnit
    (A : (Matrix (Fin 4) (Fin 4) F)ˣ) : Prop :=
  ∃ (σ : Equiv.Perm (Fin 4)) (c : Fin 4 → Fˣ),
    (∀ p, c p = 1 ∨ c p = -1) ∧
      (A : Matrix (Fin 4) (Fin 4) F) = signedMonomialMatrix σ c

theorem signedMonomialMatrix_one_field :
    signedMonomialMatrix (1 : Equiv.Perm (Fin 4))
      (fun _ => (1 : Fˣ)) = 1 := by
  ext r s
  simp [signedMonomialMatrix, Matrix.one_apply]

theorem signedMonomialMatrix_inv_data_field
    (A : (Matrix (Fin 4) (Fin 4) F)ˣ)
    (σ : Equiv.Perm (Fin 4)) (c : Fin 4 → Fˣ)
    (hA : (A : Matrix (Fin 4) (Fin 4) F) = signedMonomialMatrix σ c) :
    ((A⁻¹ : (Matrix (Fin 4) (Fin 4) F)ˣ) : Matrix (Fin 4) (Fin 4) F) =
      signedMonomialMatrix σ.symm (fun p => (c (σ.symm p))⁻¹) := by
  let B := signedMonomialMatrix σ.symm (fun p => (c (σ.symm p))⁻¹)
  have hBA : B * (A : Matrix (Fin 4) (Fin 4) F) = 1 := by
    rw [hA, signedMonomialMatrix_mul]
    ext r s
    simp [signedMonomialMatrix, Matrix.one_apply]
  have hB : B = A.inv := by
    calc
      B = B * 1 := by rw [mul_one]
      _ = B * ((A : Matrix (Fin 4) (Fin 4) F) * A.inv) := by
        rw [A.val_inv]
      _ = (B * (A : Matrix (Fin 4) (Fin 4) F)) * A.inv := by
        rw [mul_assoc]
      _ = A.inv := by rw [hBA, one_mul]
  exact hB.symm

theorem fieldSignedWeylSubgroup_isSignedMonomial
    (A : fieldSignedWeylSubgroup (F := F)) :
    IsFieldSignedMonomialUnit A.1 := by
  rcases A with ⟨A, hA⟩
  induction hA using Subgroup.closure_induction with
  | mem A hA =>
      obtain ⟨i, j, hij, rfl⟩ := hA
      refine ⟨Equiv.swap i j,
        steinbergWeylRootScale (i := i) (j := j) (1 : Fˣ), ?_, ?_⟩
      · intro p
        by_cases hpi : p = i
        · subst p
          simp [steinbergWeylRootScale]
        · by_cases hpj : p = j
          · subst p
            simp [steinbergWeylRootScale, Ne.symm hij]
          · simp [steinbergWeylRootScale, hpi, hpj]
      · rw [fieldWeylMatrixGenerator_val,
          weylMatrix_eq_signedMonomial hij]
  | one =>
      exact ⟨1, fun _ => 1, fun _ => Or.inl rfl,
        signedMonomialMatrix_one_field.symm⟩
  | mul A B _ _ hA hB =>
      obtain ⟨σ, c, hc, hAc⟩ := hA
      obtain ⟨τ, d, hd, hBd⟩ := hB
      refine ⟨τ.trans σ, fun p => c (τ p) * d p, ?_, ?_⟩
      · intro p
        rcases hc (τ p) with hc' | hc' <;>
          rcases hd p with hd' | hd' <;>
          simp [hc', hd']
      · change (A : Matrix (Fin 4) (Fin 4) F) *
          (B : Matrix (Fin 4) (Fin 4) F) = _
        rw [hAc, hBd, signedMonomialMatrix_mul]
  | inv A _ hA =>
      obtain ⟨σ, c, hc, hAc⟩ := hA
      refine ⟨σ.symm, fun p => (c (σ.symm p))⁻¹, ?_,
        signedMonomialMatrix_inv_data_field A σ c hAc⟩
      intro p
      rcases hc (σ.symm p) with h | h
      · left
        simp [h]
      · right
        simp [h]

theorem fieldWeylMatrixGenerator_det (i j : Fin 4) (hij : i ≠ j) :
    Matrix.det (fieldWeylMatrixGenerator (F := F) i j hij :
      Matrix (Fin 4) (Fin 4) F) = 1 := by
  rw [fieldWeylMatrixGenerator_val, ← transvection_weyl hij]
  simp [Matrix.det_mul, Matrix.det_transvection_of_ne, hij, Ne.symm hij]

theorem fieldSignedWeylSubgroup_det_one
    (A : fieldSignedWeylSubgroup (F := F)) :
    Matrix.det (A.1 : Matrix (Fin 4) (Fin 4) F) = 1 := by
  rcases A with ⟨A, hA⟩
  change Matrix.det (A : Matrix (Fin 4) (Fin 4) F) = 1
  induction hA using Subgroup.closure_induction with
  | mem A hA =>
      obtain ⟨i, j, hij, rfl⟩ := hA
      exact fieldWeylMatrixGenerator_det i j hij
  | one => simp
  | mul A B _ _ hA hB =>
      rw [Units.val_mul, Matrix.det_mul, hA, hB, one_mul]
  | inv A _ hA =>
      have hdet := congrArg Matrix.det A.inv_val
      rw [Matrix.det_mul, hA, Matrix.det_one, mul_one] at hdet
      simpa using hdet

private theorem exists_fieldSignedMonomialData
    (A : fieldSignedWeylSubgroup (F := F)) :
    ∃ q : Equiv.Perm (Fin 4) × (Fin 4 → Fˣ),
      (∀ p, q.2 p = 1 ∨ q.2 p = -1) ∧
        (A.1 : Matrix (Fin 4) (Fin 4) F) =
          signedMonomialMatrix q.1 q.2 := by
  obtain ⟨σ, c, hc, hA⟩ := fieldSignedWeylSubgroup_isSignedMonomial A
  exact ⟨(σ, c), hc, hA⟩

noncomputable def fieldSignedMonomialData
    (A : fieldSignedWeylSubgroup (F := F)) :
    Equiv.Perm (Fin 4) × (Fin 4 → Fˣ) :=
  Classical.choose (exists_fieldSignedMonomialData A)

theorem fieldSignedMonomialData_signs
    (A : fieldSignedWeylSubgroup (F := F)) :
    ∀ p, (fieldSignedMonomialData A).2 p = 1 ∨
      (fieldSignedMonomialData A).2 p = -1 :=
  (Classical.choose_spec (exists_fieldSignedMonomialData A)).1

theorem fieldSignedMonomialData_matrix
    (A : fieldSignedWeylSubgroup (F := F)) :
    (A.1 : Matrix (Fin 4) (Fin 4) F) =
      signedMonomialMatrix (fieldSignedMonomialData A).1
        (fieldSignedMonomialData A).2 :=
  (Classical.choose_spec (exists_fieldSignedMonomialData A)).2

theorem fieldSignedMonomialData_eq
    {A : fieldSignedWeylSubgroup (F := F)}
    {σ : Equiv.Perm (Fin 4)} {c : Fin 4 → Fˣ}
    (hA : (A.1 : Matrix (Fin 4) (Fin 4) F) =
      signedMonomialMatrix σ c) :
    (fieldSignedMonomialData A).1 = σ ∧
      (fieldSignedMonomialData A).2 = c := by
  apply signedMonomialMatrix_data_injective
  rw [← fieldSignedMonomialData_matrix A, hA]

/-- Permutation quotient of Milnor's field-valued `M₀`. -/
noncomputable def fieldSignedPermutationHom :
    fieldSignedWeylSubgroup (F := F) →* Equiv.Perm (Fin 4) where
  toFun A := (fieldSignedMonomialData A).1
  map_one' :=
    (fieldSignedMonomialData_eq
      (A := (1 : fieldSignedWeylSubgroup (F := F)))
      (σ := 1) (c := fun _ => 1) (by
        simp [signedMonomialMatrix_one_field])).1
  map_mul' A B := by
    let c := (fieldSignedMonomialData A).2
    let d := (fieldSignedMonomialData B).2
    have hAB : (((A * B).1 :
        (Matrix (Fin 4) (Fin 4) F)ˣ) : Matrix (Fin 4) (Fin 4) F) =
        signedMonomialMatrix
          ((fieldSignedMonomialData A).1 * (fieldSignedMonomialData B).1)
          (fun p => c ((fieldSignedMonomialData B).1 p) * d p) := by
      change (A.1 : Matrix (Fin 4) (Fin 4) F) *
        (B.1 : Matrix (Fin 4) (Fin 4) F) = _
      rw [fieldSignedMonomialData_matrix A, fieldSignedMonomialData_matrix B,
        signedMonomialMatrix_mul]
      rfl
    exact (fieldSignedMonomialData_eq hAB).1

def fieldDiagonalSignedSubgroup :
    Subgroup (fieldSignedWeylSubgroup (F := F)) :=
  fieldSignedPermutationHom.ker

theorem mem_fieldDiagonalSignedSubgroup_iff
    (A : fieldSignedWeylSubgroup (F := F)) :
    A ∈ fieldDiagonalSignedSubgroup ↔
      ∃ c : Fin 4 → Fˣ, (∀ p, c p = 1 ∨ c p = -1) ∧
        (A.1 : Matrix (Fin 4) (Fin 4) F) =
          signedMonomialMatrix 1 c := by
  constructor
  · intro hA
    refine ⟨(fieldSignedMonomialData A).2,
      fieldSignedMonomialData_signs A, ?_⟩
    have hperm : (fieldSignedMonomialData A).1 = 1 := hA
    simpa [hperm] using fieldSignedMonomialData_matrix A
  · rintro ⟨c, hc, hA⟩
    change fieldSignedPermutationHom A = 1
    exact (fieldSignedMonomialData_eq hA).1

theorem det_signedMonomialMatrix_one_field (c : Fin 4 → Fˣ) :
    Matrix.det (signedMonomialMatrix 1 c) = ∏ p, (c p : F) := by
  rw [show signedMonomialMatrix 1 c = Matrix.diagonal (fun p => (c p : F)) by
    ext r s
    by_cases hrs : r = s
    · subst s
      simp [signedMonomialMatrix]
    · simp [signedMonomialMatrix, hrs]]
  exact Matrix.det_diagonal

theorem detOneDiagonalMatrixUnitHom_fin4MatsumotoDiagonal
    {i j : Fin 4} (hij : i ≠ j) (u : Fˣ) :
    detOneDiagonalMatrixUnitHom (fin4MatsumotoDiagonal i j u) =
      diagUnit hij u := by
  apply Units.ext
  ext r s
  by_cases hrs : r = s
  · subst s
    by_cases hri : r = i
    · subst r
      simp [detOneDiagonalMatrixUnitHom, fin4MatsumotoDiagonal,
        diagUnit, diagMatrix, hij, Ne.symm hij]
    · by_cases hrj : r = j
      · subst r
        simp [detOneDiagonalMatrixUnitHom, fin4MatsumotoDiagonal,
          diagUnit, diagMatrix, hri, hij]
      · simp [detOneDiagonalMatrixUnitHom, fin4MatsumotoDiagonal,
          diagUnit, diagMatrix, hri, hrj, Ne.symm hri, Ne.symm hrj]
  · have hi : ¬(i = r ∧ i = s) := by
      rintro ⟨hir, his⟩
      exact hrs (hir.symm.trans his)
    have hj : ¬(j = r ∧ j = s) := by
      rintro ⟨hjr, hjs⟩
      exact hrs (hjr.symm.trans hjs)
    simp [detOneDiagonalMatrixUnitHom, diagUnit, diagMatrix,
      hrs, hi, hj]

theorem fieldWeylMatrixGenerator_sq (i j : Fin 4) (hij : i ≠ j) :
    fieldWeylMatrixGenerator (F := F) i j hij ^ 2 =
      detOneDiagonalMatrixUnitHom (fin4MatsumotoDiagonal i j (-1 : Fˣ)) := by
  rw [pow_two, detOneDiagonalMatrixUnitHom_fin4MatsumotoDiagonal hij]
  change steinbergToGL (steinbergWeyl hij (1 : Fˣ)) *
      steinbergToGL (steinbergWeyl hij (1 : Fˣ)) = diagUnit hij (-1 : Fˣ)
  rw [← map_mul]
  exact steinbergToGL_weyl_sq hij 1

def fin4MilnorH0DiagonalMatrixHom :
    fin4MilnorH0 (F := F) →* (Matrix (Fin 4) (Fin 4) F)ˣ :=
  detOneDiagonalMatrixUnitHom.comp
    (proj.comp (fin4MilnorH0 (F := F)).subtype)

theorem fin4MilnorH0DiagonalMatrixHom_mem_fieldSignedWeyl
    (x : fin4MilnorH0 (F := F)) :
    fin4MilnorH0DiagonalMatrixHom x ∈ fieldSignedWeylSubgroup := by
  rcases x with ⟨x, hx⟩
  change detOneDiagonalMatrixUnitHom x.diag ∈ fieldSignedWeylSubgroup
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨i, j, hij, rfl⟩ := hx
      change detOneDiagonalMatrixUnitHom (fin4MatsumotoDiagonal i j (-1 : Fˣ)) ∈
        fieldSignedWeylSubgroup
      rw [← fieldWeylMatrixGenerator_sq i j hij]
      exact fieldSignedWeylSubgroup.pow_mem
        (Subgroup.subset_closure ⟨i, j, hij, rfl⟩) 2
  | one =>
      change detOneDiagonalMatrixUnitHom (1 : detOneDiagonalUnits F 4) ∈
        fieldSignedWeylSubgroup
      rw [map_one]
      exact fieldSignedWeylSubgroup.one_mem
  | mul x y _ _ hx hy =>
      change detOneDiagonalMatrixUnitHom (x.diag * y.diag) ∈
        fieldSignedWeylSubgroup
      rw [map_mul]
      exact fieldSignedWeylSubgroup.mul_mem hx hy
  | inv x _ hx =>
      change detOneDiagonalMatrixUnitHom x.diag⁻¹ ∈ fieldSignedWeylSubgroup
      rw [map_inv]
      exact fieldSignedWeylSubgroup.inv_mem hx

/-- Common-subgroup map for Milnor's `e_F=0` branch. -/
def fin4MilnorH0ToFieldSignedWeyl :
    fin4MilnorH0 (F := F) →* fieldSignedWeylSubgroup (F := F) :=
  (fin4MilnorH0DiagonalMatrixHom (F := F)).codRestrict
    (fieldSignedWeylSubgroup (F := F))
    (fin4MilnorH0DiagonalMatrixHom_mem_fieldSignedWeyl (F := F))

theorem fin4MilnorH0ToFieldSignedWeyl_mem_diagonal
    (x : fin4MilnorH0 (F := F)) :
    fin4MilnorH0ToFieldSignedWeyl x ∈ fieldDiagonalSignedSubgroup := by
  rw [mem_fieldDiagonalSignedSubgroup_iff]
  refine ⟨x.1.diag.1, fin4MilnorH0_signs x, ?_⟩
  change (detOneDiagonalMatrixUnitHom x.1.diag :
    Matrix (Fin 4) (Fin 4) F) = _
  exact detOneDiagonalMatrixUnitHom_matrix x.1.diag

/-- Exact common subgroup: diagonal kernel of field-valued `M₀` is the image of `H₀`. -/
theorem fin4MilnorH0ToFieldSignedWeyl_range_eq_diagonal :
    MonoidHom.range (fin4MilnorH0ToFieldSignedWeyl (F := F)) =
      fieldDiagonalSignedSubgroup := by
  ext A
  constructor
  · rintro ⟨x, rfl⟩
    exact fin4MilnorH0ToFieldSignedWeyl_mem_diagonal x
  · intro hA
    obtain ⟨c, hc, hAmatrix⟩ :=
      (mem_fieldDiagonalSignedSubgroup_iff A).mp hA
    have hdet := fieldSignedWeylSubgroup_det_one A
    rw [hAmatrix, det_signedMonomialMatrix_one_field] at hdet
    have hcprod : ∏ p, c p = 1 := by
      apply Units.ext
      simpa using hdet
    let u : detOneDiagonalUnits F 4 := ⟨c, hcprod⟩
    let x0 : MilnorDiagonalExtension F 4 := ⟨u, 0⟩
    have hx0sign : x0 ∈ fin4MilnorSignSubgroup (F := F) := by
      constructor
      · exact hc
      · exact (AddSubgroup.zmultiples (fin4MinusOneSymbol F)).zero_mem
    have hx0H0 : x0 ∈ fin4MilnorH0 (F := F) :=
      fin4MilnorSignSubgroup_le_H0 hx0sign
    let x : fin4MilnorH0 (F := F) := ⟨x0, hx0H0⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    apply Units.ext
    change (detOneDiagonalMatrixUnitHom u : Matrix (Fin 4) (Fin 4) F) =
      (A.1 : Matrix (Fin 4) (Fin 4) F)
    rw [detOneDiagonalMatrixUnitHom_matrix]
    exact hAmatrix.symm

theorem fin4MilnorH0ToFieldSignedWeyl_injective
    (he : fin4MinusOneSymbol F = 0) :
    Function.Injective (fin4MilnorH0ToFieldSignedWeyl (F := F)) := by
  intro x y hxy
  have hdiag : x.1.diag = y.1.diag := by
    apply detOneDiagonalMatrixUnitHom_injective
    exact congrArg (fun z : fieldSignedWeylSubgroup => z.1) hxy
  have hxcentral : x.1.central = 0 := by
    obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp
      (fin4MilnorH0_le_signSubgroup x.2).2
    rw [he] at hm
    simpa using hm.symm
  have hycentral : y.1.central = 0 := by
    obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp
      (fin4MilnorH0_le_signSubgroup y.2).2
    rw [he] at hm
    simpa using hm.symm
  apply Subtype.ext
  apply MilnorDiagonalExtension.ext
  · exact hdiag
  · rw [hxcentral, hycentral]

end MilnorDiagonalExtension
end GaloisForLFunctions.HTGeometry

end
