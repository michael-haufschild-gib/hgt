import GaloisForLFunctions.HTGeometry.MilnorKTwoFieldWeyl
import GaloisForLFunctions.HTGeometry.MilnorKTwoWeylAction
import GaloisForLFunctions.HTGeometry.MilnorKTwoAmalgamatedSemidirect


/-!
# Field-valued Weyl action and Milnor's zero-symbol quotient

The existing Steinberg simple-Weyl action descends through the exact field matrix model.
When `{-1,-1}_m = 0`, its common subgroup is faithful and compatible with conjugation,
so the generic identification quotient contains a central injective copy of Milnor `K₂`.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry
namespace MilnorDiagonalExtension

variable {F : Type*} [Field F]

theorem fin4SimpleWeylToFieldSigned_mem
    (s : fin4SimpleWeylSubgroup (F := F)) :
    steinbergToGL s.1 ∈ fieldSignedWeylSubgroup := by
  rcases s with ⟨s, hs⟩
  induction hs using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨i, j, hij, rfl⟩ := hx
      exact Subgroup.subset_closure ⟨i, j, hij, rfl⟩
  | one => simp
  | mul x y _ _ hx hy => simpa using fieldSignedWeylSubgroup.mul_mem hx hy
  | inv x _ hx => simpa using fieldSignedWeylSubgroup.inv_mem hx

/-- Matrix quotient from the Steinberg simple-Weyl subgroup to Milnor's field model. -/
def fin4SimpleWeylToFieldSigned :
    fin4SimpleWeylSubgroup (F := F) →* fieldSignedWeylSubgroup (F := F) :=
  ((steinbergToGL (R := F) (n := Fin 4)).comp
      (fin4SimpleWeylSubgroup (F := F)).subtype).codRestrict
    (fieldSignedWeylSubgroup (F := F))
    fin4SimpleWeylToFieldSigned_mem

theorem fin4SimpleWeylToFieldSigned_surjective :
    Function.Surjective (fin4SimpleWeylToFieldSigned (F := F)) := by
  intro A
  let P := fun B : (Matrix (Fin 4) (Fin 4) F)ˣ =>
    ∀ hB : B ∈ fieldSignedWeylSubgroup (F := F),
      ∃ s, fin4SimpleWeylToFieldSigned s = ⟨B, hB⟩
  have hP : P A.1 := by
    apply Subgroup.closure_induction (p := fun B _ => P B)
      ?_ ?_ ?_ ?_ A.property
    · intro B hB _
      obtain ⟨i, j, hij, rfl⟩ := hB
      refine ⟨⟨steinbergWeyl hij (1 : Fˣ),
        Subgroup.subset_closure ⟨i, j, hij, rfl⟩⟩, ?_⟩
      rfl
    · intro _
      refine ⟨1, ?_⟩
      apply Subtype.ext
      rfl
    · intro B C hB hC ihB ihC hBC
      obtain ⟨s, hs⟩ := ihB hB
      obtain ⟨t, ht⟩ := ihC hC
      refine ⟨s * t, ?_⟩
      rw [map_mul, hs, ht]
      apply Subtype.ext
      rfl
    · intro B hB ihB hBinv
      obtain ⟨s, hs⟩ := ihB hB
      refine ⟨s⁻¹, ?_⟩
      rw [map_inv, hs]
      apply Subtype.ext
      rfl
  exact hP A.property

theorem fin4SimpleWeylActionHom_eq_of_matrix_eq
    (s t : fin4SimpleWeylSubgroup (F := F))
    (hst : steinbergToGL s.1 = steinbergToGL t.1) :
    fin4SimpleWeylActionHom s = fin4SimpleWeylActionHom t := by
  let ws := fin4WeylSubgroupChosenWord (fin4SimpleWeylToWeylWord s)
  let wt := fin4WeylSubgroupChosenWord (fin4SimpleWeylToWeylWord t)
  have hmatrix : signedMonomialMatrix ws.perm ws.scale =
      signedMonomialMatrix wt.perm wt.scale := by
    rw [← steinbergWeylWord_matrix ws, ← steinbergWeylWord_matrix wt,
      fin4WeylSubgroupChosenWord_eval, fin4WeylSubgroupChosenWord_eval]
    exact congrArg Units.val hst
  obtain ⟨hperm, hscale⟩ := signedMonomialMatrix_data_injective hmatrix
  exact SteinbergWeylWord.fin4MilnorAction_eq_of_perm_scale_eq
    ws wt hperm hscale

theorem fin4SimpleWeylActionHom_eq_of_fieldSigned_eq
    (s t : fin4SimpleWeylSubgroup (F := F))
    (hst : fin4SimpleWeylToFieldSigned s =
      fin4SimpleWeylToFieldSigned t) :
    fin4SimpleWeylActionHom s = fin4SimpleWeylActionHom t := by
  apply fin4SimpleWeylActionHom_eq_of_matrix_eq
  simpa [fin4SimpleWeylToFieldSigned] using congrArg Subtype.val hst

noncomputable def fieldSignedWeylChosenLift
    (A : fieldSignedWeylSubgroup (F := F)) :
    fin4SimpleWeylSubgroup (F := F) :=
  Classical.choose (fin4SimpleWeylToFieldSigned_surjective A)

theorem fin4SimpleWeylToFieldSigned_chosenLift
    (A : fieldSignedWeylSubgroup (F := F)) :
    fin4SimpleWeylToFieldSigned (fieldSignedWeylChosenLift A) = A :=
  Classical.choose_spec (fin4SimpleWeylToFieldSigned_surjective A)

noncomputable def fieldSignedWeylChosenWord
    (A : fieldSignedWeylSubgroup (F := F)) :
    SteinbergWeylWord F (Fin 4) :=
  fin4WeylSubgroupChosenWord
    (fin4SimpleWeylToWeylWord (fieldSignedWeylChosenLift A))

theorem fieldSignedWeylChosenWord_data
    (A : fieldSignedWeylSubgroup (F := F)) :
    (fieldSignedWeylChosenWord A).perm = fieldSignedPermutationHom A ∧
      (fieldSignedWeylChosenWord A).scale = (fieldSignedMonomialData A).2 := by
  apply signedMonomialMatrix_data_injective
  rw [← steinbergWeylWord_matrix (fieldSignedWeylChosenWord A),
    fieldSignedWeylChosenWord, fin4WeylSubgroupChosenWord_eval]
  have hchosen := congrArg Subtype.val
    (fin4SimpleWeylToFieldSigned_chosenLift A)
  have hmatrix :
      ((steinbergToGL (fieldSignedWeylChosenLift A).1 :
        (Matrix (Fin 4) (Fin 4) F)ˣ) : Matrix (Fin 4) (Fin 4) F) =
        (A.1 : Matrix (Fin 4) (Fin 4) F) := by
    exact congrArg Units.val hchosen
  have hmatrix' :
      ((steinbergToGL (fin4SimpleWeylToWeylWord
          (fieldSignedWeylChosenLift A)).1 :
        (Matrix (Fin 4) (Fin 4) F)ˣ) : Matrix (Fin 4) (Fin 4) F) =
        (A.1 : Matrix (Fin 4) (Fin 4) F) := hmatrix
  rw [hmatrix', fieldSignedMonomialData_matrix]
  rfl

/-- Milnor action descended to the exact field-valued `W₀` model. -/
noncomputable def fieldSignedWeylActionHom :
    fieldSignedWeylSubgroup (F := F) →* MulAut (MilnorDiagonalExtension F 4) where
  toFun A := fin4SimpleWeylActionHom (fieldSignedWeylChosenLift A)
  map_one' := by
    rw [← map_one (fin4SimpleWeylActionHom (F := F))]
    apply fin4SimpleWeylActionHom_eq_of_fieldSigned_eq
    rw [fin4SimpleWeylToFieldSigned_chosenLift, map_one]
  map_mul' A B := by
    rw [← map_mul]
    apply fin4SimpleWeylActionHom_eq_of_fieldSigned_eq
    rw [fin4SimpleWeylToFieldSigned_chosenLift, map_mul,
      fin4SimpleWeylToFieldSigned_chosenLift,
      fin4SimpleWeylToFieldSigned_chosenLift]

theorem fieldSignedWeylActionHom_centralIncl
    (A : fieldSignedWeylSubgroup (F := F))
    (z : Multiplicative (MilnorKDeg F 2)) :
    fieldSignedWeylActionHom A (centralIncl (F := F) (n := 4) z) =
      centralIncl z :=
  fin4SimpleWeylActionHom_centralIncl _ z

private theorem signed_ratio_eq_one_or_neg_one {a b : Fˣ}
    (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) :
    a * b⁻¹ = 1 ∨ a * b⁻¹ = -1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp

theorem fieldSignedWeylActionHom_generator
    (he : fin4MinusOneSymbol F = 0)
    (A : fieldSignedWeylSubgroup (F := F))
    {p q : Fin 4} (hpq : p ≠ q) :
    fieldSignedWeylActionHom A
        (fin4MatsumotoDiagonalLift hpq (-1 : Fˣ)) =
      fin4MatsumotoDiagonalLift
        ((fieldSignedPermutationHom A).injective.ne_iff.mpr hpq) (-1 : Fˣ) := by
  let word := fieldSignedWeylChosenWord A
  have hdata := fieldSignedWeylChosenWord_data A
  have hratio : word.scale p * (word.scale q)⁻¹ = 1 ∨
      word.scale p * (word.scale q)⁻¹ = -1 := by
    rw [hdata.2]
    exact signed_ratio_eq_one_or_neg_one
      (fieldSignedMonomialData_signs A p)
      (fieldSignedMonomialData_signs A q)
  have hsymbol :
      milnorSym2 F (word.scale p * (word.scale q)⁻¹) (-1 : Fˣ) = 0 := by
    rcases hratio with hr | hr
    · rw [hr, milnorSym2_one_left]
    · rw [hr]
      exact he
  change SteinbergWeylWord.fin4MilnorAction word
      (fin4MatsumotoDiagonalLift hpq (-1 : Fˣ)) = _
  rw [SteinbergWeylWord.fin4MilnorAction_matsumotoDiagonalLift,
    hsymbol, hdata.1]
  simp

theorem fieldSignedWeylActionHom_mem_H0
    (he : fin4MinusOneSymbol F = 0)
    (A : fieldSignedWeylSubgroup (F := F))
    (x : fin4MilnorH0 (F := F)) :
    fieldSignedWeylActionHom A x.1 ∈ fin4MilnorH0 (F := F) := by
  rcases x with ⟨x, hx⟩
  apply Subgroup.closure_induction
    (p := fun x _ => fieldSignedWeylActionHom A x ∈ fin4MilnorH0 (F := F))
    ?_ ?_ ?_ ?_ hx
  · rintro x ⟨p, q, hpq, rfl⟩
    rw [fieldSignedWeylActionHom_generator he]
    exact Subgroup.subset_closure ⟨_, _, _, rfl⟩
  · simp
  · intro x y _ _ hx hy
    rw [map_mul]
    exact (fin4MilnorH0 (F := F)).mul_mem hx hy
  · intro x _ hx
    rw [map_inv]
    exact (fin4MilnorH0 (F := F)).inv_mem hx

theorem fieldSignedWeylActionHom_generator_mem_H0
    (A : fieldSignedWeylSubgroup (F := F))
    {p q : Fin 4} (hpq : p ≠ q) :
    fieldSignedWeylActionHom A
        (fin4MatsumotoDiagonalLift hpq (-1 : Fˣ)) ∈
      fin4MilnorH0 (F := F) := by
  let word := fieldSignedWeylChosenWord A
  have hdata := fieldSignedWeylChosenWord_data A
  have hratio : word.scale p * (word.scale q)⁻¹ = 1 ∨
      word.scale p * (word.scale q)⁻¹ = -1 := by
    rw [hdata.2]
    exact signed_ratio_eq_one_or_neg_one
      (fieldSignedMonomialData_signs A p)
      (fieldSignedMonomialData_signs A q)
  change SteinbergWeylWord.fin4MilnorAction word
      (fin4MatsumotoDiagonalLift hpq (-1 : Fˣ)) ∈ _
  rw [SteinbergWeylWord.fin4MilnorAction_matsumotoDiagonalLift]
  apply (fin4MilnorH0 (F := F)).mul_mem
  · apply centralIncl_mem_H0_of_mem_zmultiples
    rcases hratio with hr | hr
    · rw [hr, milnorSym2_one_left]
      exact AddSubgroup.zero_mem _
    · rw [hr]
      exact fin4MinusOneSymbol_mem_zmultiples (F := F)
  · exact Subgroup.subset_closure ⟨_, _, _, rfl⟩

theorem fieldSignedWeylActionHom_mem_H0_general
    (A : fieldSignedWeylSubgroup (F := F))
    (x : fin4MilnorH0 (F := F)) :
    fieldSignedWeylActionHom A x.1 ∈ fin4MilnorH0 (F := F) := by
  rcases x with ⟨x, hx⟩
  apply Subgroup.closure_induction
    (p := fun x _ => fieldSignedWeylActionHom A x ∈ fin4MilnorH0 (F := F))
    ?_ ?_ ?_ ?_ hx
  · rintro x ⟨p, q, hpq, rfl⟩
    exact fieldSignedWeylActionHom_generator_mem_H0 A hpq
  · simp
  · intro x y _ _ hx hy
    rw [map_mul]
    exact (fin4MilnorH0 (F := F)).mul_mem hx hy
  · intro x _ hx
    rw [map_inv]
    exact (fin4MilnorH0 (F := F)).inv_mem hx

theorem fieldSignedWeyl_conj_diagonal
    (A : fieldSignedWeylSubgroup (F := F))
    (u : detOneDiagonalUnits F 4) :
    A.1 * detOneDiagonalMatrixUnitHom u * A.1⁻¹ =
      detOneDiagonalMatrixUnitHom
        (fin4PermuteDiagonal (F := F) (fieldSignedPermutationHom A) u) := by
  let σ := (fieldSignedMonomialData A).1
  let c := (fieldSignedMonomialData A).2
  have hA : (A.1 : Matrix (Fin 4) (Fin 4) F) =
      signedMonomialMatrix σ c := fieldSignedMonomialData_matrix A
  have hAinv := signedMonomialMatrix_inv_data_field A.1 σ c hA
  apply Units.ext
  simp only [Units.val_mul]
  rw [hA, detOneDiagonalMatrixUnitHom_matrix, hAinv,
    signedMonomialMatrix_mul, signedMonomialMatrix_mul,
    detOneDiagonalMatrixUnitHom_matrix]
  ext r s
  simp [σ, c, fieldSignedPermutationHom, signedMonomialMatrix,
    fin4PermuteDiagonal]

theorem fin4PermuteDiagonal_matsumotoDiagonal
    (pi : Equiv.Perm (Fin 4)) (p q : Fin 4) (u : Fˣ) :
    fin4PermuteDiagonal (F := F) pi (fin4MatsumotoDiagonal p q u) =
      fin4MatsumotoDiagonal (pi p) (pi q) u := by
  apply Subtype.ext
  funext r
  by_cases hrp : pi.symm r = p
  · have hrp' : r = pi p := by
      calc
        r = pi (pi.symm r) := (pi.apply_symm_apply r).symm
        _ = pi p := congrArg pi hrp
    subst r
    by_cases hpq : p = q
    · subst q
      simp [fin4PermuteDiagonal, fin4MatsumotoDiagonal]
    · have hpq' : pi p ≠ pi q := pi.injective.ne hpq
      simp [fin4PermuteDiagonal, fin4MatsumotoDiagonal, hpq, hpq']
  · by_cases hrq : pi.symm r = q
    · have hrq' : r = pi q := by
        calc
          r = pi (pi.symm r) := (pi.apply_symm_apply r).symm
          _ = pi q := congrArg pi hrq
      subst r
      by_cases hpq : p = q
      · subst q
        simp [fin4PermuteDiagonal, fin4MatsumotoDiagonal]
      · have hpq' : pi p ≠ pi q := pi.injective.ne hpq
        simp [fin4PermuteDiagonal, fin4MatsumotoDiagonal, hpq, hpq']
    · have hrp' : r ≠ pi p := by
        intro hr
        subst r
        simp at hrp
      have hrq' : r ≠ pi q := by
        intro hr
        subst r
        simp at hrq
      simp [fin4PermuteDiagonal, fin4MatsumotoDiagonal,
        hrp, hrq, hrp', hrq']

theorem fieldSignedWeyl_equivariant_generator
    (he : fin4MinusOneSymbol F = 0)
    (A : fieldSignedWeylSubgroup (F := F))
    {p q : Fin 4} (hpq : p ≠ q) :
    fin4MilnorH0ToFieldSignedWeyl
        ⟨fieldSignedWeylActionHom A
            (fin4MatsumotoDiagonalLift hpq (-1 : Fˣ)),
          fieldSignedWeylActionHom_mem_H0 he A
            ⟨fin4MatsumotoDiagonalLift hpq (-1 : Fˣ),
              Subgroup.subset_closure ⟨p, q, hpq, rfl⟩⟩⟩ =
      A * fin4MilnorH0ToFieldSignedWeyl
          ⟨fin4MatsumotoDiagonalLift hpq (-1 : Fˣ),
            Subgroup.subset_closure ⟨p, q, hpq, rfl⟩⟩ * A⁻¹ := by
  have haction := fieldSignedWeylActionHom_generator he A hpq
  have hdiag := congrArg MilnorDiagonalExtension.diag haction
  apply Subtype.ext
  change detOneDiagonalMatrixUnitHom
      (fieldSignedWeylActionHom A
        (fin4MatsumotoDiagonalLift hpq (-1 : Fˣ))).diag =
    A.1 * detOneDiagonalMatrixUnitHom
      (fin4MatsumotoDiagonal p q (-1 : Fˣ)) * A.1⁻¹
  rw [hdiag, fieldSignedWeyl_conj_diagonal,
    fin4PermuteDiagonal_matsumotoDiagonal]
  rfl

def fieldSignedWeylH0ActionHom
    (he : fin4MinusOneSymbol F = 0)
    (A : fieldSignedWeylSubgroup (F := F)) :
    fin4MilnorH0 (F := F) →* fin4MilnorH0 (F := F) :=
  ((fieldSignedWeylActionHom A).toMonoidHom.comp
      (fin4MilnorH0 (F := F)).subtype).codRestrict
    (fin4MilnorH0 (F := F))
    (fieldSignedWeylActionHom_mem_H0 he A)

theorem fieldSignedWeyl_equivariant
    (he : fin4MinusOneSymbol F = 0)
    (A : fieldSignedWeylSubgroup (F := F))
    (x : fin4MilnorH0 (F := F)) :
    fin4MilnorH0ToFieldSignedWeyl (fieldSignedWeylH0ActionHom he A x) =
      A * fin4MilnorH0ToFieldSignedWeyl x * A⁻¹ := by
  rcases x with ⟨x, hx⟩
  let P := fun y : MilnorDiagonalExtension F 4 =>
    ∀ hy : y ∈ fin4MilnorH0 (F := F),
      fin4MilnorH0ToFieldSignedWeyl
          (fieldSignedWeylH0ActionHom he A ⟨y, hy⟩) =
        A * fin4MilnorH0ToFieldSignedWeyl ⟨y, hy⟩ * A⁻¹
  have hP : P x := by
    apply Subgroup.closure_induction (p := fun y _ => P y)
      ?_ ?_ ?_ ?_ hx
    · rintro y ⟨p, q, hpq, rfl⟩ _
      exact fieldSignedWeyl_equivariant_generator he A hpq
    · intro hOne
      have hsub : (⟨1, hOne⟩ : fin4MilnorH0 (F := F)) = 1 := by
        apply Subtype.ext
        rfl
      rw [hsub]
      simp
    · intro y z hy hz ihy ihz hyz
      let ky : fin4MilnorH0 (F := F) := ⟨y, hy⟩
      let kz : fin4MilnorH0 (F := F) := ⟨z, hz⟩
      have ey := ihy hy
      have ez := ihz hz
      have hsub : (⟨y * z, hyz⟩ : fin4MilnorH0 (F := F)) =
          ky * kz := by
        apply Subtype.ext
        rfl
      change fin4MilnorH0ToFieldSignedWeyl
          (fieldSignedWeylH0ActionHom he A ⟨y * z, hyz⟩) =
        A * fin4MilnorH0ToFieldSignedWeyl ⟨y * z, hyz⟩ * A⁻¹
      rw [hsub, map_mul, map_mul, ey, ez]
      group
      simp [ky, kz, mul_assoc]
    · intro y hy ihy hyinv
      let ky : fin4MilnorH0 (F := F) := ⟨y, hy⟩
      have ey := ihy hy
      have hsub : (⟨y⁻¹, hyinv⟩ : fin4MilnorH0 (F := F)) =
          ky⁻¹ := by
        apply Subtype.ext
        rfl
      change fin4MilnorH0ToFieldSignedWeyl
          (fieldSignedWeylH0ActionHom he A ⟨y⁻¹, hyinv⟩) =
        A * fin4MilnorH0ToFieldSignedWeyl ⟨y⁻¹, hyinv⟩ * A⁻¹
      have hmap := map_inv (fin4MilnorH0ToFieldSignedWeyl (F := F)) ky
      rw [hsub, map_inv, map_inv, ey, hmap]
      simp [ky]
      group
  exact hP hx

theorem fin4MilnorAction_eq_diagonalAction
    (word : SteinbergWeylWord F (Fin 4)) (hperm : word.perm = 1) :
    SteinbergWeylWord.fin4MilnorAction word =
      fin4DiagonalAction (F := F) word.scale := by
  apply mulEquiv_eq_of_centralIncl_and_matsumotoDiagonalLift
  · intro z
    rw [SteinbergWeylWord.fin4MilnorAction_centralIncl]
    apply MilnorDiagonalExtension.ext
    · rfl
    · simp [fin4DiagonalAction]
  · intro p q hpq u
    rw [SteinbergWeylWord.fin4MilnorAction_matsumotoDiagonalLift,
      fin4DiagonalAction_matsumotoDiagonalLift, hperm]
    rfl

theorem fieldSignedWeylActionHom_common
    (x : fin4MilnorH0 (F := F)) (g : MilnorDiagonalExtension F 4) :
    fieldSignedWeylActionHom (fin4MilnorH0ToFieldSignedWeyl x) g =
      x.1 * g * x.1⁻¹ := by
  let A := fin4MilnorH0ToFieldSignedWeyl x
  let word := fieldSignedWeylChosenWord A
  have hwordData := fieldSignedWeylChosenWord_data A
  have hmatrix : (A.1 : Matrix (Fin 4) (Fin 4) F) =
      signedMonomialMatrix 1 x.1.diag.1 := by
    change (detOneDiagonalMatrixUnitHom x.1.diag :
      Matrix (Fin 4) (Fin 4) F) = _
    exact detOneDiagonalMatrixUnitHom_matrix x.1.diag
  have hdata := fieldSignedMonomialData_eq hmatrix
  have hperm : word.perm = 1 := hwordData.1.trans hdata.1
  have hscale : word.scale = x.1.diag.1 := hwordData.2.trans hdata.2
  change SteinbergWeylWord.fin4MilnorAction word g = _
  rw [fin4MilnorAction_eq_diagonalAction word hperm, hscale]
  exact fin4DiagonalAction_eq_conj x.1.diag x.1 g rfl

theorem fieldSignedWeylCompatible
    (he : fin4MinusOneSymbol F = 0) :
    AmalgamatedSemidirect.Compatible
      (fin4MilnorH0 (F := F))
      (fin4MilnorH0ToFieldSignedWeyl (F := F))
      (fieldSignedWeylActionHom (F := F)) where
  injective := fin4MilnorH0ToFieldSignedWeyl_injective he
  stable := fieldSignedWeylActionHom_mem_H0 he
  equivariant := by
    intro A x
    simpa [fieldSignedWeylH0ActionHom] using
      fieldSignedWeyl_equivariant he A x
  common_action := fieldSignedWeylActionHom_common

/-- Milnor's group `W` in the zero-symbol branch. -/
abbrev MilnorWZero (he : fin4MinusOneSymbol F = 0) :=
  AmalgamatedSemidirect.Construction
    (fin4MilnorH0 (F := F))
    (fin4MilnorH0ToFieldSignedWeyl (F := F))
    (fieldSignedWeylActionHom (F := F))
    (fieldSignedWeylCompatible he)

def milnorWZeroCentralIncl (he : fin4MinusOneSymbol F = 0) :
    Multiplicative (MilnorKDeg F 2) →* MilnorWZero he :=
  (AmalgamatedSemidirect.inl
    (fin4MilnorH0 (F := F))
    (fin4MilnorH0ToFieldSignedWeyl (F := F))
    (fieldSignedWeylActionHom (F := F))
    (fieldSignedWeylCompatible he)).comp centralIncl

theorem milnorWZeroCentralIncl_injective
    (he : fin4MinusOneSymbol F = 0) :
    Function.Injective (milnorWZeroCentralIncl he) :=
  (AmalgamatedSemidirect.inl_injective
    (fin4MilnorH0 (F := F))
    (fin4MilnorH0ToFieldSignedWeyl (F := F))
    (fieldSignedWeylActionHom (F := F))
    (fieldSignedWeylCompatible he)).comp centralIncl_injective

theorem milnorWZeroCentralIncl_mem_center
    (he : fin4MinusOneSymbol F = 0)
    (z : Multiplicative (MilnorKDeg F 2)) :
    milnorWZeroCentralIncl he z ∈ Subgroup.center (MilnorWZero he) := by
  exact AmalgamatedSemidirect.inl_mem_center
    (fin4MilnorH0 (F := F))
    (fin4MilnorH0ToFieldSignedWeyl (F := F))
    (fieldSignedWeylActionHom (F := F))
    (fieldSignedWeylCompatible he)
    (centralIncl z) (centralIncl_mem_center z)
    (fun A => fieldSignedWeylActionHom_centralIncl A z)

end MilnorDiagonalExtension
end GaloisForLFunctions.HTGeometry

end
