import GaloisForLFunctions.HTGeometry.MilnorKTwoFieldWeylAction
import GaloisForLFunctions.HTGeometry.MilnorKTwoSpinWeylCommon


/-!
# Spin Weyl action and Milnor's nonzero-symbol quotient

Real signed-monomial matrices of Spin Weyl rotors are transported to every source field.
The descended Milnor action preserves `H₀`; its `{-1,-1}` cocycle agrees exactly with
Clifford conjugation's central sign. This gives the compatible nonzero-symbol amalgamation
and a central injective copy of Milnor `K₂` in the resulting group `W`.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry
namespace MilnorSpinWeyl

open MilnorDiagonalExtension

variable {F : Type*} [Field F]

local instance milnorKTwoSpinWeylFieldActionLocalInst1 : DecidableEq F := Classical.decEq F

/-- A signed-monomial matrix as an explicit matrix unit. -/
def signedMonomialMatrixUnit (sigma : Equiv.Perm (Fin 4))
    (c : Fin 4 → Fˣ) : (Matrix (Fin 4) (Fin 4) F)ˣ where
  val := signedMonomialMatrix sigma c
  inv := signedMonomialMatrix sigma.symm (fun p => (c (sigma.symm p))⁻¹)
  val_inv := by
    rw [signedMonomialMatrix_mul]
    ext r s
    simp [signedMonomialMatrix, Matrix.one_apply]
  inv_val := by
    rw [signedMonomialMatrix_mul]
    ext r s
    simp [signedMonomialMatrix, Matrix.one_apply]

@[simp] theorem signedMonomialMatrixUnit_val
    (sigma : Equiv.Perm (Fin 4)) (c : Fin 4 → Fˣ) :
    (signedMonomialMatrixUnit sigma c : Matrix (Fin 4) (Fin 4) F) =
      signedMonomialMatrix sigma c := rfl

/-- Reinterpret a real sign as a sign in the source field. -/
def realSignToField (u : ℝˣ) : Fˣ :=
  signUnit (F := F) (signBit (F := ℝ) u)

theorem realSignToField_eq_of_sign {u : ℝˣ}
    (hu : u = 1 ∨ u = -1) :
    realSignToField (F := F) u = if u = 1 then 1 else -1 := by
  rcases hu with rfl | rfl
  · simp [realSignToField, signBit]
  · norm_num [realSignToField, signBit]

theorem realSignToField_mul {u v : ℝˣ}
    (hu : u = 1 ∨ u = -1) (hv : v = 1 ∨ v = -1) :
    realSignToField (F := F) (u * v) =
      realSignToField u * realSignToField v := by
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;>
    norm_num [realSignToField, signBit]

theorem realSignToField_inv {u : ℝˣ}
    (hu : u = 1 ∨ u = -1) :
    realSignToField (F := F) u⁻¹ = (realSignToField u)⁻¹ := by
  rcases hu with rfl | rfl <;> norm_num [realSignToField, signBit]

/-- Base-change signed real rotor matrices to signed matrices over `F`. -/
noncomputable def generatedSignedMonomialToFieldMatrix :
    generatedSignedMonomialSubgroup →* (Matrix (Fin 4) (Fin 4) F)ˣ where
  toFun A := signedMonomialMatrixUnit (signedMonomialData A).1
    (fun p => realSignToField (F := F) ((signedMonomialData A).2 p))
  map_one' := by
    have hdata := signedMonomialData_eq
      (A := (1 : generatedSignedMonomialSubgroup))
      (σ := 1) (c := fun _ => 1) (by
        simp [signedMonomialMatrix_one])
    apply Units.ext
    rw [signedMonomialMatrixUnit_val, hdata.1, hdata.2]
    ext r s
    simp [realSignToField, signBit, signedMonomialMatrix, Matrix.one_apply]
  map_mul' A B := by
    let c := (signedMonomialData A).2
    let d := (signedMonomialData B).2
    have hAB : ((((A * B).1 :
        (Matrix (Fin 4) (Fin 4) ℝ)ˣ) : Matrix (Fin 4) (Fin 4) ℝ)) =
        signedMonomialMatrix
          ((signedMonomialData A).1 * (signedMonomialData B).1)
          (fun p => c ((signedMonomialData B).1 p) * d p) := by
      change (A.1 : Matrix (Fin 4) (Fin 4) ℝ) *
        (B.1 : Matrix (Fin 4) (Fin 4) ℝ) = _
      rw [signedMonomialData_matrix A, signedMonomialData_matrix B,
        signedMonomialMatrix_mul]
      rfl
    have hdata := signedMonomialData_eq hAB
    apply Units.ext
    simp only [signedMonomialMatrixUnit_val, Units.val_mul]
    rw [hdata.1, hdata.2, signedMonomialMatrix_mul]
    congr 2
    funext p
    exact realSignToField_mul
      (signedMonomialData_signs A ((signedMonomialData B).1 p))
      (signedMonomialData_signs B p)

theorem generatedSignedMonomialToFieldMatrix_generator
    (i j : Fin 4) (hij : i ≠ j) :
    generatedSignedMonomialToFieldMatrix (F := F)
        ⟨spinWeylMatrixGenerator i j hij,
          Subgroup.subset_closure ⟨i, j, hij, rfl⟩⟩ =
      fieldWeylMatrixGenerator (F := F) i j hij := by
  have hdata := signedMonomialData_eq
    (A := ⟨spinWeylMatrixGenerator i j hij,
      Subgroup.subset_closure ⟨i, j, hij, rfl⟩⟩)
    (spinWeylMatrixGenerator_signedMonomial i j hij)
  change signedMonomialMatrixUnit
      (signedMonomialData ⟨spinWeylMatrixGenerator i j hij,
        Subgroup.subset_closure ⟨i, j, hij, rfl⟩⟩).1
      (fun p => realSignToField (F := F)
        ((signedMonomialData ⟨spinWeylMatrixGenerator i j hij,
          Subgroup.subset_closure ⟨i, j, hij, rfl⟩⟩).2 p)) = _
  apply Units.ext
  rw [signedMonomialMatrixUnit_val, hdata.1, hdata.2,
    fieldWeylMatrixGenerator_val,
    weylMatrix_eq_signedMonomial hij (1 : Fˣ)]
  congr 2
  funext p
  by_cases hpi : p = i
  · subst p
    simp [realSignToField, signBit, steinbergWeylRootScale]
  · by_cases hpj : p = j
    · subst p
      norm_num [realSignToField, signBit, steinbergWeylRootScale, hpi]
    · simp [realSignToField, signBit, steinbergWeylRootScale,
        hpi, hpj]

theorem generatedSignedMonomialToFieldMatrix_mem
    (A : generatedSignedMonomialSubgroup) :
    generatedSignedMonomialToFieldMatrix (F := F) A ∈
      fieldSignedWeylSubgroup := by
  rcases A with ⟨A, hA⟩
  induction hA using Subgroup.closure_induction with
  | mem A hA =>
      obtain ⟨i, j, hij, rfl⟩ := hA
      rw [generatedSignedMonomialToFieldMatrix_generator]
      exact Subgroup.subset_closure ⟨i, j, hij, rfl⟩
  | one =>
      have hsub : (⟨1, generatedSignedMonomialSubgroup.one_mem⟩ :
          generatedSignedMonomialSubgroup) = 1 := by
        apply Subtype.ext
        rfl
      rw [hsub, map_one]
      exact fieldSignedWeylSubgroup.one_mem
  | mul A B hAmem hBmem hA hB =>
      let a : generatedSignedMonomialSubgroup := ⟨A, hAmem⟩
      let b : generatedSignedMonomialSubgroup := ⟨B, hBmem⟩
      have hsub : (⟨A * B, generatedSignedMonomialSubgroup.mul_mem hAmem hBmem⟩ :
          generatedSignedMonomialSubgroup) = a * b := by
        apply Subtype.ext
        rfl
      rw [hsub, map_mul]
      exact fieldSignedWeylSubgroup.mul_mem hA hB
  | inv A hAmem hA =>
      let a : generatedSignedMonomialSubgroup := ⟨A, hAmem⟩
      have hsub : (⟨A⁻¹, generatedSignedMonomialSubgroup.inv_mem hAmem⟩ :
          generatedSignedMonomialSubgroup) = a⁻¹ := by
        apply Subtype.ext
        rfl
      rw [hsub, map_inv]
      exact fieldSignedWeylSubgroup.inv_mem hA

def generatedSignedMonomialToFieldSigned :
    generatedSignedMonomialSubgroup →* fieldSignedWeylSubgroup (F := F) :=
  (generatedSignedMonomialToFieldMatrix (F := F)).codRestrict
    (fieldSignedWeylSubgroup (F := F))
    generatedSignedMonomialToFieldMatrix_mem

/-- Field signed-matrix quotient of the Spin Weyl group. -/
def spinWeylToFieldSigned :
    spinWeylSubgroup →* fieldSignedWeylSubgroup (F := F) :=
  (generatedSignedMonomialToFieldSigned (F := F)).comp
    spinWeylMatrixRepresentation

def fieldWeylGeneratorSigned (i j : Fin 4) (hij : i ≠ j) :
    fieldSignedWeylSubgroup (F := F) :=
  ⟨fieldWeylMatrixGenerator (F := F) i j hij,
    Subgroup.subset_closure ⟨i, j, hij, rfl⟩⟩

theorem spinWeylToFieldSigned_weylLift
    (i j : Fin 4) (hij : i ≠ j) :
    spinWeylToFieldSigned (F := F) (weylLiftSpinWeyl i j hij) =
      fieldWeylGeneratorSigned (F := F) i j hij := by
  apply Subtype.ext
  exact generatedSignedMonomialToFieldMatrix_generator (F := F) i j hij

theorem fin4SimpleWeylActionHom_generator
    (i j : Fin 4) (hij : i ≠ j) :
    fin4SimpleWeylActionHom
        ⟨steinbergWeyl hij (1 : Fˣ),
          Subgroup.subset_closure ⟨i, j, hij, rfl⟩⟩ =
      fin4WeylGeneratorAction (F := F) hij 1 := by
  change SteinbergWeylWord.fin4MilnorAction
      (fin4WeylSubgroupChosenWord
        (fin4SimpleWeylToWeylWord
          ⟨steinbergWeyl hij (1 : Fˣ),
            Subgroup.subset_closure ⟨i, j, hij, rfl⟩⟩)) = _
  change SteinbergWeylWord.fin4MilnorAction _ =
      SteinbergWeylWord.fin4MilnorAction
        (.snoc .one i j hij (1 : Fˣ))
  apply SteinbergWeylWord.fin4MilnorAction_eq_of_eval_eq
  rw [fin4WeylSubgroupChosenWord_eval]
  rfl

theorem fieldSignedWeylActionHom_matrixGenerator
    (i j : Fin 4) (hij : i ≠ j) :
    fieldSignedWeylActionHom (F := F)
        (fieldWeylGeneratorSigned (F := F) i j hij) =
      fin4WeylGeneratorAction (F := F) hij 1 := by
  let s : fin4SimpleWeylSubgroup (F := F) :=
    ⟨steinbergWeyl hij (1 : Fˣ),
      Subgroup.subset_closure ⟨i, j, hij, rfl⟩⟩
  have hs : fin4SimpleWeylToFieldSigned s =
      fieldWeylGeneratorSigned (F := F) i j hij := rfl
  change fin4SimpleWeylActionHom
      (fieldSignedWeylChosenLift
        (fieldWeylGeneratorSigned (F := F) i j hij)) = _
  rw [← fin4SimpleWeylActionHom_generator (F := F) i j hij]
  apply fin4SimpleWeylActionHom_eq_of_fieldSigned_eq
  rw [fin4SimpleWeylToFieldSigned_chosenLift, hs]

theorem fieldSignedPermutationHom_spinWeylToFieldSigned
    (s : spinWeylSubgroup) :
    fieldSignedPermutationHom (spinWeylToFieldSigned (F := F) s) =
      spinWeylPermutationHom s := by
  let A := spinWeylMatrixRepresentation s
  have hmatrix :
      (((spinWeylToFieldSigned (F := F) s).1 :
        (Matrix (Fin 4) (Fin 4) F)ˣ) : Matrix (Fin 4) (Fin 4) F) =
      signedMonomialMatrix (signedMonomialData A).1
        (fun p => realSignToField (F := F) ((signedMonomialData A).2 p)) := rfl
  have hdata := fieldSignedMonomialData_eq hmatrix
  exact hdata.1

/-- Spin Weyl action on Milnor's diagonal extension, factored through signed matrices. -/
noncomputable def spinWeylActionHom :
    spinWeylSubgroup →* MulAut (MilnorDiagonalExtension F 4) :=
  (fieldSignedWeylActionHom (F := F)).comp
    (spinWeylToFieldSigned (F := F))

theorem spinWeylActionHom_mem_H0
    (s : spinWeylSubgroup) (x : fin4MilnorH0 (F := F)) :
    spinWeylActionHom (F := F) s x.1 ∈ fin4MilnorH0 (F := F) :=
  fieldSignedWeylActionHom_mem_H0_general _ x

def spinWeylH0ActionHom (s : spinWeylSubgroup) :
    fin4MilnorH0 (F := F) →* fin4MilnorH0 (F := F) :=
  ((spinWeylActionHom (F := F) s).toMonoidHom.comp
      (fin4MilnorH0 (F := F)).subtype).codRestrict
    (fin4MilnorH0 (F := F))
    (spinWeylActionHom_mem_H0 (F := F) s)

theorem spinWeylH0ActionHom_one (x : fin4MilnorH0 (F := F)) :
    spinWeylH0ActionHom (F := F) 1 x = x := by
  apply Subtype.ext
  change spinWeylActionHom (F := F) 1 x.1 = x.1
  rw [map_one]
  rfl

theorem spinWeylH0ActionHom_mul
    (s t : spinWeylSubgroup) (x : fin4MilnorH0 (F := F)) :
    spinWeylH0ActionHom (F := F) (s * t) x =
      spinWeylH0ActionHom (F := F) s
        (spinWeylH0ActionHom (F := F) t x) := by
  apply Subtype.ext
  change spinWeylActionHom (F := F) (s * t) x.1 =
    spinWeylActionHom (F := F) s (spinWeylActionHom (F := F) t x.1)
  rw [map_mul]
  rfl

theorem spinWeylH0ActionHom_mul_inv
    (s : spinWeylSubgroup) (x : fin4MilnorH0 (F := F)) :
    spinWeylH0ActionHom (F := F) s
        (spinWeylH0ActionHom (F := F) s⁻¹ x) = x := by
  rw [← spinWeylH0ActionHom_mul]
  simp [spinWeylH0ActionHom_one]

theorem spinWeylActionHom_weylLift
    (i j : Fin 4) (hij : i ≠ j) :
    spinWeylActionHom (F := F) (weylLiftSpinWeyl i j hij) =
      fin4WeylGeneratorAction (F := F) hij 1 := by
  change fieldSignedWeylActionHom (F := F)
      (spinWeylToFieldSigned (F := F) (weylLiftSpinWeyl i j hij)) = _
  rw [spinWeylToFieldSigned_weylLift]
  exact fieldSignedWeylActionHom_matrixGenerator i j hij

theorem spinWeylActionHom_centralIncl
    (s : spinWeylSubgroup)
    (z : Multiplicative (MilnorKDeg F 2)) :
    spinWeylActionHom (F := F) s (centralIncl (F := F) (n := 4) z) =
      centralIncl z :=
  fieldSignedWeylActionHom_centralIncl _ z

private theorem zmodTwo_eq_zero_or_one_local (a : ZMod 2) :
    a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem spinWeylMatrixRepresentation_coordinates
    (c : MilnorH0Coordinates.Coordinates) :
    spinWeylMatrixRepresentation (coordinatesSpinWeylHom c) =
      spinWeylMatrixRepresentation
        (coordinatesSpinWeylHom ⟨c.diag, 0⟩) := by
  rw [coordinatesSpinWeylHom_eq, coordinatesSpinWeylHom_eq,
    map_mul, map_mul, map_mul, map_mul, map_mul, map_mul]
  rcases zmodTwo_eq_zero_or_one_local c.central with hc | hc
  · simp [hc]
  · simp [hc, spinWeylMatrixRepresentation_centralNegOne]

theorem realSignToField_signUnit (a : ZMod 2) :
    realSignToField (F := F) (signUnit (F := ℝ) a) =
      signUnit (F := F) a := by
  rcases zmodTwo_eq_zero_or_one_local a with rfl | rfl <;>
    norm_num [realSignToField, signBit]

theorem spinWeylToFieldSigned_fin4MilnorH0
    (he : fin4MinusOneSymbol F ≠ 0)
    (x : fin4MilnorH0 (F := F)) :
    spinWeylToFieldSigned (F := F) (fin4MilnorH0ToSpinWeyl he x) =
      fin4MilnorH0ToFieldSignedWeyl x := by
  let a : Fin 3 → ZMod 2 := fin4MilnorH0Bits x
  let uR : detOneDiagonalUnits ℝ 4 := coordinatesDiagonal a
  let uF : detOneDiagonalUnits F 4 := coordinatesDiagonal a
  have huF : uF = x.1.diag := by
    apply detOneDiagonalUnits_fin4_ext
    · exact signUnit_signBit (fin4MilnorH0_signs x 0)
    · exact signUnit_signBit (fin4MilnorH0_signs x 1)
    · exact signUnit_signBit (fin4MilnorH0_signs x 2)
  have huRsign : ∀ p, uR.1 p = 1 ∨ uR.1 p = -1 := by
    intro p
    dsimp [uR, coordinatesDiagonal]
    fin_cases p <;> exact signUnit_eq_one_or_neg_one _
  have huRdet : Matrix.det (signedMonomialMatrix 1 uR.1) = 1 := by
    rw [det_signedMonomialMatrix_one]
    exact congrArg Units.val uR.property
  have hspin : spinWeylMatrixRepresentation
      (fin4MilnorH0ToSpinWeyl he x) = generatedDiagonalSignLift uR.1 := by
    change spinWeylMatrixRepresentation
      (coordinatesSpinWeylHom (fin4MilnorH0ToCoordinates he x)) = _
    rw [spinWeylMatrixRepresentation_coordinates,
      spinWeylMatrixRepresentation_coordinatesDiagonal]
    rfl
  have hrealMatrix :
      (((spinWeylMatrixRepresentation (fin4MilnorH0ToSpinWeyl he x)).1 :
        (Matrix (Fin 4) (Fin 4) ℝ)ˣ) : Matrix (Fin 4) (Fin 4) ℝ) =
        signedMonomialMatrix 1 uR.1 := by
    rw [hspin]
    exact generatedDiagonalSignLift_val uR.1 huRsign huRdet
  have hrealData := signedMonomialData_eq hrealMatrix
  apply Subtype.ext
  apply Units.ext
  change signedMonomialMatrix
      (signedMonomialData
        (spinWeylMatrixRepresentation (fin4MilnorH0ToSpinWeyl he x))).1
      (fun p => realSignToField (F := F)
        ((signedMonomialData
          (spinWeylMatrixRepresentation (fin4MilnorH0ToSpinWeyl he x))).2 p)) =
    (detOneDiagonalMatrixUnitHom x.1.diag : Matrix (Fin 4) (Fin 4) F)
  rw [hrealData.1, hrealData.2, ← huF,
    detOneDiagonalMatrixUnitHom_matrix]
  congr 2
  funext p
  dsimp [uR, uF, coordinatesDiagonal]
  fin_cases p <;> exact realSignToField_signUnit _

def pairFlipSpinWeyl (p q : Fin 4) (hpq : p ≠ q) : spinWeylSubgroup :=
  (weylLiftSpinWeyl p q hpq)⁻¹ ^ 2

@[simp] theorem pairFlipSpinWeyl_val
    (p q : Fin 4) (hpq : p ≠ q) :
    ((pairFlipSpinWeyl p q hpq).1 : Clifford) = bivector p q := by
  exact weylLift_inv_sq_val p q hpq

theorem spinVectorLinearEquiv_basis_signedData
    (s : spinWeylSubgroup) (p : Fin 4) :
    spinVectorLinearEquiv s.1 (basisVector p) =
      (((signedMonomialData (spinWeylMatrixRepresentation s)).2 p : ℝ) •
        basisVector ((signedMonomialData (spinWeylMatrixRepresentation s)).1 p)) := by
  apply vectorBasis.repr.injective
  apply Finsupp.ext
  intro r
  have hm := congrFun (congrFun
    (signedMonomialData_matrix (spinWeylMatrixRepresentation s)) r) p
  change spinVectorMatrixRepresentation s.1 r p = _ at hm
  rw [spinVectorMatrixRepresentation_apply, LinearMap.toMatrix_apply] at hm
  rw [show vectorBasis p = basisVector p by
    exact Pi.basisFun_apply ℝ (Fin 4) p] at hm
  by_cases hr : r = (signedMonomialData (spinWeylMatrixRepresentation s)).1 p
  · simp [basisVector, vectorBasis, signedMonomialMatrix, hr] at hm ⊢
    exact hm
  · simp [basisVector, vectorBasis, signedMonomialMatrix, hr] at hm ⊢
    exact hm

theorem spinWeyl_conj_basis_signedData
    (s : spinWeylSubgroup) (p : Fin 4) :
    (s.1 : Clifford) * basisClifford p * ((s⁻¹).1 : Clifford) =
      (((signedMonomialData (spinWeylMatrixRepresentation s)).2 p : ℝ) •
        basisClifford ((signedMonomialData (spinWeylMatrixRepresentation s)).1 p)) := by
  have h := spinCliffordIota_spinVectorLinearEquiv s.1 (basisVector p)
  rw [spinVectorLinearEquiv_basis_signedData] at h
  simpa [spinConjugation, basisClifford,
    @ConjAct.units_smul_def, @ConjAct.ofConjAct_toConjAct] using h.symm

set_option maxHeartbeats 800000 in
theorem spinWeyl_conj_weylLift_signedData
    (s : spinWeylSubgroup) (p q : Fin 4) (hpq : p ≠ q) :
    let A := spinWeylMatrixRepresentation s
    let σ := (signedMonomialData A).1
    let c := (signedMonomialData A).2
    let ratio := c p * (c q)⁻¹
    s * weylLiftSpinWeyl p q hpq * s⁻¹ =
      (if ratio = 1 then 1 else
        pairFlipSpinWeyl (σ p) (σ q) (σ.injective.ne hpq)) *
      weylLiftSpinWeyl (σ p) (σ q) (σ.injective.ne hpq) := by
  dsimp only
  let A := spinWeylMatrixRepresentation s
  let σ := (signedMonomialData A).1
  let c := (signedMonomialData A).2
  have hcp := signedMonomialData_signs A p
  have hcq := signedMonomialData_signs A q
  change c p = 1 ∨ c p = -1 at hcp
  change c q = 1 ∨ c q = -1 at hcq
  have hb : spinConjugation s.1 (bivector p q) =
      ((c p : ℝ) * (c q : ℝ)) • bivector (σ p) (σ q) := by
    rw [bivector, map_mul]
    rw [show spinConjugation s.1 (basisClifford p) =
        (c p : ℝ) • basisClifford (σ p) by
          simpa [A, σ, c, spinConjugation,
            @ConjAct.units_smul_def, @ConjAct.ofConjAct_toConjAct] using
            spinWeyl_conj_basis_signedData s p,
      show spinConjugation s.1 (basisClifford q) =
        (c q : ℝ) • basisClifford (σ q) by
          simpa [A, σ, c, spinConjugation,
            @ConjAct.units_smul_def, @ConjAct.ofConjAct_toConjAct] using
            spinWeyl_conj_basis_signedData s q]
    rw [smul_mul_smul]
    rfl
  apply Subtype.ext
  apply Subtype.ext
  change spinConjugation s.1 (weylLiftVal p q) =
    (((if c p * (c q)⁻¹ = 1 then 1 else
        pairFlipSpinWeyl (σ p) (σ q) (σ.injective.ne hpq)) :
          spinWeylSubgroup).1 : Clifford) * weylLiftVal (σ p) (σ q)
  rw [weylLiftVal_formula, map_smul, map_sub, hb, map_one]
  rcases hcp with hcp | hcp <;> rcases hcq with hcq | hcq
  · rw [hcp, hcq]
    norm_num
    rw [weylLiftVal_formula]
    simp [div_eq_mul_inv]
  · rw [hcp, hcq]
    norm_num [pairFlipSpinWeyl_val]
    rw [weylLiftVal_formula, mul_smul_comm, mul_sub]
    rw [bivector_sq (σ p) (σ q) (σ.injective.ne hpq)]
    simp only [mul_one, div_eq_mul_inv, one_mul]
    congr 1
    abel
  · rw [hcp, hcq]
    norm_num [pairFlipSpinWeyl_val]
    rw [weylLiftVal_formula, mul_smul_comm, mul_sub]
    rw [bivector_sq (σ p) (σ q) (σ.injective.ne hpq)]
    simp only [mul_one, div_eq_mul_inv, one_mul]
    congr 1
    abel
  · rw [hcp, hcq]
    norm_num
    rw [weylLiftVal_formula]
    simp [div_eq_mul_inv]

theorem fieldSignedMonomialData_spinWeylToFieldSigned_scale
    (s : spinWeylSubgroup) :
    (fieldSignedMonomialData (spinWeylToFieldSigned (F := F) s)).2 =
      fun p => realSignToField (F := F)
        ((signedMonomialData (spinWeylMatrixRepresentation s)).2 p) := by
  let A := spinWeylMatrixRepresentation s
  have hmatrix :
      (((spinWeylToFieldSigned (F := F) s).1 :
        (Matrix (Fin 4) (Fin 4) F)ˣ) : Matrix (Fin 4) (Fin 4) F) =
      signedMonomialMatrix (signedMonomialData A).1
        (fun p => realSignToField (F := F) ((signedMonomialData A).2 p)) := rfl
  exact (fieldSignedMonomialData_eq hmatrix).2

def pairFlipCoordinates (p q : Fin 4) : MilnorH0Coordinates.Coordinates :=
  ⟨fun i => if i.castSucc = p ∨ i.castSucc = q then 1 else 0,
    if p < q then 0 else 1⟩

theorem fin4MilnorH0ToCoordinates_generator
    (he : fin4MinusOneSymbol F ≠ 0)
    {p q : Fin 4} (hpq : p ≠ q) :
    fin4MilnorH0ToCoordinates he
        ⟨fin4MatsumotoDiagonalLift hpq (-1 : Fˣ),
          Subgroup.subset_closure ⟨p, q, hpq, rfl⟩⟩ =
      pairFlipCoordinates p q := by
  letI : CharZero F := charZero_of_fin4MinusOneSymbol_ne_zero he
  have hminus : (-1 : Fˣ) ≠ 1 := by
    intro h
    have hv : (-1 : F) = 1 := congrArg Units.val h
    norm_num at hv
  apply MilnorH0Coordinates.Coordinates.ext
  · funext i
    fin_cases p <;> fin_cases q <;> fin_cases i <;>
      simp_all [fin4MilnorH0ToCoordinates, fin4MilnorH0Bits,
        fullSignBits, signBit, fin4MatsumotoDiagonalLift,
        fin4MatsumotoDiagonal, pairFlipCoordinates]
    all_goals exact (hpq rfl).elim
  · apply (fin4MinusOneCenterEquiv he).injective
    apply Subtype.ext
    change (fin4MinusOneCenterEquiv he
      (fin4MilnorH0CentralParity he
        ⟨fin4MatsumotoDiagonalLift hpq (-1 : Fˣ),
          Subgroup.subset_closure ⟨p, q, hpq, rfl⟩⟩)).1 =
      (fin4MinusOneCenterEquiv he (if p < q then 0 else 1)).1
    rw [fin4MinusOneCenterEquiv_h0CentralParity]
    have hzero : (fin4MinusOneCenterEquiv he 0).1 = 0 := by simp
    have hone : (fin4MinusOneCenterEquiv he 1).1 =
        fin4MinusOneSymbol F := by
      have h := congrArg Subtype.val
        (fin4MinusOneCenterEquiv_apply_intCast he 1)
      simpa using h
    fin_cases p <;> fin_cases q <;>
      simp_all [fin4MatsumotoDiagonalLift, fin4MinusOneSymbol]

theorem bivector_terminal_mul_terminal
    (p q : Fin 3) :
    bivector p.castSucc 3 * bivector q.castSucc 3 =
      bivector p.castSucc q.castSucc := by
  calc
    bivector p.castSucc 3 * bivector q.castSucc 3 =
        basisClifford p.castSucc *
          (basisClifford 3 * basisClifford q.castSucc) * basisClifford 3 := by
      simp [bivector, mul_assoc]
    _ = basisClifford p.castSucc *
          (-(basisClifford q.castSucc * basisClifford 3)) * basisClifford 3 := by
      rw [basisClifford_anti 3 q.castSucc
        (Ne.symm (Fin.castSucc_ne_last q))]
    _ = bivector p.castSucc q.castSucc := by
      rw [show basisClifford p.castSucc *
          (-(basisClifford q.castSucc * basisClifford 3)) * basisClifford 3 =
          -(basisClifford p.castSucc * basisClifford q.castSucc) *
            (basisClifford 3 * basisClifford 3) by noncomm_ring,
        basisClifford_sq]
      simp [bivector]

theorem coordinatesSpin_pairFlipCoordinates
    {p q : Fin 4} (hpq : p ≠ q) :
    coordinatesSpinWeylHom (pairFlipCoordinates p q) =
      pairFlipSpinWeyl p q hpq := by
  apply Subtype.ext
  change coordinatesSpin (pairFlipCoordinates p q) = _
  apply Subtype.ext
  rw [pairFlipSpinWeyl_val]
  have h01 : bivector 0 3 * bivector 1 3 = bivector 0 1 := by
    simpa using bivector_terminal_mul_terminal 0 1
  have h02 : bivector 0 3 * bivector 2 3 = bivector 0 2 := by
    simpa using bivector_terminal_mul_terminal 0 2
  have h12 : bivector 1 3 * bivector 2 3 = bivector 1 2 := by
    simpa using bivector_terminal_mul_terminal 1 2
  have h10 : -bivector 0 1 = bivector 1 0 :=
    (bivector_reverse 0 1 (by decide)).symm
  have h20 : -bivector 0 2 = bivector 2 0 :=
    (bivector_reverse 0 2 (by decide)).symm
  have h21 : -bivector 1 2 = bivector 2 1 :=
    (bivector_reverse 1 2 (by decide)).symm
  have h30 : -bivector 0 3 = bivector 3 0 :=
    (bivector_reverse 0 3 (by decide)).symm
  have h31 : -bivector 1 3 = bivector 3 1 :=
    (bivector_reverse 1 3 (by decide)).symm
  have h32 : -bivector 2 3 = bivector 3 2 :=
    (bivector_reverse 2 3 (by decide)).symm
  have h301 : bivector 3 0 * bivector 1 3 = bivector 1 0 := by
    rw [← h30, neg_mul, h01, h10]
  have h302 : bivector 3 0 * bivector 2 3 = bivector 2 0 := by
    rw [← h30, neg_mul, h02, h20]
  have h312 : bivector 3 1 * bivector 2 3 = bivector 2 1 := by
    rw [← h31, neg_mul, h12, h21]
  fin_cases p <;> fin_cases q <;>
    simp_all [pairFlipCoordinates, coordinatesSpin, bitElement,
      h0Generator_val, centralNegOne_val]

theorem fin4MilnorH0ToSpinWeyl_generator
    (he : fin4MinusOneSymbol F ≠ 0)
    {p q : Fin 4} (hpq : p ≠ q) :
    fin4MilnorH0ToSpinWeyl he
        ⟨fin4MatsumotoDiagonalLift hpq (-1 : Fˣ),
          Subgroup.subset_closure ⟨p, q, hpq, rfl⟩⟩ =
      pairFlipSpinWeyl p q hpq := by
  change coordinatesSpinWeylHom
      (fin4MilnorH0ToCoordinates he
        ⟨fin4MatsumotoDiagonalLift hpq (-1 : Fˣ),
          Subgroup.subset_closure ⟨p, q, hpq, rfl⟩⟩) = _
  rw [fin4MilnorH0ToCoordinates_generator he hpq]
  exact coordinatesSpin_pairFlipCoordinates hpq

theorem fin4MilnorH0ToSpinWeyl_rootLift
    (he : fin4MinusOneSymbol F ≠ 0)
    {p q : Fin 4} (hpq : p ≠ q)
    (u : Fˣ) (hu : u = 1 ∨ u = -1) :
    fin4MilnorH0ToSpinWeyl he (fin4MilnorH0RootLift hpq u hu) =
      if u = 1 then 1 else pairFlipSpinWeyl p q hpq := by
  letI : CharZero F := charZero_of_fin4MinusOneSymbol_ne_zero he
  rcases hu with rfl | rfl
  · have hsub : fin4MilnorH0RootLift hpq (1 : Fˣ) (Or.inl rfl) = 1 := by
      apply Subtype.ext
      exact fin4MatsumotoDiagonalLift_one hpq
    rw [hsub, map_one]
    simp
  · have hminus : (-1 : Fˣ) ≠ 1 := by
      intro h
      have hv : (-1 : F) = 1 := congrArg Units.val h
      norm_num at hv
    rw [if_neg hminus]
    exact fin4MilnorH0ToSpinWeyl_generator he hpq

def fin4MinusOneCentralH0 : fin4MilnorH0 (F := F) :=
  ⟨centralIncl (F := F) (n := 4)
      (Multiplicative.ofAdd (fin4MinusOneSymbol F)),
    centralIncl_minusOneSymbol_mem_H0 (F := F)⟩

theorem pairFlipSpinWeyl_sq
    (p q : Fin 4) (hpq : p ≠ q) :
    pairFlipSpinWeyl p q hpq * pairFlipSpinWeyl p q hpq =
      centralNegOneSpinWeyl := by
  apply Subtype.ext
  change (pairFlipSpinWeyl p q hpq).1 *
      (pairFlipSpinWeyl p q hpq).1 = centralNegOne
  apply Subtype.ext
  simp only [Submonoid.coe_mul]
  rw [centralNegOne_val]
  change ((pairFlipSpinWeyl p q hpq).1 : Clifford) *
      ((pairFlipSpinWeyl p q hpq).1 : Clifford) = -1
  simpa only [pairFlipSpinWeyl_val] using bivector_sq p q hpq

theorem fin4MilnorH0ToSpinWeyl_centralMinusOne
    (he : fin4MinusOneSymbol F ≠ 0) :
    fin4MilnorH0ToSpinWeyl he (fin4MinusOneCentralH0 (F := F)) =
      centralNegOneSpinWeyl := by
  let hpq : (0 : Fin 4) ≠ 1 := by decide
  let x : fin4MilnorH0 (F := F) :=
    ⟨fin4MatsumotoDiagonalLift hpq (-1 : Fˣ),
      Subgroup.subset_closure ⟨0, 1, hpq, rfl⟩⟩
  have hxx : x * x = fin4MinusOneCentralH0 (F := F) := by
    apply Subtype.ext
    simpa [x, fin4MinusOneCentralH0, fin4MinusOneSymbol] using
      (fin4MatsumotoDiagonalLift_mul hpq (-1 : Fˣ) (-1 : Fˣ))
  have hm := map_mul (fin4MilnorH0ToSpinWeyl he) x x
  rw [hxx] at hm
  have hx : fin4MilnorH0ToSpinWeyl he x =
      pairFlipSpinWeyl 0 1 hpq := by
    exact fin4MilnorH0ToSpinWeyl_generator he hpq
  rw [hx, pairFlipSpinWeyl_sq] at hm
  exact hm

theorem centralSymbol_mem_H0_of_eq_one_or_neg_one
    (u : Fˣ) (hu : u = 1 ∨ u = -1) :
    centralIncl (F := F) (n := 4)
        (Multiplicative.ofAdd (milnorSym2 F u (-1 : Fˣ))) ∈
      fin4MilnorH0 (F := F) := by
  apply centralIncl_mem_H0_of_mem_zmultiples
  rcases hu with rfl | rfl
  · rw [milnorSym2_one_left]
    exact AddSubgroup.zero_mem _
  · exact fin4MinusOneSymbol_mem_zmultiples (F := F)

theorem fin4MilnorH0ToSpinWeyl_centralSymbol
    (he : fin4MinusOneSymbol F ≠ 0)
    (u : Fˣ) (hu : u = 1 ∨ u = -1) :
    fin4MilnorH0ToSpinWeyl he
        ⟨centralIncl (F := F) (n := 4)
          (Multiplicative.ofAdd (milnorSym2 F u (-1 : Fˣ))),
          centralSymbol_mem_H0_of_eq_one_or_neg_one u hu⟩ =
      if u = 1 then 1 else centralNegOneSpinWeyl := by
  letI : CharZero F := charZero_of_fin4MinusOneSymbol_ne_zero he
  rcases hu with rfl | rfl
  · have hsub :
        (⟨centralIncl (F := F) (n := 4)
            (Multiplicative.ofAdd (milnorSym2 F (1 : Fˣ) (-1 : Fˣ))),
            centralSymbol_mem_H0_of_eq_one_or_neg_one (1 : Fˣ) (Or.inl rfl)⟩ :
          fin4MilnorH0 (F := F)) = 1 := by
      apply Subtype.ext
      simp [milnorSym2_one_left]
    rw [hsub, map_one]
    simp
  · have hsub :
        (⟨centralIncl (F := F) (n := 4)
            (Multiplicative.ofAdd (milnorSym2 F (-1 : Fˣ) (-1 : Fˣ))),
            centralSymbol_mem_H0_of_eq_one_or_neg_one (-1 : Fˣ) (Or.inr rfl)⟩ :
          fin4MilnorH0 (F := F)) = fin4MinusOneCentralH0 (F := F) := by
      apply Subtype.ext
      rfl
    rw [hsub, fin4MilnorH0ToSpinWeyl_centralMinusOne]
    norm_num

theorem weylLift_conj_basis (i j : Fin 4) (hij : i ≠ j)
    (k : Fin 4) :
    ((weylLift i j hij : spinGroup spinQ) : Clifford) * basisClifford k *
        (((weylLift i j hij)⁻¹ : spinGroup spinQ) : Clifford) =
      if k = i then -basisClifford j
      else if k = j then basisClifford i else basisClifford k := by
  by_cases hki : k = i
  · subst k
    rw [weylLift_conj_basis_left]
    simp
  · by_cases hkj : k = j
    · subst k
      rw [weylLift_conj_basis_right]
      simp [hki]
    · rw [weylLift_conj_basis_other i j k hij hki hkj]
      simp [hki, hkj]

theorem weylLift_conj_bivector (i j : Fin 4) (hij : i ≠ j)
    (p q : Fin 4) :
    ((weylLift i j hij : spinGroup spinQ) : Clifford) * bivector p q *
        (((weylLift i j hij)⁻¹ : spinGroup spinQ) : Clifford) =
      (if p = i then -basisClifford j
        else if p = j then basisClifford i else basisClifford p) *
      (if q = i then -basisClifford j
        else if q = j then basisClifford i else basisClifford q) := by
  change spinConjugation (weylLift i j hij)
      (basisClifford p * basisClifford q) = _
  rw [map_mul]
  change (((weylLift i j hij : spinGroup spinQ) : Clifford) * basisClifford p *
      (((weylLift i j hij)⁻¹ : spinGroup spinQ) : Clifford)) *
    (((weylLift i j hij : spinGroup spinQ) : Clifford) * basisClifford q *
      (((weylLift i j hij)⁻¹ : spinGroup spinQ) : Clifford)) = _
  rw [weylLift_conj_basis, weylLift_conj_basis]

set_option maxHeartbeats 800000 in
theorem weylLiftSpinWeyl_conj_pairFlip
    (he : fin4MinusOneSymbol F ≠ 0)
    (i j : Fin 4) (hij : i ≠ j)
    (p q : Fin 4) (hpq : p ≠ q) :
    weylLiftSpinWeyl i j hij * pairFlipSpinWeyl p q hpq *
        (weylLiftSpinWeyl i j hij)⁻¹ =
      (if steinbergWeylRootScale (i := i) (j := j) (1 : Fˣ) p *
            (steinbergWeylRootScale (i := i) (j := j) (1 : Fˣ) q)⁻¹ = 1
        then 1 else centralNegOneSpinWeyl) *
      pairFlipSpinWeyl (Equiv.swap i j p) (Equiv.swap i j q)
        (equiv_swap_ne i j p q hpq) := by
  letI : CharZero F := charZero_of_fin4MinusOneSymbol_ne_zero he
  apply Subtype.ext
  change weylLift i j hij * (pairFlipSpinWeyl p q hpq).1 *
      (weylLift i j hij)⁻¹ = _
  apply Subtype.ext
  simp only [Submonoid.coe_mul]
  rw [pairFlipSpinWeyl_val]
  rw [weylLift_conj_bivector]
  have hc : ((centralNegOneSpinWeyl).1 : Clifford) = -1 :=
    centralNegOne_val
  fin_cases i <;> fin_cases j <;> fin_cases p <;> fin_cases q <;>
    simp_all [steinbergWeylRootScale, pairFlipSpinWeyl_val,
      Equiv.swap_apply_def, bivector]

def fin4MilnorH0Generator (p q : Fin 4) (hpq : p ≠ q) :
    fin4MilnorH0 (F := F) :=
  ⟨fin4MatsumotoDiagonalLift hpq (-1 : Fˣ),
    Subgroup.subset_closure ⟨p, q, hpq, rfl⟩⟩

theorem rootScaleOne_eq_one_or_neg_one
    (i j : Fin 4) (_hij : i ≠ j) (p : Fin 4) :
    steinbergWeylRootScale (F := F) (i := i) (j := j) (1 : Fˣ) p = 1 ∨
      steinbergWeylRootScale (F := F) (i := i) (j := j) (1 : Fˣ) p = -1 := by
  by_cases hpi : p = i
  · right
    simp [steinbergWeylRootScale, hpi]
  · left
    simp [steinbergWeylRootScale, hpi]

theorem unitSignRatio_eq_one_or_neg_one
    {a b : Fˣ} (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) :
    a * b⁻¹ = 1 ∨ a * b⁻¹ = -1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp

/-- Exact conjugation of a normalized Weyl rotor, expressed in source-field signed data. -/
theorem spinWeyl_conj_weylLift_fieldData
    (he : fin4MinusOneSymbol F ≠ 0)
    (s : spinWeylSubgroup) (p q : Fin 4) (hpq : p ≠ q) :
    let A := spinWeylToFieldSigned (F := F) s
    let σ := fieldSignedPermutationHom A
    let c := (fieldSignedMonomialData A).2
    let ratio := c p * (c q)⁻¹
    let hratio : ratio = 1 ∨ ratio = -1 :=
      unitSignRatio_eq_one_or_neg_one
        (fieldSignedMonomialData_signs A p)
        (fieldSignedMonomialData_signs A q)
    s * weylLiftSpinWeyl p q hpq * s⁻¹ =
      fin4MilnorH0ToSpinWeyl he
        (fin4MilnorH0RootLift (σ.injective.ne hpq) ratio hratio) *
      weylLiftSpinWeyl (σ p) (σ q) (σ.injective.ne hpq) := by
  dsimp only
  letI : CharZero F := charZero_of_fin4MinusOneSymbol_ne_zero he
  let A := spinWeylToFieldSigned (F := F) s
  let Ar := spinWeylMatrixRepresentation s
  let σ := fieldSignedPermutationHom A
  let σr := (signedMonomialData Ar).1
  let c := (fieldSignedMonomialData A).2
  let cr := (signedMonomialData Ar).2
  let ratio := c p * (c q)⁻¹
  have hratio : ratio = 1 ∨ ratio = -1 :=
    unitSignRatio_eq_one_or_neg_one
      (fieldSignedMonomialData_signs A p)
      (fieldSignedMonomialData_signs A q)
  have hperm : σ = σr := by
    exact fieldSignedPermutationHom_spinWeylToFieldSigned (F := F) s
  have hscale : c = fun r => realSignToField (F := F) (cr r) := by
    exact fieldSignedMonomialData_spinWeylToFieldSigned_scale s
  rw [fin4MilnorH0ToSpinWeyl_rootLift he]
  change s * weylLiftSpinWeyl p q hpq * s⁻¹ =
      (if ratio = 1 then 1 else
        pairFlipSpinWeyl (σ p) (σ q) (σ.injective.ne hpq)) *
      weylLiftSpinWeyl (σ p) (σ q) (σ.injective.ne hpq)
  rw [hperm]
  have hreal := spinWeyl_conj_weylLift_signedData s p q hpq
  dsimp only at hreal
  change s * weylLiftSpinWeyl p q hpq * s⁻¹ =
      (if cr p * (cr q)⁻¹ = 1 then 1 else
        pairFlipSpinWeyl (σr p) (σr q) (σr.injective.ne hpq)) *
      weylLiftSpinWeyl (σr p) (σr q) (σr.injective.ne hpq) at hreal
  change s * weylLiftSpinWeyl p q hpq * s⁻¹ =
      (if ratio = 1 then 1 else
        pairFlipSpinWeyl (σr p) (σr q) (σr.injective.ne hpq)) *
      weylLiftSpinWeyl (σr p) (σr q) (σr.injective.ne hpq)
  dsimp [ratio]
  simp only [hscale]
  have hcp := signedMonomialData_signs Ar p
  have hcq := signedMonomialData_signs Ar q
  change cr p = 1 ∨ cr p = -1 at hcp
  change cr q = 1 ∨ cr q = -1 at hcq
  rcases hcp with hcp | hcp <;> rcases hcq with hcq | hcq
  all_goals simp [hcp, hcq, realSignToField, signBit] at hreal ⊢
  all_goals exact hreal

set_option maxHeartbeats 800000 in
theorem spinWeyl_equivariant_generator
    (he : fin4MinusOneSymbol F ≠ 0)
    (i j : Fin 4) (hij : i ≠ j)
    (p q : Fin 4) (hpq : p ≠ q) :
    fin4MilnorH0ToSpinWeyl he
        (spinWeylH0ActionHom (F := F) (weylLiftSpinWeyl i j hij)
          (fin4MilnorH0Generator (F := F) p q hpq)) =
      weylLiftSpinWeyl i j hij *
        fin4MilnorH0ToSpinWeyl he
          (fin4MilnorH0Generator (F := F) p q hpq) *
        (weylLiftSpinWeyl i j hij)⁻¹ := by
  let ratio : Fˣ :=
    steinbergWeylRootScale (i := i) (j := j) (1 : Fˣ) p *
      (steinbergWeylRootScale (i := i) (j := j) (1 : Fˣ) q)⁻¹
  have hratio : ratio = 1 ∨ ratio = -1 :=
    unitSignRatio_eq_one_or_neg_one
      (rootScaleOne_eq_one_or_neg_one i j hij p)
      (rootScaleOne_eq_one_or_neg_one i j hij q)
  let c : fin4MilnorH0 (F := F) :=
    ⟨centralIncl (F := F) (n := 4)
        (Multiplicative.ofAdd (milnorSym2 F ratio (-1 : Fˣ))),
      centralSymbol_mem_H0_of_eq_one_or_neg_one ratio hratio⟩
  let y : fin4MilnorH0 (F := F) :=
    fin4MilnorH0Generator (F := F)
      (Equiv.swap i j p) (Equiv.swap i j q)
      (equiv_swap_ne i j p q hpq)
  have haction :
      spinWeylH0ActionHom (F := F) (weylLiftSpinWeyl i j hij)
          (fin4MilnorH0Generator (F := F) p q hpq) = c * y := by
    apply Subtype.ext
    change spinWeylActionHom (F := F) (weylLiftSpinWeyl i j hij)
        (fin4MatsumotoDiagonalLift hpq (-1 : Fˣ)) = (c * y).1
    rw [spinWeylActionHom_weylLift]
    change fin4WeylGeneratorAction (F := F) hij 1
        (fin4MatsumotoDiagonalLift hpq (-1 : Fˣ)) =
      centralIncl (F := F) (n := 4)
          (Multiplicative.ofAdd (milnorSym2 F ratio (-1 : Fˣ))) *
        fin4MatsumotoDiagonalLift (equiv_swap_ne i j p q hpq) (-1 : Fˣ)
    rw [fin4WeylGeneratorAction_matsumotoDiagonalLift]
  rw [haction, map_mul]
  change fin4MilnorH0ToSpinWeyl he c * fin4MilnorH0ToSpinWeyl he y = _
  rw [show fin4MilnorH0ToSpinWeyl he c =
      if ratio = 1 then 1 else centralNegOneSpinWeyl by
        exact fin4MilnorH0ToSpinWeyl_centralSymbol he ratio hratio]
  rw [show fin4MilnorH0ToSpinWeyl he y =
      pairFlipSpinWeyl (Equiv.swap i j p) (Equiv.swap i j q)
        (equiv_swap_ne i j p q hpq) by
        exact fin4MilnorH0ToSpinWeyl_generator he _]
  rw [show fin4MilnorH0ToSpinWeyl he
      (fin4MilnorH0Generator (F := F) p q hpq) =
        pairFlipSpinWeyl p q hpq by
      exact fin4MilnorH0ToSpinWeyl_generator he hpq]
  exact (weylLiftSpinWeyl_conj_pairFlip he i j hij p q hpq).symm

theorem spinWeyl_equivariant_weylLift
    (he : fin4MinusOneSymbol F ≠ 0)
    (i j : Fin 4) (hij : i ≠ j)
    (x : fin4MilnorH0 (F := F)) :
    fin4MilnorH0ToSpinWeyl he
        (spinWeylH0ActionHom (F := F) (weylLiftSpinWeyl i j hij) x) =
      weylLiftSpinWeyl i j hij * fin4MilnorH0ToSpinWeyl he x *
        (weylLiftSpinWeyl i j hij)⁻¹ := by
  rcases x with ⟨x, hx⟩
  let r := weylLiftSpinWeyl i j hij
  let P := fun y : MilnorDiagonalExtension F 4 =>
    ∀ hy : y ∈ fin4MilnorH0 (F := F),
      fin4MilnorH0ToSpinWeyl he
          (spinWeylH0ActionHom (F := F) r ⟨y, hy⟩) =
        r * fin4MilnorH0ToSpinWeyl he ⟨y, hy⟩ * r⁻¹
  have hP : P x := by
    apply Subgroup.closure_induction (p := fun y _ => P y)
      ?_ ?_ ?_ ?_ hx
    · rintro y ⟨p, q, hpq, rfl⟩ _
      exact spinWeyl_equivariant_generator he i j hij p q hpq
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
      change fin4MilnorH0ToSpinWeyl he
          (spinWeylH0ActionHom (F := F) r ⟨y * z, hyz⟩) =
        r * fin4MilnorH0ToSpinWeyl he ⟨y * z, hyz⟩ * r⁻¹
      rw [hsub, map_mul, map_mul, ey, ez]
      group
      simp [ky, kz, mul_assoc]
    · intro y hy ihy hyinv
      let ky : fin4MilnorH0 (F := F) := ⟨y, hy⟩
      have ey := ihy hy
      have hsub : (⟨y⁻¹, hyinv⟩ : fin4MilnorH0 (F := F)) = ky⁻¹ := by
        apply Subtype.ext
        rfl
      change fin4MilnorH0ToSpinWeyl he
          (spinWeylH0ActionHom (F := F) r ⟨y⁻¹, hyinv⟩) =
        r * fin4MilnorH0ToSpinWeyl he ⟨y⁻¹, hyinv⟩ * r⁻¹
      have hmap := map_inv (fin4MilnorH0ToSpinWeyl he) ky
      rw [hsub, map_inv, map_inv, ey, hmap]
      simp [ky]
      group
  exact hP hx

theorem spinWeyl_equivariant
    (he : fin4MinusOneSymbol F ≠ 0)
    (s : spinWeylSubgroup) (x : fin4MilnorH0 (F := F)) :
    fin4MilnorH0ToSpinWeyl he (spinWeylH0ActionHom (F := F) s x) =
      s * fin4MilnorH0ToSpinWeyl he x * s⁻¹ := by
  rcases s with ⟨s, hs⟩
  let P := fun t : spinGroup spinQ =>
    ∀ ht : t ∈ spinWeylSubgroup, ∀ y : fin4MilnorH0 (F := F),
      fin4MilnorH0ToSpinWeyl he
          (spinWeylH0ActionHom (F := F) ⟨t, ht⟩ y) =
        (⟨t, ht⟩ : spinWeylSubgroup) * fin4MilnorH0ToSpinWeyl he y *
          (⟨t, ht⟩ : spinWeylSubgroup)⁻¹
  have hP : P s := by
    apply Subgroup.closure_induction (p := fun t _ => P t)
      ?_ ?_ ?_ ?_ hs
    · rintro t ⟨i, j, hij, rfl⟩ ht y
      have hsub : (⟨weylLift i j hij, ht⟩ : spinWeylSubgroup) =
          weylLiftSpinWeyl i j hij := by
        apply Subtype.ext
        rfl
      rw [hsub]
      exact spinWeyl_equivariant_weylLift he i j hij y
    · intro hOne y
      have hsub : (⟨1, hOne⟩ : spinWeylSubgroup) = 1 := by
        apply Subtype.ext
        rfl
      rw [hsub, spinWeylH0ActionHom_one]
      simp
    · intro a b ha hb iha ihb hab y
      let sa : spinWeylSubgroup := ⟨a, ha⟩
      let sb : spinWeylSubgroup := ⟨b, hb⟩
      have hsub : (⟨a * b, hab⟩ : spinWeylSubgroup) = sa * sb := by
        apply Subtype.ext
        rfl
      have ea := iha ha
      have eb := ihb hb
      rw [hsub, spinWeylH0ActionHom_mul, ea, eb]
      group
      simp [sa, sb]
    · intro a ha iha hainv y
      let sa : spinWeylSubgroup := ⟨a, ha⟩
      let sainv : spinWeylSubgroup := ⟨a⁻¹, hainv⟩
      have hsub : sainv = sa⁻¹ := by
        apply Subtype.ext
        rfl
      let z := spinWeylH0ActionHom (F := F) sainv y
      have ea := iha ha z
      have hcancel : spinWeylH0ActionHom (F := F) sa z = y := by
        change spinWeylH0ActionHom (F := F) sa
            (spinWeylH0ActionHom (F := F) sainv y) = y
        rw [hsub]
        exact spinWeylH0ActionHom_mul_inv sa y
      rw [hcancel] at ea
      change fin4MilnorH0ToSpinWeyl he y =
        sa * fin4MilnorH0ToSpinWeyl he z * sa⁻¹ at ea
      rw [show (⟨a⁻¹, hainv⟩ : spinWeylSubgroup) = sainv by rfl,
        hsub]
      change fin4MilnorH0ToSpinWeyl he z =
        sa⁻¹ * fin4MilnorH0ToSpinWeyl he y * (sa⁻¹)⁻¹
      rw [ea]
      group
  exact hP hs x

theorem spinWeylActionHom_common
    (he : fin4MinusOneSymbol F ≠ 0)
    (x : fin4MilnorH0 (F := F)) (g : MilnorDiagonalExtension F 4) :
    spinWeylActionHom (F := F) (fin4MilnorH0ToSpinWeyl he x) g =
      x.1 * g * x.1⁻¹ := by
  change fieldSignedWeylActionHom (F := F)
      (spinWeylToFieldSigned (F := F) (fin4MilnorH0ToSpinWeyl he x)) g = _
  rw [spinWeylToFieldSigned_fin4MilnorH0 he x]
  exact fieldSignedWeylActionHom_common x g

theorem spinWeylCompatible
    (he : fin4MinusOneSymbol F ≠ 0) :
    AmalgamatedSemidirect.Compatible
      (fin4MilnorH0 (F := F))
      (fin4MilnorH0ToSpinWeyl he)
      (spinWeylActionHom (F := F)) where
  injective := fin4MilnorH0ToSpinWeyl_injective he
  stable := spinWeylActionHom_mem_H0
  equivariant := by
    intro s x
    simpa [spinWeylH0ActionHom] using spinWeyl_equivariant he s x
  common_action := spinWeylActionHom_common he

/-- Milnor's group `W` in the nonzero-symbol branch. -/
abbrev MilnorWNonzero (he : fin4MinusOneSymbol F ≠ 0) :=
  AmalgamatedSemidirect.Construction
    (fin4MilnorH0 (F := F))
    (fin4MilnorH0ToSpinWeyl he)
    (spinWeylActionHom (F := F))
    (spinWeylCompatible he)

def milnorWNonzeroCentralIncl (he : fin4MinusOneSymbol F ≠ 0) :
    Multiplicative (MilnorKDeg F 2) →* MilnorWNonzero he :=
  (AmalgamatedSemidirect.inl
    (fin4MilnorH0 (F := F))
    (fin4MilnorH0ToSpinWeyl he)
    (spinWeylActionHom (F := F))
    (spinWeylCompatible he)).comp centralIncl

theorem milnorWNonzeroCentralIncl_injective
    (he : fin4MinusOneSymbol F ≠ 0) :
    Function.Injective (milnorWNonzeroCentralIncl he) :=
  (AmalgamatedSemidirect.inl_injective
    (fin4MilnorH0 (F := F))
    (fin4MilnorH0ToSpinWeyl he)
    (spinWeylActionHom (F := F))
    (spinWeylCompatible he)).comp centralIncl_injective

theorem milnorWNonzeroCentralIncl_mem_center
    (he : fin4MinusOneSymbol F ≠ 0)
    (z : Multiplicative (MilnorKDeg F 2)) :
    milnorWNonzeroCentralIncl he z ∈ Subgroup.center (MilnorWNonzero he) := by
  exact AmalgamatedSemidirect.inl_mem_center
    (fin4MilnorH0 (F := F))
    (fin4MilnorH0ToSpinWeyl he)
    (spinWeylActionHom (F := F))
    (spinWeylCompatible he)
    (centralIncl z) (centralIncl_mem_center z)
    (fun s => spinWeylActionHom_centralIncl s z)

end MilnorSpinWeyl
end GaloisForLFunctions.HTGeometry

end
