import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.ParabolicBlockMatrices
import GaloisForLFunctions.HTGeometry.DetUpdateRowOne

/-! The mirabolic group stabilizes the last coordinate covector. Its
elements are upper-block matrices with bottom-right entry one. -/

noncomputable section
open Matrix GaloisForLFunctions.HTGeometry
open scoped Classical

namespace GlobalTheory.GLq

variable {g m : ℕ} [Fact g.Prime]

/-- Any nonzero row of a vector space over the prime field can be completed to an invertible matrix. -/
theorem exists_GL_with_row {n : ℕ} (l : Fin n) (ξ : Fin n → ZMod g) (hξ : ξ ≠ 0) :
    ∃ A : Gn g n, ∀ i, A.val l i = ξ i := by
  obtain ⟨i, hi⟩ : ∃ i, ξ i ≠ 0 := by
    by_contra! h
    exact hξ (funext h)
  let σ := Equiv.swap l i
  let M := (Matrix.updateRow (1 : Mt g n) i ξ).submatrix σ id
  have hsign : IsUnit (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ZMod g) :=
    (Equiv.Perm.sign σ).isUnit.map (Int.castRingHom (ZMod g))
  have hM : IsUnit M.det := by
    change IsUnit ((Matrix.updateRow (1 : Mt g n) i ξ).submatrix σ id).det
    rw [Matrix.det_permute, det_updateRow_one]
    exact hsign.mul (isUnit_iff_ne_zero.mpr hi)
  let hA := (Matrix.isUnit_iff_isUnit_det M).mpr hM
  refine ⟨hA.unit, fun j => ?_⟩
  rw [IsUnit.unit_spec hA]
  simp [M, σ, Matrix.updateRow_apply, Matrix.submatrix_apply]

variable (g m) in
/-- The standard mirabolic subgroup fixes the last coordinate covector on the right. -/
def mirabolicSubgroup : Subgroup (Gn g (m + 1)) where
  carrier := {A | (Pi.single (Fin.last m) 1 : Fin (m + 1) → ZMod g) ᵥ* A.val = Pi.single (Fin.last m) 1}
  one_mem' := vecMul_one _
  mul_mem' := by
    intro A B hA hB
    change _ ᵥ* (A.val * B.val) = _
    rw [← vecMul_vecMul, hA, hB]
  inv_mem' := by
    intro A hA
    change _ ᵥ* A.inv = _
    have h := congrArg (fun v : Fin (m + 1) → ZMod g => v ᵥ* A.inv) hA
    rw [vecMul_vecMul, A.val_inv, vecMul_one] at h
    exact h.symm

theorem mem_mirabolicSubgroup_iff (A : Gn g (m + 1)) :
    A ∈ mirabolicSubgroup g m ↔
      ∀ i, A.val (Fin.last m) i = (Pi.single (Fin.last m) 1 : Fin (m + 1) → ZMod g) i := by
  change ((Pi.single (Fin.last m) 1 : Fin (m + 1) → ZMod g) ᵥ* A.val = _) ↔ _
  have he (i : Fin (m + 1)) :
      ((Pi.single (Fin.last m) 1 : Fin (m + 1) → ZMod g) ᵥ* A.val) i = A.val (Fin.last m) i := by
    simp [vecMul, single_dotProduct]
  constructor
  · intro h i
    exact (he i).symm.trans (congrFun h i)
  · intro h
    exact funext fun i => (he i).trans (h i)

/-- The mirabolic block with first block `A` and rightmost column `v` above the diagonal. -/
def mirabolicBlock (A : Gn g m) (v : Fin m → ZMod g) : Gn g (m + 1) :=
  upperBlockUnit A (fun i _ => v i) (1 : Gn g 1)

theorem mirabolicBlock_mem (A : Gn g m) (v : Fin m → ZMod g) :
    mirabolicBlock A v ∈ mirabolicSubgroup g m := by
  rw [mem_mirabolicSubgroup_iff]
  intro j
  induction j using Fin.lastCases with
  | last =>
    rw [Pi.single_eq_same]
    change (upperBlockMatrix A.val (fun i (_ : Fin 1) => v i) (1 : Mt g 1))
      (Fin.last m) (Fin.last m) = 1
    have h : Fin.last m = Fin.natAdd m (0 : Fin 1) := Fin.ext rfl
    rw [h]
    simp [upperBlockMatrix]
  | cast j =>
    rw [Pi.single_eq_of_ne (Fin.castSucc_ne_last j)]
    change (upperBlockMatrix A.val (fun i (_ : Fin 1) => v i) (1 : Mt g 1))
      (Fin.last m) j.castSucc = 0
    have h : Fin.last m = Fin.natAdd m (0 : Fin 1) := Fin.ext rfl
    have h' : j.castSucc = Fin.castAdd 1 j := Fin.ext rfl
    rw [h, h']
    simp [upperBlockMatrix]

@[simp] theorem mirabolicBlock_one : mirabolicBlock (1 : Gn g m) 0 = 1 :=
  upperBlockUnit_one

theorem mirabolicBlock_mul (A B : Gn g m) (v w : Fin m → ZMod g) :
    mirabolicBlock A v * mirabolicBlock B w =
      mirabolicBlock (A * B) (A.val.mulVec w + v) := by
  simp only [mirabolicBlock, upperBlockUnit_mul, mul_one, Units.val_one, Matrix.mul_one]
  congr 1

theorem mirabolicBlock_inv (A : Gn g m) (v : Fin m → ZMod g) :
    (mirabolicBlock A v)⁻¹ = mirabolicBlock A⁻¹ (-A.inv.mulVec v) := by
  apply inv_eq_of_mul_eq_one_left
  rw [mirabolicBlock_mul, inv_mul_cancel]
  change mirabolicBlock (1 : Gn g m) (A.inv.mulVec v + -A.inv.mulVec v) = 1
  rw [add_neg_cancel, mirabolicBlock_one]

theorem mirabolicBlock_conj (A B : Gn g m) (v w : Fin m → ZMod g) :
    mirabolicBlock B w * mirabolicBlock A v * (mirabolicBlock B w)⁻¹ =
      mirabolicBlock (B * A * B⁻¹)
        (B.val.mulVec v + w - (B * A * B⁻¹).val.mulVec w) := by
  rw [mirabolicBlock_inv, mirabolicBlock_mul, mirabolicBlock_mul]
  congr 1
  rw [Matrix.mulVec_neg, Matrix.mulVec_mulVec, sub_eq_add_neg]
  exact add_comm _ _

theorem mirabolic_le_parabolic : mirabolicSubgroup g m ≤ twoBlockParabolic g m 1 := by
  intro A hA
  have hr := (mem_mirabolicSubgroup_iff A).mp hA
  have hlast : Fin.natAdd m (0 : Fin 1) = Fin.last m := Fin.ext rfl
  change InPar m A.val
  rw [inPar_iff_lowerLeft_zero]
  intro i j
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  change A.val (Fin.natAdd m 0) j.castSucc = 0
  rw [hlast, hr, Pi.single_eq_of_ne (Fin.castSucc_ne_last j)]

theorem exists_mirabolicBlock {A : Gn g (m + 1)} (hA : A ∈ mirabolicSubgroup g m) :
    ∃ B : Gn g m, ∃ v : Fin m → ZMod g, A = mirabolicBlock B v := by
  have hr := (mem_mirabolicSubgroup_iff A).mp hA
  have hlast : Fin.natAdd m (0 : Fin 1) = Fin.last m := Fin.ext rfl
  have hP := mirabolic_le_parabolic hA
  let p : twoBlockParabolic g m 1 := ⟨A, hP⟩
  have hbr : br m 1 A.val = 1 := by
    ext i j
    have hi : i = 0 := Subsingleton.elim _ _
    have hj : j = 0 := Subsingleton.elim _ _
    subst i
    subst j
    rw [br_apply_add, hlast, hr, Pi.single_eq_same, Matrix.one_apply_eq]
  have hD : (twoBlockLevi p).2 = 1 := by
    apply Units.ext
    have he := congrArg Prod.snd (twoBlockLevi_val p)
    change (twoBlockLevi p).2 = toG (br m 1 A.val) at he
    rw [he, hbr, toG, dif_pos isUnit_one, IsUnit.unit_spec, Units.val_one]
  refine ⟨(twoBlockLevi p).1, fun i => upperRightBlock A.val i 0, ?_⟩
  have h := upperBlockUnit_eq_of_mem_parabolic p
  rw [hD] at h
  refine h.symm.trans (congrArg (fun X => upperBlockUnit (twoBlockLevi p).1 X (1 : Gn g 1)) ?_)
  ext i j
  have hj : j = 0 := Subsingleton.elim _ _
  rw [hj]

/-- The mirabolic subgroup projects onto its invertible leading block. -/
def mirabolicLevi : mirabolicSubgroup g m →* Gn g m :=
  ((MonoidHom.fst (Gn g m) (Gn g 1)).comp twoBlockLevi).comp
    (Subgroup.inclusion mirabolic_le_parabolic)

/-- The upper part of the final column of a mirabolic matrix. -/
def mirabolicColumn (x : mirabolicSubgroup g m) : Fin m → ZMod g :=
  fun i => upperRightBlock x.val.val i 0

def mirabolicUnit (A : Gn g m) (v : Fin m → ZMod g) : mirabolicSubgroup g m :=
  ⟨mirabolicBlock A v, mirabolicBlock_mem A v⟩

@[simp] theorem mirabolicLevi_unit (A : Gn g m) (v : Fin m → ZMod g) :
    mirabolicLevi (mirabolicUnit A v) = A := by
  exact congrArg Prod.fst (twoBlockLevi_upperBlockUnit A (fun i _ => v i) (1 : Gn g 1))

@[simp] theorem mirabolicColumn_unit (A : Gn g m) (v : Fin m → ZMod g) :
    mirabolicColumn (mirabolicUnit A v) = v := by
  funext i
  exact congrFun (congrFun
    (upperRightBlock_upperBlockMatrix A.val (fun i (_ : Fin 1) => v i) (1 : Mt g 1)) i) 0

theorem mirabolicUnit_mul (A B : Gn g m) (v w : Fin m → ZMod g) :
    mirabolicUnit A v * mirabolicUnit B w = mirabolicUnit (A * B) (A.val.mulVec w + v) :=
  Subtype.ext (mirabolicBlock_mul A B v w)

/-- An element of the mirabolic subgroup is specified by its leading block and final column. -/
def mirabolicCoordinates : mirabolicSubgroup g m ≃ Gn g m × (Fin m → ZMod g) where
  toFun x := (mirabolicLevi x, mirabolicColumn x)
  invFun x := mirabolicUnit x.1 x.2
  left_inv x := by
    obtain ⟨A, v, h⟩ := exists_mirabolicBlock x.property
    rw [show x = mirabolicUnit A v from Subtype.ext h]
    simp
  right_inv x := Prod.ext (mirabolicLevi_unit x.1 x.2) (mirabolicColumn_unit x.1 x.2)

theorem mirabolicLevi_surjective : Function.Surjective (mirabolicLevi (g := g) (m := m)) :=
  fun A => ⟨mirabolicUnit A 0, mirabolicLevi_unit A 0⟩

end GlobalTheory.GLq
