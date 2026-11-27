import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PatternCharacterGroups
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MirabolicCoordinates
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitriangularBlockCoordinates

/-! With the distinguished column cleared, the unitriangular matrix has
an identity coordinate after its leading block. The remaining rectangle
and trailing unitriangular block are free. -/

noncomputable section
open WindowedLandauTheory.MainNotions.ArithmeticCylinders
open scoped Classical

namespace GlobalTheory.GLq

variable {g n k b : ℕ} [Fact g.Prime]

/-- The unitriangular subgroup with no entries above the diagonal in column k. -/
def jacquetColumnSubgroup (g n k : ℕ) [Fact g.Prime] : Subgroup (Gn g n) :=
  patternGroup (fun i j => i < j ∧ (j : ℕ) ≠ k)
    (fun _ _ _ hij hjl => ⟨hij.1.trans hjl.1, hjl.2⟩)

theorem mem_jacquetColumnSubgroup_iff (hk : k < n) (x : Gn g n) :
    x ∈ jacquetColumnSubgroup g n k ↔
      IsUniUp x.val ∧ ∀ a, a < k → entN x.val a k = 0 := by
  change InPattern (fun i j => i < j ∧ (j : ℕ) ≠ k) x.val ↔ _
  constructor
  · intro h
    refine ⟨fun i j => ⟨fun hij => ?_, fun e => ?_⟩, fun a ha => ?_⟩
    · rw [h i j (fun h' => hij.not_gt h'.1), Matrix.one_apply_ne hij.ne']
    · subst j
      rw [h i i (fun h' => lt_irrefl _ h'.1), Matrix.one_apply_eq]
    · have han : a < n := ha.trans hk
      have hn : (⟨a, han⟩ : Fin n) ≠ ⟨k, hk⟩ := fun h' => ha.ne (congrArg Fin.val h')
      rw [entN, dif_pos ⟨han, hk⟩, h _ _ (fun h' => h'.2 rfl), Matrix.one_apply_ne hn]
  · rintro ⟨hu, hz⟩ i j hij
    obtain h | rfl | h := lt_trichotomy i j
    · have hj : (j : ℕ) = k := of_not_not (fun h' => hij ⟨h, h'⟩)
      have he := hz i.val (show (i : ℕ) < k from hj ▸ h)
      rw [← hj] at he
      rw [Matrix.one_apply_ne h.ne]
      have hn : (i : ℕ) < n ∧ (j : ℕ) < n := ⟨i.isLt, j.isLt⟩
      simpa only [entN, dif_pos hn, Fin.eta] using he
    · rw [(hu i i).2 rfl, Matrix.one_apply_eq]
    · rw [(hu i j).1 h, Matrix.one_apply_ne h.ne']

local notation "Rect" => Matrix (Fin (k + 1)) (Fin b) (ZMod g)
local notation "U" => upperUnitriangular g

private theorem leading_zeroColumn_iff (u : U (k + 1 + b)) :
    (∀ a, a < k → entN u.val.val a k = 0) ↔
      upperRightBlock (a := k) (b := 1) (unitriangularLevi u).1.val.val = 0 := by
  have he (i : Fin k) :
      upperRightBlock (a := k) (b := 1) (unitriangularLevi u).1.val.val i 0 =
        entN u.val.val i.val k := by
    rw [unitriangularLevi_fst_val, upperRightBlock, tl_apply_add]
    have h : i.val < k + 1 + b ∧ k < k + 1 + b := by omega
    rw [entN, dif_pos h]
    rfl
  constructor
  · intro h
    ext i j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact (he i).trans (h _ i.isLt)
  · intro h a ha
    rw [← he (⟨a, ha⟩ : Fin k), h, Matrix.zero_apply]

private def column_unipotent (u : jacquetColumnSubgroup g (k + 1 + b) k) :
    U (k + 1 + b) :=
  ⟨u.val, ((mem_jacquetColumnSubgroup_iff (by omega) u.val).mp u.property).1⟩

private def appendOne (A : U k) : U (k + 1) :=
  unitriangularBlock A 0 (1 : U 1)

private theorem leading_eq_appendOne (u : jacquetColumnSubgroup g (k + 1 + b) k) :
    (unitriangularLevi (column_unipotent u)).1 =
      appendOne (unitriangularLevi (b := 1) (unitriangularLevi (column_unipotent u)).1).1 := by
  let A := (unitriangularLevi (column_unipotent u)).1
  have hR : upperRightBlock (a := k) (b := 1) A.val.val = 0 :=
    (leading_zeroColumn_iff (column_unipotent u)).mp
      ((mem_jacquetColumnSubgroup_iff (by omega) u.val).mp u.property).2
  letI := unitriangular_one_subsingleton (g := g)
  have hD : (unitriangularLevi (a := k) (b := 1) A).2 = (1 : U 1) := Subsingleton.elim _ _
  have he :
      unitriangularBlock (unitriangularLevi (a := k) (b := 1) A).1
        (upperRightBlock A.val.val) (unitriangularLevi (a := k) (b := 1) A).2 = A :=
    unitriangularBlockEquiv.left_inv A
  rw [hR, hD] at he
  exact he.symm

/-- Assemble the cleared-column matrix from the remaining free blocks. -/
def jacquetColumnBlock (A : U k) (X : Rect) (D : U b) :
    jacquetColumnSubgroup g (k + 1 + b) k := by
  let v := unitriangularBlock (appendOne A) X D
  refine ⟨v.val, (mem_jacquetColumnSubgroup_iff (by omega) v.val).mpr ⟨v.property, ?_⟩⟩
  apply (leading_zeroColumn_iff v).mpr
  rw [show unitriangularLevi v = (appendOne A, D) from unitriangularLevi_block _ _ _]
  exact upperRightBlock_upperBlockMatrix A.val.val 0 (1 : Mt g 1)

theorem jacquetColumnBlock_val (A : U k) (X : Rect) (D : U b) :
    (jacquetColumnBlock A X D).val = upperBlockUnit (mirabolicBlock A.val 0) X D.val := rfl

/-- The cleared column leaves one leading unitriangular block and an
independent right rectangle and unitriangular block. -/
def jacquetColumnEquiv :
    jacquetColumnSubgroup g (k + 1 + b) k ≃ U k × (Rect × U b) where
  toFun u :=
    ((unitriangularLevi (b := 1) (unitriangularLevi (column_unipotent u)).1).1,
      upperRightBlock u.val.val, (unitriangularLevi (column_unipotent u)).2)
  invFun q := jacquetColumnBlock q.1 q.2.1 q.2.2
  left_inv u := by
    apply Subtype.ext
    let v := column_unipotent u
    have he :
        unitriangularBlock (unitriangularLevi v).1 (upperRightBlock v.val.val)
          (unitriangularLevi v).2 = v := unitriangularBlockEquiv.left_inv v
    change (unitriangularBlock
      (appendOne (unitriangularLevi (b := 1) (unitriangularLevi v).1).1)
        (upperRightBlock v.val.val) (unitriangularLevi v).2).val = v.val
    rw [← leading_eq_appendOne u]
    exact congrArg Subtype.val he
  right_inv q := by
    have he : unitriangularLevi (column_unipotent (jacquetColumnBlock q.1 q.2.1 q.2.2)) =
        (appendOne q.1, q.2.2) := unitriangularLevi_block _ _ _
    apply Prod.ext
    · dsimp only
      rw [he]
      exact congrArg Prod.fst (unitriangularLevi_block q.1 0 (1 : U 1))
    · apply Prod.ext
      · exact upperRightBlock_upperBlockMatrix (appendOne q.1).val.val q.2.1 q.2.2.val.val
      · exact congrArg (fun z : U (k + 1) × U b => z.2) he

end GlobalTheory.GLq
