import GaloisForLFunctions.HTGeometry.SteinbergFieldBruhatGeneration
import GaloisForLFunctions.HTGeometry.SteinbergUpperTetrahedronNormalForm

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {F : Type*} [Field F]

def upperSteinbergSubgroup (n : Type*) [LinearOrder n] : Subgroup (SteinbergGroup F n) :=
  Subgroup.closure (upperSteinbergGens (F := F) (n := n))

theorem upperSteinbergSubgroup_fin4_eq_tetrahedron :
    upperSteinbergSubgroup (F := F) (Fin 4)
      = steinbergUpperTetrahedronSubgroup (R := F)
          (by decide : (0 : Fin 4) ≠ 1) (by decide : (1 : Fin 4) ≠ 2)
          (by decide : (0 : Fin 4) ≠ 2) (by decide : (0 : Fin 4) ≠ 3)
          (by decide : (1 : Fin 4) ≠ 3) (by decide : (2 : Fin 4) ≠ 3) := by
  let h01 : (0 : Fin 4) ≠ 1 := by decide
  let h12 : (1 : Fin 4) ≠ 2 := by decide
  let h02 : (0 : Fin 4) ≠ 2 := by decide
  let h03 : (0 : Fin 4) ≠ 3 := by decide
  let h13 : (1 : Fin 4) ≠ 3 := by decide
  let h23 : (2 : Fin 4) ≠ 3 := by decide
  change upperSteinbergSubgroup (F := F) (Fin 4)
    = steinbergUpperTetrahedronSubgroup h01 h12 h02 h03 h13 h23
  apply le_antisymm
  · apply (Subgroup.closure_le _).2
    rintro x ⟨i, j, hij, a, hijlt, rfl⟩
    rw [steinbergUpperTetrahedronSubgroup_eq_closure]
    fin_cases i <;> fin_cases j <;> norm_num at hijlt
    · exact Subgroup.subset_closure (Or.inl ⟨a, by congr⟩)
    · exact Subgroup.subset_closure (Or.inr (Or.inl ⟨a, by congr⟩))
    · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, by congr⟩))))
    · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inl ⟨a, by congr⟩)))
    · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, by congr⟩)))))
    · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨a, by congr⟩)))))
  · rw [steinbergUpperTetrahedronSubgroup_eq_closure]
    apply (Subgroup.closure_le _).2
    rintro x (⟨a, rfl⟩ | ⟨b, rfl⟩ | ⟨c, rfl⟩ | ⟨d, rfl⟩ | ⟨e, rfl⟩ | ⟨f, rfl⟩)
    · exact Subgroup.subset_closure ⟨0, 1, h01, a, by decide, rfl⟩
    · exact Subgroup.subset_closure ⟨0, 2, h02, b, by decide, rfl⟩
    · exact Subgroup.subset_closure ⟨1, 2, h12, c, by decide, rfl⟩
    · exact Subgroup.subset_closure ⟨0, 3, h03, d, by decide, rfl⟩
    · exact Subgroup.subset_closure ⟨1, 3, h13, e, by decide, rfl⟩
    · exact Subgroup.subset_closure ⟨2, 3, h23, f, by decide, rfl⟩

end GaloisForLFunctions.HTGeometry
