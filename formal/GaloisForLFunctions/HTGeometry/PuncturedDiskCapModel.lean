import GaloisForLFunctions.HTGeometry.PuncturedDiskCover

/-!
# The full disk for peripheral cap charts

The unit disk is contractible and locally path connected. Removing its center
recovers the punctured unit-disk covering model through an explicit homeomorphism.
-/

open Topology Set Function

namespace GaloisForLFunctions.HTGeometry

/-- The full disk used to fill a finite peripheral component. -/
abbrev UnitCapDisk := {z : ℂ // ‖z‖ < 1}

def unitCapCenter : UnitCapDisk := ⟨0, by simp⟩

instance unitCapDiskContractibleSpace : ContractibleSpace UnitCapDisk := by
  have hball : Metric.ball (0 : ℂ) 1 = {z : ℂ | ‖z‖ < 1} := by
    ext z
    simp only [Metric.mem_ball, dist_zero_right, mem_setOf_eq]
  have h := Metric.contractibleSpace_ball (x := (0 : ℂ)) (r := (1 : ℝ)) (by norm_num)
  rw [hball] at h
  exact h

instance unitCapDiskLocallyPathConnectedSpace : LocallyPathConnectedSpace UnitCapDisk :=
  (isOpen_lt continuous_norm continuous_const).locallyPathConnectedSpace

/-- Forgetting the nested subtype identifies the punctured cap with the model disk. -/
def puncturedCapHomeomorph : {z : UnitCapDisk // z ≠ unitCapCenter} ≃ₜ PuncturedUnitDisk where
  toFun z := ⟨z.val.val, fun h => z.property (Subtype.ext h), z.val.property⟩
  invFun z := ⟨⟨z.val, z.property.2⟩, fun h => z.property.1 (congrArg Subtype.val h)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp] theorem puncturedCapHomeomorph_val (z : {z : UnitCapDisk // z ≠ unitCapCenter}) :
    (puncturedCapHomeomorph z : ℂ) = z.val.val := rfl

@[simp] theorem puncturedCapHomeomorph_symm_val (z : PuncturedUnitDisk) :
    (puncturedCapHomeomorph.symm z).val.val = z.val := rfl

instance puncturedCapPathConnectedSpace : PathConnectedSpace {z : UnitCapDisk // z ≠ unitCapCenter} :=
  puncturedCapHomeomorph.symm.surjective.pathConnectedSpace puncturedCapHomeomorph.symm.continuous

end GaloisForLFunctions.HTGeometry
