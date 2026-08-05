import GaloisForLFunctions.HTGeometry.TwoReplicaTwoScaleLocalCommutatorClosure

open scoped BigOperators Matrix Kronecker
open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

set_option maxHeartbeats 4000000 in
/-- The simultaneous kernel of the three one-qubit two-replica collective
commutators consists exactly of the identity--swap plane. -/
theorem twoReplicaLocalCollectiveCommutator_commonKernel :
    {X : TwoReplicaLocalMatrix |
      ∀ a : Fin 3, twoReplicaLocalCollectiveCommutatorLinear a X = 0} =
      (Submodule.span ℂ
        ({(1 : TwoReplicaLocalMatrix), twoReplicaSwap} :
          Set TwoReplicaLocalMatrix) : Set TwoReplicaLocalMatrix) := by
  ext X
  constructor
  · intro h
    change X ∈ Submodule.span ℂ
      ({(1 : TwoReplicaLocalMatrix), twoReplicaSwap} :
        Set TwoReplicaLocalMatrix)
    rw [Submodule.mem_span_pair]
    refine ⟨X (false, true) (false, true),
      X (false, true) (true, false), ?_⟩
    have h0 := h (0 : Fin 3)
    have h2 := h (2 : Fin 3)
    rw [← Matrix.ext_iff] at h0 h2
    have h0_01 := h0 (false, false) (false, true)
    have h0_02 := h0 (false, false) (true, false)
    have h0_10 := h0 (false, true) (false, false)
    have h0_13 := h0 (false, true) (true, true)
    have h2_01 := h2 (false, false) (false, true)
    have h2_02 := h2 (false, false) (true, false)
    have h2_03 := h2 (false, false) (true, true)
    have h2_10 := h2 (false, true) (false, false)
    have h2_13 := h2 (false, true) (true, true)
    have h2_20 := h2 (true, false) (false, false)
    have h2_23 := h2 (true, false) (true, true)
    have h2_30 := h2 (true, true) (false, false)
    have h2_31 := h2 (true, true) (false, true)
    have h2_32 := h2 (true, true) (true, false)
    clear h h0 h2
    simp [twoReplicaLocalCollectiveCommutatorLinear,
      twoReplicaLocalCollectiveCommutator, ringCommutator,
      twoReplicaPauliLeft, twoReplicaPauliRight, finiteQubitPauli,
      Matrix.mul_apply, Fintype.sum_prod_type] at h0_01 h0_02 h0_10 h0_13
    simp [twoReplicaLocalCollectiveCommutatorLinear,
      twoReplicaLocalCollectiveCommutator, ringCommutator,
      twoReplicaPauliLeft, twoReplicaPauliRight, finiteQubitPauli,
      Matrix.mul_apply, Fintype.sum_prod_type] at h2_01 h2_02 h2_03 h2_10 h2_13
    simp [twoReplicaLocalCollectiveCommutatorLinear,
      twoReplicaLocalCollectiveCommutator, ringCommutator,
      twoReplicaPauliLeft, twoReplicaPauliRight, finiteQubitPauli,
      Matrix.mul_apply, Fintype.sum_prod_type] at h2_20 h2_23 h2_30 h2_31 h2_32
    have z01 : X (false, false) (false, true) = 0 := h2_01
    have z02 : X (false, false) (true, false) = 0 := h2_02
    have z03 : X (false, false) (true, true) = 0 := h2_03
    have z10 : X (false, true) (false, false) = 0 := by
      linear_combination (-1 / 2 : ℂ) * h2_10
    have z13 : X (false, true) (true, true) = 0 := h2_13
    have z20 : X (true, false) (false, false) = 0 := by
      linear_combination (-1 / 2 : ℂ) * h2_20
    have z23 : X (true, false) (true, true) = 0 := h2_23
    have z30 : X (true, true) (false, false) = 0 := by
      linear_combination (-1 / 2 : ℂ) * h2_30
    have z31 : X (true, true) (false, true) = 0 := by
      linear_combination (-1 / 2 : ℂ) * h2_31
    have z32 : X (true, true) (true, false) = 0 := by
      linear_combination (-1 / 2 : ℂ) * h2_32
    simp [z03, z30] at h0_01 h0_02 h0_10 h0_13
    have e21 : X (true, false) (false, true) =
        X (false, true) (true, false) := by
      linear_combination h0_01 + h0_10
    have e00 : X (false, false) (false, false) =
        X (false, true) (false, true) + X (false, true) (true, false) := by
      linear_combination h0_10
    have e22 : X (true, false) (true, false) =
        X (false, true) (false, true) := by
      linear_combination h0_02 + h0_10
    have e33 : X (true, true) (true, true) =
        X (false, true) (false, true) + X (false, true) (true, false) := by
      linear_combination h0_13
    apply Matrix.ext
    rintro ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
    fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;>
      simp [twoReplicaSwap, z01, z02, z03, z10, z13, z20, z23, z30,
        z31, z32, e21, e00, e22, e33]
  · intro h
    change X ∈ Submodule.span ℂ
      ({(1 : TwoReplicaLocalMatrix), twoReplicaSwap} :
        Set TwoReplicaLocalMatrix) at h
    change ∀ a : Fin 3,
      twoReplicaLocalCollectiveCommutatorLinear a X = 0
    rw [Submodule.mem_span_pair] at h
    obtain ⟨c, d, rfl⟩ := h
    intro a
    rw [map_add, map_smul, map_smul]
    have hone : twoReplicaLocalCollectiveCommutatorLinear a
        (1 : TwoReplicaLocalMatrix) = 0 := by
      simp [twoReplicaLocalCollectiveCommutatorLinear,
        twoReplicaLocalCollectiveCommutator, ringCommutator]
    have hswap : twoReplicaLocalCollectiveCommutatorLinear a
        twoReplicaSwap = 0 := by
      change ringCommutator (twoReplicaPauliLeft a) twoReplicaSwap +
        ringCommutator (twoReplicaPauliRight a) twoReplicaSwap = 0
      rw [ringCommutator, ringCommutator,
        ← twoReplicaSwap_mul_right,
        ← twoReplicaSwap_mul_left]
      abel
    rw [hone, hswap, smul_zero, smul_zero, add_zero]

end

end GaloisForLFunctions.HTGeometry
