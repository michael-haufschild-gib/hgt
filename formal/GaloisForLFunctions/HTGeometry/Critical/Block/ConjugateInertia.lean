import GaloisForLFunctions.HTGeometry.Critical.Block.FieldUnramified
import GaloisForLFunctions.HTGeometry.Critical.Geometric.NormalClosureTower

/-!
# Conjugates of Schur inertia preserve monodromy blocks

Every translate of a monodromy block is again a block of the same size.  Since chosen Schur
inertia preserves all non-singleton blocks, each conjugate of that inertia lies in the stabilizer
of the original block.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open MulAction
open scoped Pointwise

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 4000000

variable (K : Type*) [Field K] [CharZero K] [IsAlgClosed K] {m n : ℕ}
variable [Fact (0 < m)] [Fact (0 < n)] [Fact (1 < m)] [Fact (1 < n)]

noncomputable local instance criticalBlockConjugateInertiaInst1 : DecidableEq (criticalGeometricSheet K m n) :=
  Classical.decEq _

/-- If `h` preserves the inverse translate of `B`, then its conjugate by `g` preserves `B`. -/
theorem conjugate_mem_stabilizer_of_smul_inv_eq
    {G X : Type*} [Group G] [MulAction G X]
    (g h : G) (B : Set X) (hh : h • (g⁻¹ • B) = g⁻¹ • B) :
    g * h * g⁻¹ ∈ MulAction.stabilizer G B := by
  rw [MulAction.mem_stabilizer_iff, ← smul_smul (g * h) g⁻¹ B,
    ← smul_smul g h (g⁻¹ • B), hh, smul_smul g g⁻¹ B]
  simp

/-- Every conjugate of chosen Schur inertia stabilizes every non-singleton monodromy block. -/
theorem criticalSchurInertia_conjugate_mem_blockStabilizer [DecidableEq K]
    (hm : 1 < m) (hn : 1 < n)
    {B : Set (criticalGeometricSheet K m n)}
    (hB : MulAction.IsBlock (criticalGeometricMonodromy K m n) B)
    (hB2 : ∃ x ∈ B, ∃ y ∈ B, x ≠ y)
    (σ : criticalNormalClosure K m n ≃ₐ[criticalObservationField K m n]
      criticalNormalClosure K m n)
    (i : (criticalNormalClosureSchurValuationSubring K (Nat.zero_lt_of_lt hm)
      (Nat.zero_lt_of_lt hn)).inertiaSubgroup (criticalObservationField K m n)) :
    σ * (i : criticalNormalClosure K m n ≃ₐ[criticalObservationField K m n]
      criticalNormalClosure K m n) * σ⁻¹ ∈ criticalBlockStabilizer K B := by
  let ρ := criticalNormalClosureAction K m n
  let s : criticalGeometricMonodromy K m n := ⟨ρ σ, ⟨σ, rfl⟩⟩
  let C : Set (criticalGeometricSheet K m n) := s⁻¹ • B
  have hC : MulAction.IsBlock (criticalGeometricMonodromy K m n) C :=
    MulAction.IsBlock.translate s⁻¹ hB
  have hC2 : ∃ x ∈ C, ∃ y ∈ C, x ≠ y := by
    obtain ⟨x, hx, y, hy, hxy⟩ := hB2
    refine ⟨s⁻¹ • x, ?_, s⁻¹ • y, ?_, ?_⟩
    · exact Set.smul_mem_smul_set hx
    · exact Set.smul_mem_smul_set hy
    · exact fun h => hxy ((MulAction.injective s⁻¹) h)
  have hiC : criticalSchurInertiaAction K (Nat.zero_lt_of_lt hm)
      (Nat.zero_lt_of_lt hn) i • C = C :=
    criticalSchurInertia_smul_block_eq K hm hn hC hC2 i
  change ρ (σ * (i : _) * σ⁻¹) ∈
    MulAction.stabilizer (Equiv.Perm (criticalGeometricSheet K m n)) B
  rw [map_mul, map_mul, map_inv]
  have hs : ρ σ = (s : Equiv.Perm (criticalGeometricSheet K m n)) := rfl
  have hi : ρ (i : criticalNormalClosure K m n ≃ₐ[criticalObservationField K m n]
      criticalNormalClosure K m n) =
      criticalSchurInertiaAction K (Nat.zero_lt_of_lt hm)
        (Nat.zero_lt_of_lt hn) i := rfl
  rw [hs, hi]
  apply conjugate_mem_stabilizer_of_smul_inv_eq
  change criticalSchurInertiaAction K (Nat.zero_lt_of_lt hm)
      (Nat.zero_lt_of_lt hn) i • C = C
  exact hiC

end
end GaloisForLFunctions.HTGeometry
