import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.BlockUnipotentRadicals
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.DepthZeroCuspidalTypeExists

/-! The opposite two-block subgroup is the radical for the reverse
block order. Cuspidality supplies its Jacquet vanishing. -/

noncomputable section

open Matrix GlobalTheory.GLq GlobalTheory.OppRad

namespace GlobalTheory.GLp

variable {k : Type} [Field k] {a n : ℕ}

theorem blockUnipotentRadical_reverseTwoBlocks :
    blockUnipotentRadical k (fun i : Fin n => if i.val < a then 1 else 0) =
      U (1 - blockProjection k a n) (blockProjection k a n) := by
  ext u
  let s (i : Fin n) := i.val < a
  have hP : coordinateProjection k (fun i => ¬ s i) = 1 - blockProjection k a n :=
    (one_sub_coordinateProjection s).symm
  have hQ : 1 - coordinateProjection k (fun i => ¬ s i) = blockProjection k a n := by
    rw [hP, sub_sub_cancel]
  have hU : U (1 - blockProjection k a n) (blockProjection k a n) =
      U (coordinateProjection k (fun i => ¬ s i)) (1 - coordinateProjection k (fun i => ¬ s i)) :=
    congrArg₂ U hP.symm hQ.symm
  rw [hU, mem_coordinateRadical_iff, mem_blockUnipotentRadical]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  rw [Matrix.sub_apply, sub_eq_zero]
  by_cases hi : i.val < a <;> by_cases hj : j.val < a <;> simp [s, hi, hj]


theorem exists_cuspidal_type_of_principalFixed {p : ℕ} [Fact p.Prime]
    {V : Type} [AddCommGroup V] [Module ℂ V]
    (hn : 0 < n) (ρ : Representation ℂ (GL (Fin n) ℚ_[p]) V)
    (hρ : IsSmoothCuspidal ρ) (hfix : principalFixed ρ ≠ ⊥) :
    ∃ (τ : FDRep ℂ (Gn p n)) (j : τ →ₗ[ℂ] V), IsCusp τ.character ∧ Function.Injective j ∧
      ∀ (k : GL (Fin n) ℤ_[p]) (v : τ),
        j (τ.ρ (integralReduction p (Fin n) k) v) = ρ (integralInclusion p (Fin n) k) (j v) := by
  refine exists_cuspidal_type_of_jacquetVanishing hn ρ hρ.1 (fun a ha han => ?_) hfix
  change Representation.Coinvariants.ker
    (ρ.comp (U (1 - blockProjection ℚ_[p] a n) (blockProjection ℚ_[p] a n)).subtype) = ⊤
  rw [← blockUnipotentRadical_reverseTwoBlocks]
  apply hρ.2
  exact ⟨⟨a, han⟩, ⟨0, hn⟩, by simp [ha]⟩

end GlobalTheory.GLp

#print axioms GlobalTheory.GLp.exists_cuspidal_type_of_principalFixed
