import GaloisForLFunctions.HTGeometry.SymmetricCharacters.CommonPivotCycles

/-!
# Restriction coherence of the prescribed cycle function

Adding fixed positions leaves the multiset of nontrivial cycle lengths unchanged. Thus the
literal cycle-product functions form a normalized central coherent family independently of
positivity. Positivity is the remaining representation-theoretic condition.
-/

noncomputable section
open scoped Classical

namespace GaloisForLFunctions.SymmetricCharacters

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- Extending a permutation by fixed points preserves every prescribed cycle value. -/
theorem cycleMomentCharacter_extendDomain (p : ℕ → ℝ) (s : Y → Prop)
    [DecidablePred s] (e : X ≃ Subtype s) (σ : Equiv.Perm X) :
    cycleMomentCharacter p (σ.extendDomain e) = cycleMomentCharacter p σ := by
  simp only [cycleMomentCharacter, Equiv.Perm.cycleType_extendDomain]

/-- Inversion preserves the real cycle-product function. -/
theorem cycleMomentCharacter_inv (p : ℕ → ℝ) (σ : Equiv.Perm X) :
    cycleMomentCharacter p σ⁻¹ = cycleMomentCharacter p σ := by
  simp only [cycleMomentCharacter, Equiv.Perm.cycleType_inv]

end GaloisForLFunctions.SymmetricCharacters
