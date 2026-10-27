import GaloisForLFunctions.HTGeometry.KreinIndexEscapeStratification
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheHodgeDefectIsCyclic

/-!
# Descent through growing finite presentations

Each negative subspace of a limiting finite Gram survives entrywise approximation.
Rectangular pullback cannot increase negative index. Combining these existing
principles compares a fixed limiting Gram with sufficiently late source presentations,
whose dimensions and coefficient maps may vary. No uniform coercivity, invertible
overlap Gram, or bound on the coefficient maps is required.

An arithmetic application must establish convergence of every pulled-back mixed
entry of the complete form. Convergence of separate profiles or diagonal entries
does not supply that statement.
-/

open Filter Matrix
open scoped Topology

namespace GaloisForLFunctions.ArithmeticIndexDescent

open HTGeometry ArithmeticCastelnuovoSeveri

/-- Every negative square of a fixed finite limit survives sufficiently late approximants. -/
theorem eventually_negIndex_limit_le {n : ℕ} {τ : Type*} {l : Filter τ}
    (G : τ → Matrix (Fin n) (Fin n) ℂ) (H : Matrix (Fin n) (Fin n) ℂ)
    (hconv : ∀ i j, Tendsto (fun t => G t i j) l (𝓝 (H i j))) :
    ∀ᶠ t in l, hermNegIndex H ≤ hermNegIndex (G t) := by
  obtain ⟨W, hdim, hW⟩ := exists_isPosDefOn_finrank_eq_posIndex (-H)
  have hnegative : ∀ x ∈ W, x ≠ 0 → (star x ⬝ᵥ H.mulVec x).re < 0 := by
    intro x hx hx0
    have h := hW x hx hx0
    rw [hermQuad_neg] at h
    exact neg_pos.mp h
  filter_upwards [eventually_negOn_subspace_of_entrywise_tendsto G H W hnegative hconv]
    with t ht
  have hpositive : IsPosDefOn (-(G t)) W := by
    intro x hx hx0
    rw [hermQuad_neg]
    exact neg_pos.mpr (ht x hx hx0)
  calc hermNegIndex H = Module.finrank ℂ W := hdim.symm
    _ ≤ hermNegIndex (G t) := finrank_le_posIndex hpositive

/-- Growing source dimensions and singular coefficient maps preserve each finite limiting index. -/
theorem eventually_negIndex_limit_le_presentation {n : ℕ} {τ : Type*} {l : Filter τ}
    (d : τ → ℕ) (A : (t : τ) → Matrix (Fin (d t)) (Fin (d t)) ℂ)
    (C : (t : τ) → Matrix (Fin n) (Fin (d t)) ℂ) (H : Matrix (Fin n) (Fin n) ℂ)
    (hconv : ∀ i j, Tendsto (fun t => (C t * A t * (C t)ᴴ) i j) l (𝓝 (H i j))) :
    ∀ᶠ t in l, hermNegIndex H ≤ hermNegIndex (A t) := by
  filter_upwards [eventually_negIndex_limit_le (fun t => C t * A t * (C t)ᴴ) H hconv]
    with t ht
  exact ht.trans (hermNegIndex_mul_mul_conjTranspose_le (C t) (A t))

end GaloisForLFunctions.ArithmeticIndexDescent

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.eventually_negIndex_limit_le_presentation
