import GaloisForLFunctions.HTGeometry.FiniteReplicaCollectiveCommutantBound

open scoped BigOperators Matrix
open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Matrix implementing a permutation of replica positions. -/
def replicaPermutationMatrix (r d : ℕ) (σ : Equiv.Perm (Fin r)) :
    Matrix (Fin r → Fin d) (Fin r → Fin d) ℂ :=
  fun x n => if x = fun q => n (σ q) then 1 else 0

private theorem update_eq_comp_iff_eq_update_comp
    {r d : ℕ} (σ : Equiv.Perm (Fin r))
    (x n : Fin r → Fin d) (q : Fin r) (a b : Fin d)
    (hx : x q = b) (hn : n (σ q) = a) :
    Function.update x q a = (fun k => n (σ k)) ↔
      x = (fun k => Function.update n (σ q) b (σ k)) := by
  constructor
  · intro h
    funext k
    by_cases hkq : k = q
    · subst k
      simp [hx]
    · have hval := congrFun h k
      have hσ : σ k ≠ σ q := fun heq => hkq (σ.injective heq)
      simpa [hkq, hσ] using hval
  · intro h
    funext k
    by_cases hkq : k = q
    · subst k
      simp [hn]
    · have hval := congrFun h k
      have hσ : σ k ≠ σ q := fun heq => hkq (σ.injective heq)
      simpa [hkq, hσ] using hval

/-- Replica permutations commute with every collective physical matrix unit. -/
theorem replicaPermutationMatrix_mem_collectiveCommutant
    (r d : ℕ) (σ : Equiv.Perm (Fin r)) :
    replicaPermutationMatrix r d σ ∈
      finiteReplicaCollectiveCommutant r d := by
  intro b a
  ext x n
  rw [replicaMoveMatrix_mul_apply, mul_replicaMoveMatrix_apply]
  apply Fintype.sum_equiv σ
  intro q
  dsimp [replicaPermutationMatrix]
  by_cases hn : n (σ q) = a
  · rw [if_pos hn]
    by_cases hx : x q = b
    · rw [if_pos hx]
      rw [if_congr
        (update_eq_comp_iff_eq_update_comp σ x n q a b hx hn) rfl]
      rfl
    · rw [if_neg hx, if_neg]
      intro heq
      have hq := congrFun heq q
      apply hx
      simpa using hq
  · rw [if_neg hn]
    by_cases hx : x q = b
    · rw [if_pos hx, if_neg]
      intro heq
      have hq := congrFun heq q
      apply hn
      simpa using hq.symm
    · rw [if_neg hx]

/-- In the stable range, distinct replica permutations give linearly
independent operators: evaluation on one injective tensor separates them. -/
theorem replicaPermutationMatrix_linearIndependent
    {r d : ℕ} (hrd : r ≤ d) :
    LinearIndependent ℂ
      (fun σ : Equiv.Perm (Fin r) =>
        (⟨replicaPermutationMatrix r d σ,
          replicaPermutationMatrix_mem_collectiveCommutant r d σ⟩ :
            finiteReplicaCollectiveCommutant r d)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc σ₀
  let i := canonicalReplicaInjection hrd
  have hi : Function.Injective i := canonicalReplicaInjection_injective hrd
  let ev : finiteReplicaCollectiveCommutant r d →ₗ[ℂ] ℂ :=
    { toFun := fun X => X.1 (fun q => i (σ₀ q)) i
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hcoord : (∑ σ : Equiv.Perm (Fin r),
      c σ * replicaPermutationMatrix r d σ
        (fun q => i (σ₀ q)) i) = 0 := by
    have h := congrArg ev hc
    simpa [ev] using h
  have hterm : ∀ σ : Equiv.Perm (Fin r),
      replicaPermutationMatrix r d σ (fun q => i (σ₀ q)) i =
        if σ = σ₀ then 1 else 0 := by
    intro σ
    rw [replicaPermutationMatrix]
    have heq :
        ((fun q => i (σ₀ q)) = fun q => i (σ q)) ↔ σ = σ₀ := by
      constructor
      · intro h
        apply Equiv.ext
        intro q
        exact hi (congrFun h q).symm
      · intro h
        subst σ
        rfl
    rw [if_congr heq rfl]
    rfl
  rw [Finset.sum_congr rfl (fun σ _ => by rw [hterm σ])] at hcoord
  simpa using hcoord

/-- Exact stable-range collective-commutant dimension. -/
theorem finiteReplicaCollectiveCommutant_finrank_eq_factorial
    {r d : ℕ} (hrd : r ≤ d) :
    Module.finrank ℂ (finiteReplicaCollectiveCommutant r d) =
      Nat.factorial r := by
  apply le_antisymm
  · exact finiteReplicaCollectiveCommutant_finrank_le_factorial hrd
  · simpa [Fintype.card_perm] using
      (replicaPermutationMatrix_linearIndependent hrd).fintype_card_le_finrank

/-- **Stable-range collective centralizer classification.** Every operator
commuting with all collective physical matrix units is a linear combination
of replica-position permutations. -/
theorem replicaPermutationMatrix_span_eq_collectiveCommutant
    {r d : ℕ} (hrd : r ≤ d) :
    Submodule.span ℂ (Set.range
      (fun σ : Equiv.Perm (Fin r) =>
        (⟨replicaPermutationMatrix r d σ,
          replicaPermutationMatrix_mem_collectiveCommutant r d σ⟩ :
            finiteReplicaCollectiveCommutant r d))) = ⊤ := by
  apply
    (replicaPermutationMatrix_linearIndependent hrd).span_eq_top_of_card_eq_finrank
  simpa [Fintype.card_perm] using
    (finiteReplicaCollectiveCommutant_finrank_eq_factorial hrd).symm

end
end GaloisForLFunctions.HTGeometry
