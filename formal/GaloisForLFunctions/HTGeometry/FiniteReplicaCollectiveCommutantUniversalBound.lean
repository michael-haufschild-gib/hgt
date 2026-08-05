import GaloisForLFunctions.HTGeometry.FiniteReplicaCollectiveCommutantExact

open scoped BigOperators Matrix
open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Two finite tuples with the same occupancy function differ by a
permutation of their positions.  No injectivity of either tuple is needed. -/
theorem exists_perm_of_tupleCount_eq_general
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {m : ℕ} {x n : Fin m → ι}
    (h : tupleCount x = tupleCount n) :
    ∃ σ : Equiv.Perm (Fin m), x = fun j => n (σ j) := by
  classical
  have hcard : ∀ c : ι,
      Fintype.card {j : Fin m // x j = c} =
        Fintype.card {j : Fin m // n j = c} := by
    intro c
    have hc := congrArg (fun f => f c) h
    rw [tupleCount_apply, tupleCount_apply] at hc
    rw [Fintype.card_subtype, Fintype.card_subtype]
    exact hc
  let e : ∀ c : ι, {j : Fin m // x j = c} ≃
      {j : Fin m // n j = c} :=
    fun c => Fintype.equivOfCardEq (hcard c)
  let σ : Equiv.Perm (Fin m) := Equiv.ofFiberEquiv e
  refine ⟨σ, ?_⟩
  funext j
  exact (Equiv.ofFiberEquiv_map e j).symm

/-- Evaluate every column only along its replica-permutation orbit. -/
abbrev finiteReplicaCollectiveCommutantUniversalEvaluation
    (r d : ℕ) :
    finiteReplicaCollectiveCommutant r d →ₗ[ℂ]
      ((Fin r → Fin d) → Equiv.Perm (Fin r) → ℂ) where
  toFun X n σ := X.1 (fun j => n (σ j)) n
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Orbit evaluation is injective at every replica order and every physical
dimension.  Histogram conservation kills entries outside the orbit; the
general tuple-permutation theorem supplies the orbit coordinate inside it. -/
theorem finiteReplicaCollectiveCommutantUniversalEvaluation_injective
    (r d : ℕ) :
    Function.Injective
      (finiteReplicaCollectiveCommutantUniversalEvaluation r d) := by
  intro X Y hXY
  apply Subtype.ext
  ext x n
  by_cases hcounts : ∀ c : Fin d,
      replicaCount x c = replicaCount n c
  · have htuple : tupleCount x = tupleCount n := by
      ext c
      simpa [replicaCount_eq_tupleCount_apply] using hcounts c
    obtain ⟨σ, hσ⟩ := exists_perm_of_tupleCount_eq_general htuple
    have hcoord := congrFun (congrFun hXY n) σ
    change X.1 (fun j => n (σ j)) n =
      Y.1 (fun j => n (σ j)) n at hcoord
    simpa [hσ] using hcoord
  · push Not at hcounts
    obtain ⟨c, hc⟩ := hcounts
    rw [finiteReplicaCollectiveCommutant_entry_zero_of_count_ne
          X.2 x n c hc,
      finiteReplicaCollectiveCommutant_entry_zero_of_count_ne
          Y.2 x n c hc]

/-- Universal finite-replica commutant bound.  At every `r,d`, histogram
conservation leaves at most `r!` row coordinates per one of the `d^r`
columns.  Unlike the sharp stable-range bound, this theorem has no relation
between replica order and physical dimension. -/
theorem finiteReplicaCollectiveCommutant_finrank_le_tuple_factorial
    (r d : ℕ) :
    Module.finrank ℂ (finiteReplicaCollectiveCommutant r d) ≤
      d ^ r * Nat.factorial r := by
  calc
    Module.finrank ℂ (finiteReplicaCollectiveCommutant r d) ≤
        Module.finrank ℂ
          ((Fin r → Fin d) → Equiv.Perm (Fin r) → ℂ) :=
      LinearMap.finrank_le_finrank_of_injective
        (finiteReplicaCollectiveCommutantUniversalEvaluation_injective r d)
    _ = d ^ r * Nat.factorial r := by
      rw [Module.finrank_pi_fintype]
      simp [Fintype.card_perm]

end
end GaloisForLFunctions.HTGeometry
