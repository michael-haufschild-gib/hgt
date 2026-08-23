import GaloisForLFunctions.HTGeometry.ReplicaHilbertCoareaIncidenceLaw
import GaloisForLFunctions.HTGeometry.FiniteReplicaTwoLocalPauliWordHall

open scoped BigOperators Matrix ENNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Canonical identification between replicated Choi indices and the paired
row/column tuple indices used by the local-Pauli Hall action. -/
def replicaChoiTupleIndexEquiv (r d : ℕ) :
    (Fin r → (Fin d × Fin d)) ≃
      ((Fin r → Fin d) × (Fin r → Fin d)) where
  toFun f := (fun a => (f a).1, fun a => (f a).2)
  invFun f := fun a => (f.1 a, f.2 a)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The same Choi-tuple identification as a unitary coordinate transport. -/
def replicaChoiTupleLinearIsometryEquiv (r d : ℕ) :
    EuclideanSpace ℂ (Fin r → (Fin d × Fin d)) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ ((Fin r → Fin d) × (Fin r → Fin d)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (replicaChoiTupleIndexEquiv r d)

/-- Occupied replicated Choi image transported into the physical Hall
representation on replicated matrix row/column tuples. -/
def replicaChoiTargetHallSpan
    {C : Type*} (r n : ℕ)
    (target : C → (Fin (2 ^ n) × Fin (2 ^ n)) → ℂ) :
    Submodule ℂ
      (EuclideanSpace ℂ
        ((Fin r → Fin (2 ^ n)) × (Fin r → Fin (2 ^ n)))) :=
  (replicaTargetSpan r target).map
    (replicaChoiTupleLinearIsometryEquiv r (2 ^ n)).toLinearEquiv.toLinearMap

theorem finrank_replicaChoiTargetHallSpan
    {C : Type*} (r n : ℕ)
    (target : C → (Fin (2 ^ n) × Fin (2 ^ n)) → ℂ) :
    Module.finrank ℂ (replicaChoiTargetHallSpan r n target) =
      Module.finrank ℂ (replicaTargetSpan r target) := by
  exact LinearEquiv.finrank_map_eq
    (replicaChoiTupleLinearIsometryEquiv r (2 ^ n)).toLinearEquiv
    (replicaTargetSpan r target)

/-- **Circuit-image Hall visibility law.**  At every stable replica order,
the occupied replicated Choi image is visible after at most `n` physical
one/two-local commutator factors, except for the exact factorial collective
commutant.  Circuit labels and duplicate words never enter. -/
theorem replicaChoiTargetSpan_finrank_le_wordShadow_add_factorial
    {C : Type*} {r n : ℕ} (hrn : r ≤ 2 ^ n)
    (target : C → (Fin (2 ^ n) × Fin (2 ^ n)) → ℂ) :
    Module.finrank ℂ (replicaTargetSpan r target) ≤
      Module.finrank ℂ
        (finiteReplicaTwoLocalPauliWordShadow (Fin r) n n
          (replicaChoiTargetHallSpan r n target)) + r.factorial := by
  rw [← finrank_replicaChoiTargetHallSpan r n target]
  exact finiteReplicaTwoLocalPauliWordShadow_finrank_le_add_factorial
    hrn (replicaChoiTargetHallSpan r n target)

/-- Quantitative survivor form: every occupied Choi direction beyond the
factorial permutation sector produces an independent local-word-visible
direction by physical depth `n`. -/
theorem replicaChoiTargetSpan_finrank_sub_factorial_le_wordShadow
    {C : Type*} {r n : ℕ} (hrn : r ≤ 2 ^ n)
    (target : C → (Fin (2 ^ n) × Fin (2 ^ n)) → ℂ) :
    Module.finrank ℂ (replicaTargetSpan r target) - r.factorial ≤
      Module.finrank ℂ
        (finiteReplicaTwoLocalPauliWordShadow (Fin r) n n
          (replicaChoiTargetHallSpan r n target)) := by
  have h := replicaChoiTargetSpan_finrank_le_wordShadow_add_factorial
    hrn target
  omega

/-- If occupied replicated Choi image is larger than exact collective
permutation sector, some physical one/two-local word of depth at most `n`
acts nontrivially on it. -/
theorem exists_nonzero_twoLocalWordResponse_of_factorial_lt_replicaTargetSpan_finrank
    {C : Type*} {r n : ℕ} (hrn : r ≤ 2 ^ n)
    (target : C → (Fin (2 ^ n) × Fin (2 ^ n)) → ℂ)
    (hlarge : r.factorial < Module.finrank ℂ (replicaTargetSpan r target)) :
    ∃ T : Module.End ℂ
        (EuclideanSpace ℂ
          ((Fin r → Fin (2 ^ n)) × (Fin r → Fin (2 ^ n)))),
      T ∈ (finiteReplicaTwoLocalPauliEndGeneratorSpan (Fin r) n) ^ n ∧
        ∃ x,
          x ∈ replicaChoiTargetHallSpan r n target ∧ T x ≠ 0 := by
  let U := replicaChoiTargetHallSpan r n target
  have hshadowpos :
      0 < Module.finrank ℂ
        (finiteReplicaTwoLocalPauliWordShadow (Fin r) n n U) := by
    have hbound := replicaChoiTargetSpan_finrank_le_wordShadow_add_factorial
      hrn target
    dsimp only [U] at hbound ⊢
    omega
  by_contra hnone
  push Not at hnone
  have hshadowbot :
      finiteReplicaTwoLocalPauliWordShadow (Fin r) n n U = ⊥ := by
    unfold finiteReplicaTwoLocalPauliWordShadow endomorphismSubmoduleImage
    apply iSup_eq_bot.mpr
    intro T
    rw [eq_bot_iff]
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    have hzero : T.1 x = 0 := hnone T.1 T.2 x hx
    exact hzero
  rw [hshadowbot, finrank_bot] at hshadowpos
  omega

end

end GaloisForLFunctions.HTGeometry
