import GaloisForLFunctions.HTGeometry.Sl2LineStabiliserBridge

/-!
# Finite dimension bounds the line stabilisers

If a subspace `L` of matrices is finite dimensional over the base field, then for every nonzero `Y`
the scalars carrying `Y` into `L` are bounded over the base: `finrank L + 1` of them give
`finrank L + 1` elements of `L`, which are dependent, and the relation divides by `Y`.

This replaces the line-stabiliser hypothesis of Cassidy's classification by finite dimensionality of
the Lie algebra, which for a differential algebraic group of finite type is automatic.

* `boundedOverBase_smul_of_finiteDimensional`;
* `cassidy_sl2_of_finiteDimensional`.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {C U : Type*} [Field C] [Field U] [Algebra C U]

/-- **Finite dimension bounds the scalars carrying `Y` into `L`.** -/
theorem boundedOverBase_smul_of_finiteDimensional
    (L : Submodule C (Matrix (Fin 2) (Fin 2) U)) [FiniteDimensional C L]
    {Y : Matrix (Fin 2) (Fin 2) U} (hY : Y ≠ 0) :
    BoundedOverBase C {c : U | c • Y ∈ L} := by
  classical
  refine ⟨Module.finrank C L, fun f hf => ?_⟩
  set v : Fin (Module.finrank C L + 1) → L := fun i => ⟨f i • Y, by exact hf i⟩ with hv
  have hdep : ¬ LinearIndependent C v := by
    intro hli
    have hcard := hli.fintype_card_le_finrank
    simp only [Fintype.card_fin] at hcard
    omega
  rw [Fintype.not_linearIndependent_iff] at hdep
  obtain ⟨g, hgsum, i₀, hgi₀⟩ := hdep
  refine ⟨g, ⟨i₀, hgi₀⟩, ?_⟩
  have hval : ((∑ i, g i • v i : L) : Matrix (Fin 2) (Fin 2) U)
      = (∑ i, algebraMap C U (g i) * f i) • Y := by
    rw [Submodule.coe_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    show (g i • v i : Matrix (Fin 2) (Fin 2) U) = _
    show (g i : C) • (f i • Y) = (algebraMap C U (g i) * f i) • Y
    rw [← smul_smul]
    exact (algebraMap_smul U (g i) (f i • Y)).symm
  rw [hgsum] at hval
  have hzero : (∑ i, algebraMap C U (g i) * f i) • Y = 0 := by
    rw [← hval]
    rfl
  rcases smul_eq_zero.mp hzero with h | h
  · exact h
  · exact absurd h hY

/-- **Cassidy's classification for `sl₂` with a finite-dimensional Lie algebra.** -/
theorem cassidy_sl2_of_finiteDimensional [IsAlgClosed C] [IsAlgClosed U] [CharZero U]
    (L : Submodule C (Matrix (Fin 2) (Fin 2) U)) [FiniteDimensional C L]
    (htr : ∀ A ∈ L, A.trace = 0)
    (hbr : ∀ A ∈ L, ∀ B ∈ L, A * B - B * A ∈ L)
    (hdense : ∀ Z : Matrix (Fin 2) (Fin 2) U, Z.trace = 0 →
      Z ∈ Submodule.span U (L : Set (Matrix (Fin 2) (Fin 2) U))) :
    ∃ P Q : Matrix (Fin 2) (Fin 2) U, P * Q = 1 ∧ Q * P = 1 ∧
      L.map (conjLinear C P Q) = Submodule.span C {sl2H U, sl2E U, sl2F U} :=
  cassidy_sl2_of_bounded L htr hbr hdense
    (fun _ _ hYne => boundedOverBase_smul_of_finiteDimensional L hYne)

end

end GaloisForLFunctions.HTGeometry
