import GaloisForLFunctions.HTGeometry.CompletedPseudoDiffOpRelativePositionSymmetry

/-!
# Euclidean separation for projective completed pseudodifferential lattices

The centered Cartan vector vanishes exactly on a projective homothety class.  Consequently the
Euclidean norm of relative position separates points of the projective lattice carrier, including
the rank-zero case.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

namespace DiffOp

variable {K : Type*} [Field K] [Differential K]

theorem centeredCoweight_eq_zero_iff_exists_const {r : ℕ} (m : Fin r → ℤ) :
    centeredCoweight m = 0 ↔ ∃ c : ℤ, m = fun _ => c := by
  classical
  constructor
  · intro h
    cases isEmpty_or_nonempty (Fin r) with
    | inl hfin =>
        letI := hfin
        exact ⟨0, Subsingleton.elim _ _⟩
    | inr hfin =>
        letI := hfin
        let i0 : Fin r := Classical.choice inferInstance
        refine ⟨m i0, ?_⟩
        funext i
        have hi := congrFun h i
        have hi0 := congrFun h i0
        simp only [centeredCoweight, Pi.zero_apply] at hi hi0
        exact_mod_cast (show (m i : ℝ) = (m i0 : ℝ) by linarith)
  · rintro ⟨c, rfl⟩
    have h := centeredCoweight_add_const (fun _ : Fin r => (0 : ℤ)) c
    calc
      centeredCoweight (fun _ : Fin r => c) =
          centeredCoweight ((fun _ : Fin r => 0) + fun _ => c) := by
            congr 1
            funext i
            simp
      _ = centeredCoweight (fun _ : Fin r => 0) := h
      _ = 0 := by
        funext i
        simp [centeredCoweight]

theorem completedPseudoDiffOpLattice_leftHomothetic_of_euclideanRelativePosition_eq_zero
    {r : ℕ} (L M : CompletedPseudoDiffOpLattice K (Fin r))
    (hzero : completedPseudoDiffOpEuclideanRelativePosition L M = 0) :
    L.LeftHomothetic M := by
  let d := completedPseudoDiffOpDominantCartanData L M
  obtain ⟨c, hc⟩ :=
    (centeredCoweight_eq_zero_iff_exists_const d.coweight).mp hzero
  let a : (CompletedPseudoDiffOp K)ˣ :=
    completedPseudoDiffOpUniformizerUnit (K := K) ^ c
  have hstd :
      (standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin r)).LeftHomothetic
        (standardCompletedPseudoDiffOpLatticeAtCoweight (K := K) d.coweight) := by
    refine ⟨a, ?_⟩
    rw [← standardCompletedPseudoDiffOpLatticeAtCoweight_zero]
    rw [leftScale_standardCompletedPseudoDiffOpLatticeAtCoweight_add_const]
    rw [hc]
    congr 1
    funext i
    simp
  have himg :
      (mapCompletedPseudoDiffOpLatticeLinear d.frame L).LeftHomothetic
        (mapCompletedPseudoDiffOpLatticeLinear d.frame M) := by
    simpa [d.map_left, d.map_right] using hstd
  have hback := mapCompletedPseudoDiffOpLatticeLinear_leftHomothetic d.frame.symm himg
  simpa [mapCompletedPseudoDiffOpLatticeLinear_trans,
    mapCompletedPseudoDiffOpLatticeLinear_refl] using hback

theorem completedPseudoDiffOpEuclideanRelativePosition_eq_zero_iff_leftHomothetic
    {r : ℕ} (L M : CompletedPseudoDiffOpLattice K (Fin r)) :
    completedPseudoDiffOpEuclideanRelativePosition L M = 0 ↔ L.LeftHomothetic M := by
  constructor
  · exact completedPseudoDiffOpLattice_leftHomothetic_of_euclideanRelativePosition_eq_zero L M
  · rintro ⟨a, rfl⟩
    rw [completedPseudoDiffOpEuclideanRelativePosition_second_leftScale,
      completedPseudoDiffOpEuclideanRelativePosition_self]

theorem differentialVariationalProjectiveEuclideanVertexDistance_eq_zero_iff
    {r : ℕ}
    (x y : DifferentialVariationalProjectiveBuildingCarrier K (Fin r)) :
    differentialVariationalProjectiveEuclideanVertexDistance x y = 0 ↔ x = y := by
  constructor
  · refine Quotient.inductionOn₂ x y ?_
    intro L M hzero
    change ‖(completedPseudoDiffOpEuclideanRelativePositionPoint L M).1‖ = 0 at hzero
    have hp : (completedPseudoDiffOpEuclideanRelativePositionPoint L M).1 = 0 :=
      norm_eq_zero.mp hzero
    have hv : completedPseudoDiffOpEuclideanRelativePosition L M = 0 := by
      apply WithLp.toLp_injective 2
      exact hp
    exact Quotient.sound
      ((completedPseudoDiffOpEuclideanRelativePosition_eq_zero_iff_leftHomothetic L M).mp hv)
  · rintro rfl
    exact differentialVariationalProjectiveEuclideanVertexDistance_self x

theorem differentialVariationalProjectiveEuclideanVertexDistance_pos_iff
    {r : ℕ}
    (x y : DifferentialVariationalProjectiveBuildingCarrier K (Fin r)) :
    0 < differentialVariationalProjectiveEuclideanVertexDistance x y ↔ x ≠ y := by
  constructor
  · intro hpos hxy
    subst y
    rw [differentialVariationalProjectiveEuclideanVertexDistance_self] at hpos
    exact (lt_irrefl 0) hpos
  · intro hxy
    have hne : differentialVariationalProjectiveEuclideanVertexDistance x y ≠ 0 := by
      intro hzero
      exact hxy
        ((differentialVariationalProjectiveEuclideanVertexDistance_eq_zero_iff x y).mp hzero)
    exact lt_of_le_of_ne
      (differentialVariationalProjectiveEuclideanVertexDistance_nonneg x y) hne.symm

end DiffOp

end
end GaloisForLFunctions.HTGeometry
