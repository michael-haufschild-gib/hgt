import GaloisForLFunctions.HTGeometry.FiniteWindowReplicaCollisionResolution

/-!
# Intrinsic replica observer--spectral action law

The finite set of nonzero order-`n` replica detunings has an intrinsic
positive resolution after adjoining the harmless reference value one.  This
removes the externally supplied gap parameter from the finite-window
collision bound: every finite spectrum unconditionally satisfies a
unit-constant observer--spectral action estimate.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Absolute values of every nonzero order-`n` replica detuning. -/
def nonzeroReplicaActionMagnitudes
    {I : Type*} [Fintype I] [DecidableEq I]
    (energy : I → ℝ) (n : ℕ) : Finset ℝ :=
  ((((Finset.univ.piAntidiag n).product
      (Finset.univ.piAntidiag n)).image fun pq =>
        |replicaMultiplicityEnergy energy pq.1 -
          replicaMultiplicityEnergy energy pq.2|).filter fun x => x ≠ 0)

/-- Smallest nonzero replica action magnitude, truncated above by one.  The
adjoined value one makes the definition total even when no nonzero detuning
exists. -/
def intrinsicReplicaActionResolution
    {I : Type*} [Fintype I] [DecidableEq I]
    (energy : I → ℝ) (n : ℕ) : ℝ :=
  (insert 1 (nonzeroReplicaActionMagnitudes energy n)).min'
    (by simp)

/-- Intrinsic action resolution is positive for every finite spectrum and
every replica order, without a nonresonance premise. -/
theorem intrinsicReplicaActionResolution_pos
    {I : Type*} [Fintype I] [DecidableEq I]
    (energy : I → ℝ) (n : ℕ) :
    0 < intrinsicReplicaActionResolution energy n := by
  classical
  let S := insert 1 (nonzeroReplicaActionMagnitudes energy n)
  have hS : S.Nonempty := by simp [S]
  have hmem := S.min'_mem hS
  change 0 < S.min' hS
  rw [Finset.mem_insert] at hmem
  rcases hmem with hmin | hmin
  · rw [hmin]
    norm_num
  · rw [nonzeroReplicaActionMagnitudes, Finset.mem_filter] at hmin
    obtain ⟨himage, hne⟩ := hmin
    obtain ⟨pq, hpq, heq⟩ := Finset.mem_image.mp himage
    have hdiff : replicaMultiplicityEnergy energy pq.1 -
        replicaMultiplicityEnergy energy pq.2 ≠ 0 := by
      intro hzero
      apply hne
      rw [← heq, hzero, abs_zero]
    rw [← heq]
    exact abs_pos.mpr hdiff

/-- Intrinsic resolution is below every nonzero order-`n` replica action. -/
theorem intrinsicReplicaActionResolution_le
    {I : Type*} [Fintype I] [DecidableEq I]
    (energy : I → ℝ) (n : ℕ)
    {p q : I → ℕ}
    (hp : p ∈ Finset.univ.piAntidiag n)
    (hq : q ∈ Finset.univ.piAntidiag n)
    (hne : replicaMultiplicityEnergy energy p ≠
      replicaMultiplicityEnergy energy q) :
    intrinsicReplicaActionResolution energy n ≤
      |replicaMultiplicityEnergy energy p -
        replicaMultiplicityEnergy energy q| := by
  classical
  unfold intrinsicReplicaActionResolution
  apply Finset.min'_le
  apply Finset.mem_insert_of_mem
  rw [nonzeroReplicaActionMagnitudes, Finset.mem_filter]
  constructor
  · apply Finset.mem_image.mpr
    exact ⟨(p, q), Finset.mem_product.mpr ⟨hp, hq⟩, rfl⟩
  · exact abs_ne_zero.mpr (sub_ne_zero.mpr hne)

/-- **Unconditional finite-spectrum observer--spectral action law.**  The
finite-window return moment differs from its exact zero-action collision
mass by at most the inverse intrinsic action resolution, with unit constant
independent of dimension and replica order. -/
theorem
    norm_finiteSpectralSurvivalFidelityMean_sub_collisionMass_le_intrinsic
    {I : Type*} [Fintype I] [DecidableEq I]
    {weight energy : I → ℝ}
    (hweight : ∀ i, 0 ≤ weight i)
    (hweightSum : ∑ i, weight i = 1)
    (n : ℕ) {T : ℝ} (hT : 0 < T) :
    ‖finiteSpectralSurvivalFidelityMean weight energy n T -
        (fidelityReplicaCollisionMass weight energy n : ℂ)‖ ≤
      min 1 (T * intrinsicReplicaActionResolution energy n)⁻¹ := by
  apply norm_finiteSpectralSurvivalFidelityMean_sub_collisionMass_le
    hweight hweightSum n hT
    (intrinsicReplicaActionResolution_pos energy n)
  intro p hp q hq hne
  exact intrinsicReplicaActionResolution_le energy n hp hq hne

/-- Under maximal projective rank, zero-action collision mass is exactly the
unavoidable permutation floor, so the same intrinsic action bound controls
distance to the smallest possible completed plateau. -/
theorem norm_finiteSpectralSurvivalFidelityMean_sub_floor_le_intrinsic
    {I : Type*} [Fintype I] [DecidableEq I]
    {weight energy : I → ℝ}
    (hweight : ∀ i, 0 < weight i)
    (hweightSum : ∑ i, weight i = 1)
    (hmax : MaximallyProjectiveEnergy energy)
    (n : ℕ) {T : ℝ} (hT : 0 < T) :
    ‖finiteSpectralSurvivalFidelityMean weight energy n T -
        (fidelityReplicaPermutationFloor weight n : ℂ)‖ ≤
      min 1 (T * intrinsicReplicaActionResolution energy n)⁻¹ := by
  have hcollision :
      fidelityReplicaCollisionMass weight energy n =
        fidelityReplicaPermutationFloor weight n :=
    (all_fidelityReplicaCollisionMass_eq_floor_iff hweight energy).2 hmax n
  rw [← hcollision]
  exact
    norm_finiteSpectralSurvivalFidelityMean_sub_collisionMass_le_intrinsic
      (fun i => (hweight i).le) hweightSum n hT

end

end GaloisForLFunctions.HTGeometry
