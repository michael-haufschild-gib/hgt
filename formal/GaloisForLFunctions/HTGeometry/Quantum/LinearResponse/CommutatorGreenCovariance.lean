import GaloisForLFunctions.HTGeometry.Quantum.LinearResponse.DampedGapResponse

/-!
# Equivariance of commutator Green responses

The Green response is determined by its shifted commutator equation
on the range of the shifted commutator. This characterization also
holds at a pole, where the response vanishes on the resonant block.
-/

open Matrix Set
open scoped Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The commutator with the scalar shift subtracted. -/
def hamiltonianShiftedCommutator {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ)
    (z : ℂ) (Y : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  H * Y - Y * H - z • Y

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {H : Matrix ι ι ℂ}

private theorem eq_of_energyEntries (hH : H.IsHermitian) {X Y : Matrix ι ι ℂ}
    (h : ∀ i j, hamiltonianEnergyCoordinates hH X i j = hamiltonianEnergyCoordinates hH Y i j) :
    X = Y :=
  (hamiltonianEnergyCoordinates hH).injective (Matrix.ext h)

private theorem energyCoordinates_shiftedHamiltonianCommutator_apply (hH : H.IsHermitian)
    (z : ℂ) (Y : Matrix ι ι ℂ) (i j : ι) :
    hamiltonianEnergyCoordinates hH (hamiltonianShiftedCommutator H z Y) i j =
      ((hamiltonianGap hH i j : ℂ) - z) * hamiltonianEnergyCoordinates hH Y i j := by
  rw [hamiltonianShiftedCommutator, map_sub, Matrix.sub_apply, energyCoordinates_commutator_apply,
    map_smul, Matrix.smul_apply, smul_eq_mul, sub_mul]

/-- The squared shifted equation and range condition characterize the
Green response even on a resonant block. -/
theorem eq_hamiltonianCommutatorGreen_iff (hH : H.IsHermitian)
    (z : ℂ) (X Y : Matrix ι ι ℂ) :
    Y = hamiltonianCommutatorGreen hH z X ↔
      hamiltonianShiftedCommutator H z (hamiltonianShiftedCommutator H z Y) =
        hamiltonianShiftedCommutator H z X ∧
      ∃ W, hamiltonianShiftedCommutator H z W = Y := by
  constructor
  · rintro rfl
    constructor
    · apply eq_of_energyEntries hH
      intro i j
      simp only [energyCoordinates_shiftedHamiltonianCommutator_apply,
        energyCoordinates_commutatorGreen_apply]
      by_cases h : (hamiltonianGap hH i j : ℂ) - z = 0
      · simp only [h, zero_mul]
      · rw [mul_inv_cancel_left₀ h]
    · refine ⟨hamiltonianCommutatorGreen hH z (hamiltonianCommutatorGreen hH z X), ?_⟩
      apply eq_of_energyEntries hH
      intro i j
      simp only [energyCoordinates_shiftedHamiltonianCommutator_apply,
        energyCoordinates_commutatorGreen_apply]
      by_cases h : (hamiltonianGap hH i j : ℂ) - z = 0
      · simp only [h, _root_.inv_zero, zero_mul]
      · rw [mul_inv_cancel_left₀ h]
  · rintro ⟨hY, W, hW⟩
    apply eq_of_energyEntries hH
    intro i j
    rw [energyCoordinates_commutatorGreen_apply]
    by_cases h : (hamiltonianGap hH i j : ℂ) - z = 0
    · simp only [← hW, energyCoordinates_shiftedHamiltonianCommutator_apply, h, _root_.inv_zero,
        zero_mul]
    · have he := congrArg (fun M : Matrix ι ι ℂ => hamiltonianEnergyCoordinates hH M i j) hY
      simp only [energyCoordinates_shiftedHamiltonianCommutator_apply] at he
      apply mul_left_cancel₀ h
      rw [mul_inv_cancel_left₀ h]
      exact mul_left_cancel₀ h he

/-- The shifted response loses exactly its own resonant component. -/
theorem sub_shiftedCommutatorGreen_eq_gapComponent (hH : H.IsHermitian)
    (μ : ℝ) (X : Matrix ι ι ℂ) :
    X - hamiltonianShiftedCommutator H (μ : ℂ) (hamiltonianCommutatorGreen hH μ X) =
      hamiltonianGapComponent hH μ X := by
  apply eq_of_energyEntries hH
  intro i j
  rw [map_sub, Matrix.sub_apply, energyCoordinates_shiftedHamiltonianCommutator_apply,
    energyCoordinates_commutatorGreen_apply, energyCoordinates_gapComponent_apply]
  by_cases hg : hamiltonianGap hH i j = μ
  · simp only [hg, sub_self, zero_mul, sub_zero, if_true]
  · have h : (hamiltonianGap hH i j : ℂ) - μ ≠ 0 :=
      sub_ne_zero.mpr fun he => hg (Complex.ofReal_injective he)
    rw [if_neg hg, mul_inv_cancel_left₀ h, sub_self]

omit [DecidableEq ι] [DecidableEq κ] in
/-- A star-algebra change of coordinates preserves Hermiticity. -/
theorem isHermitian_map_starAlgEquiv (e : Matrix ι ι ℂ ≃⋆ₐ[ℂ] Matrix κ κ ℂ)
    (hH : H.IsHermitian) : (e H).IsHermitian := by
  have h : star H = H := (Matrix.star_eq_conjTranspose H).trans hH
  change (e H)ᴴ = e H
  rw [← Matrix.star_eq_conjTranspose, ← map_star e, h]

omit [DecidableEq ι] [DecidableEq κ] in
theorem map_hamiltonianShiftedCommutator (e : Matrix ι ι ℂ ≃⋆ₐ[ℂ] Matrix κ κ ℂ)
    (H X : Matrix ι ι ℂ) (z : ℂ) :
    e (hamiltonianShiftedCommutator H z X) = hamiltonianShiftedCommutator (e H) z (e X) := by
  simp only [hamiltonianShiftedCommutator, map_sub, map_mul, map_smul]

/-- Every star-algebra change of basis transports the totalized Green
response, without choosing compatible eigenbases. -/
theorem map_hamiltonianCommutatorGreen (e : Matrix ι ι ℂ ≃⋆ₐ[ℂ] Matrix κ κ ℂ)
    (hH : H.IsHermitian) (z : ℂ) (X : Matrix ι ι ℂ) :
    e (hamiltonianCommutatorGreen hH z X) =
      hamiltonianCommutatorGreen (isHermitian_map_starAlgEquiv e hH) z (e X) := by
  let Y := hamiltonianCommutatorGreen hH z X
  obtain ⟨hs, W, hW⟩ := (eq_hamiltonianCommutatorGreen_iff hH z X Y).mp rfl
  apply (eq_hamiltonianCommutatorGreen_iff (isHermitian_map_starAlgEquiv e hH) z (e X) (e Y)).mpr
  constructor
  · simpa only [map_hamiltonianShiftedCommutator] using congrArg e hs
  · exact ⟨e W, by simpa only [map_hamiltonianShiftedCommutator] using congrArg e hW⟩

/-- Equivariance of the filtered response holds for every center and positive width. -/
theorem map_hamiltonianDampedGapResponse (e : Matrix ι ι ℂ ≃⋆ₐ[ℂ] Matrix κ κ ℂ)
    (hH : H.IsHermitian) (μ : ℝ) (ε : Ioi (0 : ℝ)) (X : Matrix ι ι ℂ) :
    e (hamiltonianDampedGapResponse hH μ ε X) =
      hamiltonianDampedGapResponse (isHermitian_map_starAlgEquiv e hH) μ ε (e X) := by
  simp only [hamiltonianDampedGapResponse, map_smul, map_hamiltonianCommutatorGreen]

theorem map_hamiltonianDampedGapResponse_of_eq (e : Matrix ι ι ℂ ≃⋆ₐ[ℂ] Matrix κ κ ℂ)
    (hH : H.IsHermitian) {K : Matrix κ κ ℂ} (hK : K.IsHermitian) (he : e H = K)
    (μ : ℝ) (ε : Ioi (0 : ℝ)) (X : Matrix ι ι ℂ) :
    e (hamiltonianDampedGapResponse hH μ ε X) = hamiltonianDampedGapResponse hK μ ε (e X) := by
  subst K
  exact map_hamiltonianDampedGapResponse e hH μ ε X

/-- Spectral projection onto a Bohr frequency is equivariant. -/
theorem map_hamiltonianGapComponent (e : Matrix ι ι ℂ ≃⋆ₐ[ℂ] Matrix κ κ ℂ)
    (hH : H.IsHermitian) (μ : ℝ) (X : Matrix ι ι ℂ) :
    e (hamiltonianGapComponent hH μ X) =
      hamiltonianGapComponent (isHermitian_map_starAlgEquiv e hH) μ (e X) := by
  rw [← sub_shiftedCommutatorGreen_eq_gapComponent hH μ X, map_sub,
    map_hamiltonianShiftedCommutator, map_hamiltonianCommutatorGreen,
    sub_shiftedCommutatorGreen_eq_gapComponent]

#print axioms eq_hamiltonianCommutatorGreen_iff
#print axioms map_hamiltonianCommutatorGreen
#print axioms map_hamiltonianDampedGapResponse
#print axioms map_hamiltonianGapComponent

end

end GaloisForLFunctions.HTGeometry
