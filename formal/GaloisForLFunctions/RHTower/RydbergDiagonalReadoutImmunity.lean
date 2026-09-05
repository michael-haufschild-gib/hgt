import GaloisForLFunctions.RHTower.RydbergFirstOrderChannelAdditivity

/-!
# Arbitrary finite diagonal-readout immunity

Occupation sectors are represented by diagonal zero-one masks.  Every such mask
is a Hermitian projector, so its Lindblad dephasing leaves every diagonal score
unchanged.  The conclusion is lifted to arbitrary finite rate-weighted families.
-/

open scoped BigOperators Matrix

noncomputable section

namespace RHTower

/-- A finite occupation sector, represented only by its selected basis labels. -/
structure RydbergDiagonalOccupation (d : ℕ) where
  occupied : Finset (Fin d)

namespace RydbergDiagonalOccupation

def projector {d : ℕ} (M : RydbergDiagonalOccupation d) : QuantumMatrix d :=
  Matrix.diagonal fun i => if i ∈ M.occupied then 1 else 0

@[simp] theorem projector_apply {d : ℕ} (M : RydbergDiagonalOccupation d)
    (i j : Fin d) :
    M.projector i j = if i = j ∧ i ∈ M.occupied then 1 else 0 := by
  by_cases hij : i = j <;> by_cases hi : i ∈ M.occupied <;>
    simp [projector, Matrix.diagonal, hij, hi]

@[simp] theorem projector_conjTranspose {d : ℕ}
    (M : RydbergDiagonalOccupation d) : M.projectorᴴ = M.projector := by
  rw [projector, Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  by_cases hi : i ∈ M.occupied <;> simp [hi]

@[simp] theorem projector_mul_self {d : ℕ}
    (M : RydbergDiagonalOccupation d) : M.projector * M.projector = M.projector := by
  rw [projector, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  by_cases hi : i ∈ M.occupied <;> simp [hi]

theorem projector_commutes_diagonal {d : ℕ}
    (M : RydbergDiagonalOccupation d) (score : Fin d → ℂ) :
    M.projector * Matrix.diagonal score = Matrix.diagonal score * M.projector := by
  exact (Matrix.commute_diagonal
    (fun i => if i ∈ M.occupied then (1 : ℂ) else 0) score).eq

/-- Every classical diagonal score is immune to dephasing by every occupation mask. -/
theorem diagonal_score_dephasing_damage_eq_zero {d : ℕ}
    (M : RydbergDiagonalOccupation d) (score : Fin d → ℂ) (ρ : QuantumMatrix d) :
    finiteLindbladObservableDamage M.projector (Matrix.diagonal score) ρ = 0 := by
  exact finiteLindbladObservableDamage_projector_eq_zero_of_commute
    M.projector (Matrix.diagonal score) ρ M.projector_mul_self
      M.projector_conjTranspose (M.projector_commutes_diagonal score)

/-- Centering any occupation mask by a real scalar identity is a dissipator gauge symmetry. -/
theorem centered_projector_gauge {d : ℕ}
    (M : RydbergDiagonalOccupation d) (X : QuantumMatrix d) (c : ℝ) :
    finiteLindbladDissipator (M.projector - (c : ℂ) • 1) X =
      finiteLindbladDissipator M.projector X := by
  exact finiteLindbladDissipator_sub_real_smul_one
    M.projector X c M.projector_conjTranspose

end RydbergDiagonalOccupation

/-- A finite family of occupation-dephasing channels has exactly zero terminal
damage on every diagonal objective, at arbitrary real rates. -/
theorem finiteOccupationFamily_diagonal_score_damage_eq_zero
    {ι : Type*} [Fintype ι] {d : ℕ}
    (rate : ι → ℝ) (mask : ι → RydbergDiagonalOccupation d)
    (score : Fin d → ℂ) (ρ : QuantumMatrix d) :
    finiteLindbladFamilyObservableDamage rate (fun i => (mask i).projector)
      (Matrix.diagonal score) ρ = 0 := by
  rw [finiteLindbladFamilyObservableDamage_eq_sum]
  simp [RydbergDiagonalOccupation.diagonal_score_dephasing_damage_eq_zero]

end RHTower
