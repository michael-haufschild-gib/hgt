import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.Pinching
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.NormalForm
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.PauliSectorRotations
import GaloisForLFunctions.HTGeometry.RationalCommonTimeWitness

/-! # Effective evolution under a field of order inverse time -/
open Matrix Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.Dephasing
noncomputable section
open DiagonalSynthesis

/-- A field scaled inversely with the laboratory date contributes its
diagonal in the unperturbed energy basis. The bound is uniform on every
bounded interval of rescaled field strengths. -/
theorem dephased_evolution {n : ℕ} (H Z : selfAdjoint (Register n)) (hi : Function.Injective H.2.isHermitian.eigenvalues) :
    let D := pinching H.2.isHermitian Z.val
    IsSelfAdjoint D ∧ ∃ C > (0:ℝ), ∀ u T : ℝ, 0 < T →
      ‖unitaryEvolution (H.val+(u/T) • Z.val) T-unitaryEvolution H.val T*unitaryEvolution D u‖ ≤ C*(|u|+u^2)/T := by
  letI : CStarAlgebra (Register n) := {}
  intro D
  obtain ⟨hd,hc,X,hX⟩ := pinching_commutator H.2.isHermitian Z.2.isHermitian hi
  let C := 2*‖X‖+‖X*D-Z.val*X‖+1
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨hd.isSelfAdjoint,C,hC,fun u T hT => ?_⟩
  have h := inverse_time_field_bound H.val Z.val D X H.2 Z.2 hd.isSelfAdjoint hX u T hT
  change ‖unitaryEvolution (H.val+(u/T) • Z.val) T-unitaryEvolution (H.val+(u/T) • D) T‖ ≤ _ at h
  have he : (u/T) • D=((u/T:ℝ):ℂ) • D := by
    ext i j
    simp only [Matrix.smul_apply,Complex.real_smul,smul_eq_mul]
  rw [he,unitaryEvolution_add_of_commuting (hc.smul_right ((u/T:ℝ):ℂ)),unitaryEvolution_smul_generator,
    div_mul_cancel₀ _ hT.ne'] at h
  apply h.trans (div_le_div_of_nonneg_right _ hT.le)
  have h₁ : 2*‖X‖ ≤ C := by dsimp only [C]; linarith only [norm_nonneg (X*D-Z.val*X)]
  have h₂ : ‖X*D-Z.val*X‖ ≤ C := by dsimp only [C]; linarith only [norm_nonneg X]
  linarith only [mul_le_mul_of_nonneg_right h₁ (abs_nonneg u),mul_le_mul_of_nonneg_right h₂ (sq_nonneg u)]

#print axioms dephased_evolution
end
end GaloisForLFunctions.HTGeometry.Dephasing
