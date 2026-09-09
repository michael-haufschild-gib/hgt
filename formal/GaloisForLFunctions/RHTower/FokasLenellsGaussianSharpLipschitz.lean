import GaloisForLFunctions.RHTower.FokasLenellsExactLipschitz
import GaloisForLFunctions.RHTower.FokasLenellsCauchyNormGate

/-!
# Positive optimal Lipschitz constants without operator-norm derivatives

Actual Gaussian scattering produces globally Lipschitz operator curves with
positive exact constants, although they are nowhere differentiable in
operator norm. The bounded strong derivative remains available on every
vector, so this is a genuine separation between two kinds of regularity.
-/

open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

private theorem positive_weight_of_not_differentiable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : ℝ → E) (K t : ℝ) (hK : 0 ≤ K)
    (hlip : ∀ s v, ‖T s - T v‖ ≤ K * ‖s-v‖)
    (hn : ¬ DifferentiableAt ℝ T t) : 0 < K := by
  by_contra hpos
  have hzero : K = 0 := le_antisymm (le_of_not_gt hpos) hK
  have he : T = fun _ => T t := by
    funext s
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    exact le_antisymm (by simpa only [hzero, zero_mul] using hlip s t) (norm_nonneg _)
  apply hn
  rw [he]
  exact differentiableAt_const _

/-- The upper Gaussian multiplier has a strictly positive optimal time Lipschitz constant. -/
theorem norm_directTimeMultiplier_Gaussian_upper_pos (a : ℝ) :
    0 < ‖directTimeMultiplier (compatibilityGaussian a) 0 0 true‖ :=
  positive_weight_of_not_differentiable
    (fun t => directMultiplier (compatibilityGaussian a) t 0 true) _ 0 (norm_nonneg _)
    (norm_directMultiplier_time_sub_le_initial_generator _ 0 true)
    (directMultiplier_Gaussian_strong_not_operator_derivative a 0 0).2

/-- The Gaussian full jump has a strictly positive optimal time Lipschitz constant. -/
theorem norm_directJumpTimeOperator_Gaussian_pos (a : ℝ) :
    0 < ‖directJumpTimeOperator (compatibilityGaussian a) 0 0‖ :=
  positive_weight_of_not_differentiable
    (fun t => directJumpPerturbation (compatibilityGaussian a) t 0) _ 0 (norm_nonneg _)
    (norm_directJumpPerturbation_time_sub_le_initial_generator _ 0)
    (directJumpPerturbation_Gaussian_not_operator_differentiableAt a 0 0)

/-- Every actual Gaussian Cauchy time generator has positive norm. -/
theorem norm_directCauchyTimeOperator_Gaussian_pos (a t x : ℝ) :
    0 < ‖directCauchyTimeOperator (compatibilityGaussian a) t x‖ := by
  rw [norm_directCauchyTimeOperator_time_space_invariant]
  exact norm_directJumpTimeOperator_Gaussian_pos a

/-- The upper Gaussian multiplier has an optimal positive global bound and no operator-norm derivative anywhere. -/
theorem directMultiplier_Gaussian_sharp_lipschitz_nowhere_differentiable (a x : ℝ) :
    0 < ‖directTimeMultiplier (compatibilityGaussian a) 0 0 true‖ ∧
    (∀ L : ℝ, (∀ s v,
      ‖directMultiplier (compatibilityGaussian a) s x true -
        directMultiplier (compatibilityGaussian a) v x true‖ ≤ L * ‖s-v‖) ↔
      ‖directTimeMultiplier (compatibilityGaussian a) 0 0 true‖ ≤ L) ∧
    (∀ t : ℝ, ¬ DifferentiableAt ℝ
      (fun s => directMultiplier (compatibilityGaussian a) s x true) t) :=
  ⟨norm_directTimeMultiplier_Gaussian_upper_pos a,
    directMultiplier_time_lipschitz_iff _ x true,
    fun t => (directMultiplier_Gaussian_strong_not_operator_derivative a t x).2⟩

/-- The full Gaussian jump retains a positive optimal Lipschitz constant despite nowhere operator-norm differentiability. -/
theorem directJumpPerturbation_Gaussian_sharp_lipschitz_nowhere_differentiable (a x : ℝ) :
    0 < ‖directJumpTimeOperator (compatibilityGaussian a) 0 0‖ ∧
    (∀ L : ℝ, (∀ s v,
      ‖directJumpPerturbation (compatibilityGaussian a) s x -
        directJumpPerturbation (compatibilityGaussian a) v x‖ ≤ L * ‖s-v‖) ↔
      ‖directJumpTimeOperator (compatibilityGaussian a) 0 0‖ ≤ L) ∧
    (∀ t : ℝ, ¬ DifferentiableAt ℝ
      (fun s => directJumpPerturbation (compatibilityGaussian a) s x) t) :=
  ⟨norm_directJumpTimeOperator_Gaussian_pos a,
    directJumpPerturbation_time_lipschitz_iff _ x,
    fun t => directJumpPerturbation_Gaussian_not_operator_differentiableAt a t x⟩

/-- Cauchy compression preserves the Gaussian example's positive optimal constant and failure of operator-norm differentiability. -/
theorem directCauchyOperator_Gaussian_sharp_lipschitz_nowhere_differentiable (a x : ℝ) :
    0 < ‖directJumpTimeOperator (compatibilityGaussian a) 0 0‖ ∧
    (∀ L : ℝ, (∀ s v,
      ‖directCauchyOperator (compatibilityGaussian a) s x -
        directCauchyOperator (compatibilityGaussian a) v x‖ ≤ L * ‖s-v‖) ↔
      ‖directJumpTimeOperator (compatibilityGaussian a) 0 0‖ ≤ L) ∧
    (∀ t : ℝ, ¬ DifferentiableAt ℝ
      (fun s => directCauchyOperator (compatibilityGaussian a) s x) t) :=
  ⟨norm_directJumpTimeOperator_Gaussian_pos a,
    directCauchyOperator_time_lipschitz_iff _ x,
    fun t => (directCauchyOperator_Gaussian_strong_not_operator_derivative a t x).2⟩

end
end RHTower.FokasLenells
