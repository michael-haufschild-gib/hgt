import GaloisForLFunctions.HTGeometry.FiniteKMSDetailedBalance
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Thermal response, fluctuation defects and static noise

Constructed Hermitian probes discharge the existing detailed-balance assumptions. The
finite-band response defect vanishes exactly, while the identity channel retains positive
static fluctuation with zero commutator response.

Source: Singh, arXiv:2609.10571, section 6.2, equations (36)--(40).
-/

set_option autoImplicit false

open scoped BigOperators
namespace GaloisForLFunctions.HTGeometry.TraceDynamics
open _root_.HTGeometry Matrix
noncomputable section
variable {α : Type*} [Fintype α]

omit [Fintype α] in
/-- Hermitian thermal probes are constructed from raw matrices. -/
theorem symmetrizedMatrix_hermitian_entries (A : Matrix α α ℂ) (a b : α) :
    (A + Aᴴ) b a = star ((A + Aᴴ) a b) := by
  simp [Matrix.conjTranspose_apply, star_add, add_comm]

/-- A finite, zero-frequency-safe form of the fluctuation--dissipation relation. -/
theorem symmetrizedMatrix_fdt (β : ℝ) (E : α → ℝ) (A : Matrix α α ℂ) (a b : α) :
    finiteKMSCommutatorTransitionIntensity β E (A + Aᴴ) a b =
      Real.tanh (β * (E a - E b) / 2) *
        finiteKMSSymmetricTransitionIntensity β E (A + Aᴴ) a b :=
  finiteKMSCommutatorTransitionIntensity_eq_tanh_mul_symmetric β E (A + Aᴴ)
    (symmetrizedMatrix_hermitian_entries A) a b

/-- Every finitely weighted band of the constructed equilibrium residual vanishes. -/
theorem symmetrizedMatrix_fdt_band_defect (β : ℝ) (E : α → ℝ)
    (A : Matrix α α ℂ) (w : α → α → ℝ) :
    (∑ a, ∑ b, w a b ^ 2 *
      (finiteKMSCommutatorTransitionIntensity β E (A + Aᴴ) a b -
        Real.tanh (β * (E a - E b) / 2) *
          finiteKMSSymmetricTransitionIntensity β E (A + Aᴴ) a b) ^ 2) = 0 := by
  simp [symmetrizedMatrix_fdt]

/-- At infinite temperature every Hermitian transition has zero response. -/
theorem symmetrizedMatrix_infiniteTemperature_response (E : α → ℝ)
    (A : Matrix α α ℂ) (a b : α) :
    finiteKMSCommutatorTransitionIntensity 0 E (A + Aᴴ) a b = 0 := by
  rw [symmetrizedMatrix_fdt]
  simp

variable [DecidableEq α]

/-- A diagonal transition has a static noise contribution, even at nonzero temperature. -/
theorem identity_static_fluctuation (β : ℝ) (E : α → ℝ) (a : α) :
    finiteKMSSymmetricTransitionIntensity β E (1 : Matrix α α ℂ) a a =
      2 * finiteGibbsStateWeight β E a := by
  simp [finiteKMSSymmetricTransitionIntensity, finiteGibbsTransitionIntensity]
  ring

theorem identity_static_response (β : ℝ) (E : α → ℝ) (a : α) :
    finiteKMSCommutatorTransitionIntensity β E (1 : Matrix α α ℂ) a a = 0 := by
  simp [finiteKMSCommutatorTransitionIntensity]

/-- No scalar multiple of the diagonal response recovers its static fluctuation. -/
theorem identity_static_noise_not_response [Nonempty α]
    (β : ℝ) (E : α → ℝ) (a : α) (c : ℝ) :
    finiteKMSSymmetricTransitionIntensity β E (1 : Matrix α α ℂ) a a ≠
      c * finiteKMSCommutatorTransitionIntensity β E (1 : Matrix α α ℂ) a a := by
  rw [identity_static_fluctuation, identity_static_response, mul_zero]
  exact ne_of_gt (mul_pos (by norm_num) (finiteGibbsStateWeight_pos β E a))

/-- Summing the conserved identity's entire static fluctuation gives its exact total mass. -/
theorem identity_static_total_fluctuation [Nonempty α] (β : ℝ) (E : α → ℝ) :
    (∑ a, finiteKMSSymmetricTransitionIntensity β E (1 : Matrix α α ℂ) a a) = 2 := by
  simp_rw [identity_static_fluctuation]
  rw [← Finset.mul_sum, sum_finiteGibbsStateWeight_eq_one, mul_one]

end
end GaloisForLFunctions.HTGeometry.TraceDynamics
