import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMGlobalAngularWeakResponse
import GaloisForLFunctions.RHTower.SelbergScatteringEntireSymbol
import GaloisForLFunctions.HTGeometry.CfcKernelPreservation
import GaloisForLFunctions.HTGeometry.BoundedPerturbedFriedrichsOperator

/-!
# Native modular operator for the entire Casimir transform

Start with the original modular form embedding `J` and covariance `B = J J†`.
The existing energy is `A = B⁻¹ = 1 − Δ_H`. Apply continuous functional calculus
to the reciprocal entire symbol to obtain `C = g(B)`. Kernel preservation proves
that `C` is injective and has dense range, even though its symbol tends to zero
at the spectral accumulation point. Define `T = C⁻¹ − 2` on the actual range of
`C`. This is the native reciprocal-calculus realization of `F(A − 1)`.

This file proves the full graph domain, self-adjointness, closedness, both inverse
identities, a bounded inverse at `−2`, and the quadratic-form lower bound `−1`.
All construction hypotheses are discharged for the original modular source.
No Xi eigenvector, approximate eigenvector, or occurrence theorem is asserted.
-/

open GaloisForLFunctions.HTGeometry
open RHTower.D4BMModularCore RHTower.SelbergScatteringEntireTransform
open scoped InnerProductSpace

namespace RHTower.SelbergScatteringEntireOperator
noncomputable section

local instance : IsometricContinuousFunctionalCalculus ℝ (Space →L[ℂ] Space) IsSelfAdjoint :=
  IsSelfAdjoint.instIsometricContinuousFunctionalCalculus

/-- Covariance of the original modular value-plus-gradient embedding. -/
def nativeCovariance : Space →L[ℂ] Space := formEmbeddingCovariance embedding

theorem nativeCovariance_injective : Function.Injective nativeCovariance :=
  formEmbeddingCovariance_injective embedding embedding_injective embedding_dense

theorem nativeCovariance_selfAdjoint : IsSelfAdjoint nativeCovariance :=
  formEmbeddingCovariance_isSelfAdjoint embedding

theorem nativeCovariance_nonneg : 0 ≤ nativeCovariance :=
  (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
    (ContinuousLinearMap.isPositive_self_comp_adjoint embedding)

/-- Exact identification with the previously constructed modular energy operator. -/
theorem nativeCovariance_energyOperator : closedDenseInverse nativeCovariance = energyOperator := rfl

/-- Bounded reciprocal of the entire transform, constructed from the original source. -/
def entireCovariance : Space →L[ℂ] Space := cfc entireCovarianceSymbol nativeCovariance

theorem entireCovariance_selfAdjoint : IsSelfAdjoint entireCovariance := IsSelfAdjoint.cfc

private theorem symbol_no_new_spectral_zeros :
    ∀ x ∈ spectrum ℝ nativeCovariance, entireCovarianceSymbol x = 0 → x = 0 := by
  intro x hx hzero
  exact le_antisymm ((entireCovarianceSymbol_zero_iff x).mp hzero)
    (spectrum_nonneg_of_nonneg nativeCovariance_nonneg hx)

theorem entireCovariance_injective : Function.Injective entireCovariance :=
  cfc_injective_of_no_new_zeros nativeCovariance nativeCovariance_selfAdjoint
    nativeCovariance_injective entireCovarianceSymbol continuous_entireCovarianceSymbol.continuousOn
    symbol_no_new_spectral_zeros

theorem entireCovariance_dense_range : Dense (entireCovariance.range : Set Space) :=
  cfc_dense_range_of_no_new_zeros nativeCovariance nativeCovariance_selfAdjoint
    nativeCovariance_injective entireCovarianceSymbol continuous_entireCovarianceSymbol.continuousOn
    symbol_no_new_spectral_zeros

theorem entireCovariance_nonneg : 0 ≤ entireCovariance :=
  cfc_nonneg (fun x _ => entireCovarianceSymbol_nonneg x)

theorem entireCovariance_norm_le : ‖entireCovariance‖ ≤ 1 := by
  nontriviality Space
  apply norm_cfc_le_of_forall_le entireCovarianceSymbol nativeCovariance
    continuous_entireCovarianceSymbol.continuousOn nativeCovariance_selfAdjoint
  intro x _
  simpa only [Real.norm_eq_abs, abs_of_nonneg (entireCovarianceSymbol_nonneg x)] using
    entireCovarianceSymbol_le_one x

/-- Native unbounded realization of `F(A - 1)`, with domain the range of its reciprocal. -/
def entireOperator : Space →ₗ.[ℂ] Space :=
  boundedShift (closedDenseInverse entireCovariance) ((-2 : ℂ) • (1 : Space →L[ℂ] Space))

theorem entireOperator_domain : entireOperator.domain = entireCovariance.range :=
  closedDenseInverse_domain entireCovariance

theorem entireOperator_dense_domain : Dense (entireOperator.domain : Set Space) := by
  rw [entireOperator_domain]
  exact entireCovariance_dense_range

theorem entireOperator_selfAdjoint : IsSelfAdjoint entireOperator := by
  apply boundedShift_isSelfAdjoint
  · exact closedDenseInverse_isSelfAdjoint entireCovariance entireCovariance_injective
      entireCovariance_dense_range entireCovariance_selfAdjoint
  · apply IsSelfAdjoint.smul
    · norm_num [IsSelfAdjoint]
    · simp [IsSelfAdjoint]

theorem entireOperator_isClosed : entireOperator.IsClosed := entireOperator_selfAdjoint.isClosed

/-- Every original Hilbert vector yields an explicit vector in the transformed graph domain. -/
theorem entireCovariance_mem_domain (y : Space) : entireCovariance y ∈ entireOperator.domain := by
  rw [entireOperator_domain]
  exact ⟨y, rfl⟩

/-- Exact action on the constructed domain; no occurrence hypothesis is used. -/
theorem entireOperator_apply_covariance (y : Space) :
    entireOperator ⟨entireCovariance y, entireCovariance_mem_domain y⟩ =
      y - (2 : ℂ) • entireCovariance y := by
  change closedDenseInverse entireCovariance ⟨entireCovariance y, _⟩ +
    (-2 : ℂ) • entireCovariance y = _
  rw [(closedDenseInverse_apply_C entireCovariance entireCovariance_injective y).2]
  simp only [neg_smul, sub_eq_add_neg]

/-- The bounded covariance is exactly `(entireOperator + 2)⁻¹` on its full domain. -/
theorem entireCovariance_apply_operator (x : entireOperator.domain) :
    entireCovariance (entireOperator x + (2 : ℂ) • (x : Space)) = (x : Space) := by
  change entireCovariance (closedDenseInverse entireCovariance x +
    (-2 : ℂ) • (x : Space) + (2 : ℂ) • (x : Space)) = _
  simp only [neg_smul, add_assoc, neg_add_cancel, add_zero]
  exact closedDenseInverse_C_apply entireCovariance entireCovariance_injective x

/-- The transformed graph has an actual everywhere-defined bounded inverse at the real shift `−2`. -/
theorem entireOperator_shift_bijective : Function.Bijective (shiftedMap entireOperator (-2)) := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    rw [← entireCovariance_apply_operator x, ← entireCovariance_apply_operator y]
    apply congrArg entireCovariance
    change entireOperator x - (-2 : ℂ) • (x : Space) =
      entireOperator y - (-2 : ℂ) • (y : Space) at hxy
    simpa only [neg_smul, sub_neg_eq_add] using hxy
  · intro y
    refine ⟨⟨entireCovariance y, entireCovariance_mem_domain y⟩, ?_⟩
    change entireOperator ⟨entireCovariance y, entireCovariance_mem_domain y⟩ -
      (-2 : ℂ) • entireCovariance y = y
    rw [entireOperator_apply_covariance]
    simp only [neg_smul, sub_neg_eq_add, sub_add_cancel]

/-- Resolvent norm bound in the actual graph domain. -/
theorem entireOperator_shift_norm_lower (x : entireOperator.domain) :
    ‖(x : Space)‖ ≤ ‖entireOperator x + (2 : ℂ) • (x : Space)‖ := by
  calc
    ‖(x : Space)‖ = ‖entireCovariance (entireOperator x + (2 : ℂ) • (x : Space))‖ :=
      congrArg norm (entireCovariance_apply_operator x).symm
    _ ≤ ‖entireCovariance‖ * ‖entireOperator x + (2 : ℂ) • (x : Space)‖ :=
      entireCovariance.le_opNorm _
    _ ≤ 1 * ‖entireOperator x + (2 : ℂ) • (x : Space)‖ :=
      mul_le_mul_of_nonneg_right entireCovariance_norm_le (norm_nonneg _)
    _ = _ := one_mul _

/-- The actual transformed operator has the unconditional quadratic-form lower bound `−1`. -/
theorem entireOperator_re_inner_lower (x : entireOperator.domain) :
    -‖(x : Space)‖ ^ (2 : ℕ) ≤ (inner ℂ (entireOperator x) (x : Space)).re := by
  classical
  by_cases hsub : Subsingleton Space
  · letI := hsub
    rw [Subsingleton.elim (x : Space) 0]
    simp
  letI : Nontrivial Space := not_subsingleton_iff_nontrivial.mp hsub
  have hpos : 0 < ‖entireCovariance‖ := by
    apply norm_pos_iff.mpr
    intro hz
    obtain ⟨y, hy⟩ := exists_ne (0 : Space)
    apply hy
    apply entireCovariance_injective
    simp [hz]
  have hinv : 1 ≤ ‖entireCovariance‖⁻¹ :=
    (one_le_inv₀ hpos).mpr entireCovariance_norm_le
  have hlower := closedDenseInverse_re_inner_lower entireCovariance entireCovariance_injective
    ((ContinuousLinearMap.nonneg_iff_isPositive _).mp entireCovariance_nonneg) x
  have hnorm := mul_le_mul_of_nonneg_right hinv (sq_nonneg ‖(x : Space)‖)
  change -‖(x : Space)‖ ^ (2 : ℕ) ≤
    (inner ℂ (closedDenseInverse entireCovariance x + (-2 : ℂ) • (x : Space)) (x : Space)).re
  rw [inner_add_left, inner_smul_left, inner_self_eq_norm_sq_to_K]
  norm_num [← Complex.ofReal_pow, Complex.mul_re]
  nlinarith

end
end RHTower.SelbergScatteringEntireOperator
