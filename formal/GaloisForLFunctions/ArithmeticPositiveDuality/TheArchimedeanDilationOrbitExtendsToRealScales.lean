import GaloisForLFunctions.ArithmeticPositiveDuality.TheSuccessorSeesOnlyTheContinuousDilationSpectrum
import GaloisForLFunctions.ArithmeticPositiveDuality.ArchimedeanPositiveDefiniteFunctionsLiveOnTheKroneckerLine
import GaloisForLFunctions.HTGeometry.StationaryHilbertCurvesExtendFromDenseParameters
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion

/-!
# The archimedean dilation orbit extends to real scales

A finite archimedean dilation measure determines a stationary inner-product
kernel for the rational dilation orbit of the cyclic GNS vector. Density of
positive rational logarithms extends this orbit uniformly continuously to all
real scales, retaining its characteristic function and total mass. This does
not assert continuity of the full affine representation.
-/

open Complex MeasureTheory Filter Set Topology
open scoped InnerProductSpace

noncomputable section
namespace GaloisForLFunctions.ArithmeticPositiveDuality

/-- Logarithms of positive rationals are dense in the real line. -/
theorem denseRange_logPos : DenseRange logPos := by
  intro t
  exact mem_closure_of_tendsto (tendsto_log_ratApprox t)
    (Eventually.of_forall fun n => ⟨ratApprox t n, rfl⟩)

variable {φ : AffineGroupQ → ℂ} (hφ : IsPosDefOnGroup φ)
    (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hν : ∀ u : ℚˣ, 0 < (u : ℚ) → φ (dilation u) = ∫ γ, archChar γ u ∂ν)

include hν

omit [IsFiniteMeasure ν] in
lemma inner_rational_dilation_orbit (u v : posUnits) :
    ⟪affRep hφ (dilation (u : ℚˣ)) (affVec hφ),
      affRep hφ (dilation (v : ℚˣ)) (affVec hφ)⟫_ℂ =
        charFun ν (logPos v - logPos u) := by
  have hg : (dilation (u : ℚˣ))⁻¹ * dilation (v : ℚˣ) =
      dilation ((u⁻¹ * v : posUnits) : ℚˣ) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
  rw [inner_affRep, hg, hν _ (u⁻¹ * v).2, ← logPos_inv_mul u v, charFun_apply_real]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro γ
  simp only [archChar, logPos, mul_comm, mul_assoc]

/-- The cyclic dilation orbit extends to every real logarithmic scale with its original
characteristic-function kernel. No continuity of the whole affine representation is assumed. -/
theorem exists_real_dilation_orbit :
    ∃ V : ℝ → GNSHilbert (⟨φ, hφ⟩ : PosDefFn AffineGroupQ), UniformContinuous V ∧
      (∀ u : posUnits, V (logPos u) = affRep hφ (dilation (u : ℚˣ)) (affVec hφ)) ∧
      (∀ s t : ℝ, ⟪V s, V t⟫_ℂ = charFun ν (t - s)) ∧
      ∀ t : ℝ, ‖V t‖ ^ 2 = ν.real univ := by
  obtain ⟨V, hV, hres, hkernel⟩ :=
    GaloisForLFunctions.HTGeometry.exists_stationary_hilbert_extension_indexed
      logPos denseRange_logPos
      (fun u => affRep hφ (dilation (u : ℚˣ)) (affVec hφ))
      (charFun ν) continuous_charFun (inner_rational_dilation_orbit hφ ν hν)
  refine ⟨V, hV, hres, hkernel, fun t => ?_⟩
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), RCLike.re_to_complex, hkernel, sub_self,
    charFun_zero, Complex.ofReal_re]

#print axioms exists_real_dilation_orbit
end GaloisForLFunctions.ArithmeticPositiveDuality
