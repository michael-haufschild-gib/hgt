import GaloisForLFunctions.HTGeometry.UnitaryFlowSmoothing
import GaloisForLFunctions.HTGeometry.TestFunctionL1Bound

/-!
# Smoothing a unitary flow against a complex weight

The modulated weights `φ_x(t) = exp(-i x t) φ₀(t)` of the temperedness argument are complex even
when `φ₀` is real, so the smoothing has to accept complex weights.  Its operator norm is bounded
by the `L¹` norm of the weight, exactly as in the real case, and on the test space that is
bounded by the order-zero seminorm.

* `cFlowSmoothing` : the smoothing against a complex weight.
* `norm_cFlowSmoothing_le` : the `L¹` operator bound.
* `norm_cFlowSmoothing_le_seminorm` : the bound by the test-space seminorm.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

section ComplexSmoothing

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [NormedSpace ℝ H] [CompleteSpace H]

/-- The smoothing of a unitary flow against a complex weight. -/
noncomputable def cFlowSmoothing (U : UnitaryFlow ℂ H) (phi : ℝ → ℂ) (x : H) : H :=
  ∫ t, phi t • U.op t x

omit [CompleteSpace H] in
/-- **The `L¹` operator bound for the complex smoothing.** -/
theorem norm_cFlowSmoothing_le (U : UnitaryFlow ℂ H) (phi : ℝ → ℂ) (x : H) :
    ‖cFlowSmoothing U phi x‖ ≤ (∫ t, ‖phi t‖) * ‖x‖ := by
  refine le_trans (norm_integral_le_integral_norm _) (le_of_eq ?_)
  have hpt : ∀ t : ℝ, ‖phi t • U.op t x‖ = ‖phi t‖ * ‖x‖ := by
    intro t
    rw [norm_smul, (U.op t).norm_map]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_mul_const]

omit [CompleteSpace H] in
/-- **The bound by the test-space seminorm.**  On test functions supported in a compact set the
operator norm of the smoothing is controlled by the supremum of the weight. -/
theorem norm_cFlowSmoothing_le_seminorm (U : UnitaryFlow ℂ H) {J : Set ℝ} (hJ : IsCompact J)
    {phi : ℝ → ℂ} (hphi : phi ∈ deningerTestSpace J) (x : H) :
    ‖cFlowSmoothing U phi x‖
      ≤ ((MeasureTheory.volume J).toReal * deningerTestSupNorm 0 phi) * ‖x‖ := by
  refine le_trans (norm_cFlowSmoothing_le U phi x) ?_
  exact mul_le_mul_of_nonneg_right (deningerTest_integral_norm_le hJ hphi) (norm_nonneg x)

omit [CompleteSpace H] in
/-- The complex smoothing is additive in the weight. -/
theorem cFlowSmoothing_add_weight (U : UnitaryFlow ℂ H) {J : Set ℝ} (hJ : IsCompact J)
    {phi psi : ℝ → ℂ} (hphi : phi ∈ deningerTestSpace J) (hpsi : psi ∈ deningerTestSpace J)
    (x : H) :
    cFlowSmoothing U (phi + psi) x = cFlowSmoothing U phi x + cFlowSmoothing U psi x := by
  have hint : ∀ {chi : ℝ → ℂ}, chi ∈ deningerTestSpace J →
      Integrable (fun t => chi t • U.op t x) := by
    intro chi hchi
    have hcont : Continuous fun t => chi t • U.op t x := by
      have h1 : Continuous chi := by
        have := continuous_iteratedDeriv_of_mem hchi 0
        simpa [iteratedDeriv_zero] using this
      exact h1.smul (U.continuous_orbit x)
    refine hcont.integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.intro (hasCompactSupport_of_mem hJ hchi).isCompact ?_
    intro t ht
    have hzero : chi t = 0 := by
      by_contra hne
      exact ht (subset_tsupport chi hne)
    rw [hzero, zero_smul]
  rw [cFlowSmoothing, cFlowSmoothing, cFlowSmoothing]
  have hsplit : ∀ t, (phi + psi) t • U.op t x = phi t • U.op t x + psi t • U.op t x := by
    intro t
    rw [Pi.add_apply, add_smul]
  rw [integral_congr_ae (Filter.Eventually.of_forall hsplit)]
  exact integral_add (hint hphi) (hint hpsi)

end ComplexSmoothing

end GaloisForLFunctions.HTGeometry
