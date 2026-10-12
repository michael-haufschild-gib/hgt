import GaloisForLFunctions.RHTower.PaperThetaL1Domain

/-! # Actual local regularity of the entire theta quantile family -/

noncomputable section

open MeasureTheory Set Filter Topology

namespace RHTower.PaperThetaEndpoint

open HedenmalmThetaSource HedenmalmQuantile GaloisForLFunctions.HTGeometry FourierLLogL

theorem differentiable_normalized_theta : Differentiable ℝ thetaSource.normalized := by
  exact (contDiff_thetaCuspFullSource.differentiable (by simp)).div_const _

/-- Strict positivity pays division by the original source at every finite coordinate. -/
theorem differentiable_flatQuotient (z : ℂ) : Differentiable ℝ (flatQuotient z) := by
  intro x
  have hρ := (differentiable_normalized_theta x).hasDerivAt.ofReal_comp.differentiableAt
  have hG := (hasDerivAt_flatPrimitiveMode_all z x).differentiableAt
  exact ((hG.const_mul (-(Complex.I * z))).sub hρ).div hρ
    (by exact_mod_cast (thetaSource.normalized_pos x).ne')

theorem differentiableAt_pullback (z : ℂ) (t : Ioo (0 : ℝ) 1) :
    DifferentiableAt ℝ (flatModePullback z) t.val :=
  (differentiable_flatQuotient z (thetaSource.quantileFun t.val)).comp t.val
    (hasDerivAt_quantileFun thetaSource t.property).differentiableAt

/-- The literal periodic representative is differentiable at every interior quantile point. -/
theorem differentiableAt_periodicMode (z : ℂ) (t : Ioo (0 : ℝ) 1) :
    DifferentiableAt ℝ (periodicMode z) t.val := by
  apply (differentiableAt_pullback z t).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds t.property.1 t.property.2] with y hy
  exact periodicMode_eq_pullback z ⟨y, hy⟩

/-- Local first-order cancellation is paid by the actual mode's derivative. -/
theorem periodicMode_local_difference_bound (z : ℂ) (t : Ioo (0 : ℝ) 1) :
    ∃ K δ : ℝ, 0 < K ∧ 0 < δ ∧ ∀ y : ℝ, |y| < δ →
      ‖periodicMode z (t.val-y) - periodicMode z t.val‖ ≤ K * |y| := by
  have hd : DifferentiableAt ℝ (fun y : ℝ => periodicMode z (t.val-y)) 0 := by
    have hs : DifferentiableAt ℝ (fun y : ℝ => t.val-y) (0 : ℝ) := by fun_prop
    have ho : DifferentiableAt ℝ (periodicMode z) (t.val-(0 : ℝ)) := by
      simpa only [sub_zero] using differentiableAt_periodicMode z t
    exact ho.comp 0 hs
  obtain ⟨K, hK, hb⟩ := hd.isBigO_sub.exists_pos
  obtain ⟨δ, hδ, hbound⟩ := Metric.eventually_nhds_iff.mp hb.bound
  refine ⟨K, δ, hK, hδ, fun y hy => ?_⟩
  simpa only [sub_zero, Real.norm_eq_abs] using hbound (by simpa [Real.dist_eq] using hy)

end RHTower.PaperThetaEndpoint
