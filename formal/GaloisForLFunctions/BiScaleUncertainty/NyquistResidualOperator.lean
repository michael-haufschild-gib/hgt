import GaloisForLFunctions.BiScaleUncertainty.NyquistResidualKernel

/-! # The positive Nyquist residual operator and its exact norm -/

open MeasureTheory Set Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

def nyquistResidualOperator (N : ℕ) : (ℝ →ᵇ ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun H => ∫ x, H x * nyquistResidualKernel N x
      map_add' := by
        intro H G
        change (∫ x, (H x + G x) * nyquistResidualKernel N x) = _
        simp_rw [add_mul]
        exact integral_add (integrable_mul_nyquistResidualKernel N H)
          (integrable_mul_nyquistResidualKernel N G)
      map_smul' := by
        intro c H
        change (∫ x, (c * H x) * nyquistResidualKernel N x) =
          c * ∫ x, H x * nyquistResidualKernel N x
        simp_rw [mul_assoc]
        exact integral_const_mul _ _ }
    (nyquistResidualTailMass N) (integral_mul_nyquistResidualKernel_le N)

theorem nyquistResidualOperator_apply (N : ℕ) (H : ℝ →ᵇ ℝ) :
    nyquistResidualOperator N H = ∫ x, H x * nyquistResidualKernel N x := rfl

theorem nyquistResidualOperator_nonneg (N : ℕ) (H : ℝ →ᵇ ℝ)
    (hH : ∀ x, 0 ≤ H x) : 0 ≤ nyquistResidualOperator N H :=
  integral_nonneg (fun x => mul_nonneg (hH x) (nyquistResidualKernel_nonneg N x))

theorem nyquistResidualOperator_const_one (N : ℕ) :
    nyquistResidualOperator N (BoundedContinuousFunction.const ℝ (1 : ℝ)) =
      nyquistResidualTailMass N := by
  simp only [nyquistResidualOperator_apply, BoundedContinuousFunction.const_apply, one_mul,
    integral_nyquistResidualKernel]

theorem norm_nyquistResidualOperator (N : ℕ) :
    ‖nyquistResidualOperator N‖ = nyquistResidualTailMass N := by
  apply le_antisymm
  · exact (nyquistResidualOperator N).opNorm_le_bound (nyquistResidualTailMass_nonneg N)
      (integral_mul_nyquistResidualKernel_le N)
  · have hh := (nyquistResidualOperator N).unit_le_opNorm
      (x := BoundedContinuousFunction.const ℝ (1 : ℝ))
      (by simp only [BoundedContinuousFunction.norm_const_eq, norm_one, le_refl])
    simpa only [nyquistResidualOperator_const_one, Real.norm_eq_abs,
      abs_of_nonneg (nyquistResidualTailMass_nonneg N)] using hh

theorem norm_nyquistResidualOperator_le (N : ℕ) :
    ‖nyquistResidualOperator N‖ ≤ nyquistResidualTailScale N := by
  rw [norm_nyquistResidualOperator]
  exact nyquistResidualTailMass_le_scale N

theorem tendsto_norm_nyquistResidualOperator :
    Tendsto (fun N => ‖nyquistResidualOperator N‖) atTop (𝓝 0) := by
  simpa only [norm_nyquistResidualOperator] using tendsto_nyquistResidualTailMass

theorem nyquistResidualOperator_abs_le (N : ℕ) (H : ℝ →ᵇ ℝ) :
    |nyquistResidualOperator N H| ≤ nyquistResidualTailMass N * ‖H‖ :=
  integral_mul_nyquistResidualKernel_le N H

theorem nyquistResidualOperator_abs_le_scale (N : ℕ) (H : ℝ →ᵇ ℝ) :
    |nyquistResidualOperator N H| ≤ nyquistResidualTailScale N * ‖H‖ :=
  (nyquistResidualOperator_abs_le N H).trans
    (mul_le_mul_of_nonneg_right (nyquistResidualTailMass_le_scale N) (norm_nonneg H))

theorem nyquistResidualOperator_abs_sub_le (N : ℕ) (H G : ℝ →ᵇ ℝ) :
    |nyquistResidualOperator N H - nyquistResidualOperator N G| ≤
      nyquistResidualTailMass N * ‖H - G‖ := by
  rw [← map_sub]
  exact nyquistResidualOperator_abs_le N (H - G)

theorem tendsto_nyquistResidualOperator_of_uniform {H : ℝ →ᵇ ℝ}
    {F : ℕ → ℝ →ᵇ ℝ} (hF : TendstoUniformly (fun n => ⇑(F n)) (⇑H) atTop) (N : ℕ) :
    Tendsto (fun n => nyquistResidualOperator N (F n)) atTop
      (𝓝 (nyquistResidualOperator N H)) :=
  (nyquistResidualOperator N).continuous.tendsto H |>.comp
    (BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mpr hF)

def nyquistCellResidual (H : ℝ →ᵇ ℝ) (k : ℕ) : ℝ :=
  ∫ x in nyquistResidualCell k, H x * nyquistResidualDensity k x

theorem nyquistCellResidual_eq_integral_kernel (N k : ℕ) (H : ℝ →ᵇ ℝ) :
    nyquistCellResidual H (N + k) =
      ∫ x in nyquistResidualCell (N + k), H x * nyquistResidualKernel N x := by
  apply setIntegral_congr_fun (measurableSet_nyquistResidualCell (N + k))
  intro x hx
  rw [nyquistResidualKernel_on_cell N k hx]

theorem norm_nyquistCellResidual_le (H : ℝ →ᵇ ℝ) (k : ℕ) :
    ‖nyquistCellResidual H k‖ ≤ ‖H‖ * nyquistResidualMass k := by
  rw [show k = 0 + k from (Nat.zero_add k).symm, nyquistCellResidual_eq_integral_kernel]
  calc
    _ ≤ ∫ x in nyquistResidualCell (0 + k), ‖H‖ * nyquistResidualKernel 0 x :=
      norm_integral_le_of_norm_le
        ((integrable_nyquistResidualKernel 0).integrableOn.const_mul ‖H‖)
        (Eventually.of_forall fun x => by
          rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (nyquistResidualKernel_nonneg 0 x)]
          exact mul_le_mul_of_nonneg_right (H.norm_coe_le_norm x) (nyquistResidualKernel_nonneg 0 x))
    _ = _ := by rw [integral_const_mul, integral_nyquistResidualKernel_cell]

theorem summable_nyquistCellResidual (H : ℝ →ᵇ ℝ) (N : ℕ) :
    Summable (fun k => nyquistCellResidual H (N + k)) :=
  Summable.of_norm_bounded ((summable_nyquistResidualMass N).mul_left ‖H‖)
    (fun k => norm_nyquistCellResidual_le H (N + k))

theorem nyquistResidualOperator_eq_tsum (N : ℕ) (H : ℝ →ᵇ ℝ) :
    nyquistResidualOperator N H = ∑' k : ℕ, nyquistCellResidual H (N + k) := by
  have hi : (Ioi (nyquistResidualNode N)).indicator
      (fun x => H x * nyquistResidualKernel N x) =
      (fun x => H x * nyquistResidualKernel N x) := by
    simpa only [smul_eq_mul, nyquistResidualKernel_indicator] using
      indicator_smul (Ioi (nyquistResidualNode N)) (fun x => H x) (nyquistResidualKernel N)
  calc
    _ = ∫ x in Ioi (nyquistResidualNode N), H x * nyquistResidualKernel N x := by
      rw [← integral_indicator measurableSet_Ioi, hi]
      rfl
    _ = ∫ x in ⋃ k : ℕ, nyquistResidualCell (N + k), H x * nyquistResidualKernel N x := by
      rw [iUnion_nyquistResidualCell]
    _ = ∑' k : ℕ, ∫ x in nyquistResidualCell (N + k), H x * nyquistResidualKernel N x :=
      integral_iUnion (fun k => measurableSet_nyquistResidualCell (N + k))
        (fun i j hij => pairwise_disjoint_nyquistResidualCell (by omega : N + i ≠ N + j))
        (integrable_mul_nyquistResidualKernel N H).integrableOn
    _ = _ := by simp only [nyquistCellResidual_eq_integral_kernel N]

theorem nyquistResidualOperator_eq_tail_integral (N : ℕ) (H : ℝ →ᵇ ℝ) :
    nyquistResidualOperator N H =
      ∫ x in Ioi (nyquistResidualNode N), H x * nyquistResidualKernel 0 x := by
  rw [nyquistResidualOperator_apply, nyquistResidualKernel_eq_tail_indicator N,
    ← integral_indicator measurableSet_Ioi]
  congr 1
  simpa only [smul_eq_mul] using
    (indicator_smul (Ioi (nyquistResidualNode N)) (fun x => H x) (nyquistResidualKernel 0)).symm

end
end GaloisForLFunctions.BiScaleUncertainty
