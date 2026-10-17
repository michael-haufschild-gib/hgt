import GaloisForLFunctions.BiScaleUncertainty.NyquistWeightOperator
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Explicit signed Taylor moments and the exact all-tail producer identity -/

open Set Filter Topology MeasureTheory
open scoped BigOperators BoundedContinuousFunction

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

def nyquistWeightCellMoment (H : ℝ →ᵇ ℝ) (j k : ℕ) : ℝ :=
  ∫ x in nyquistResidualCell k, H x * (x - nyquistResidualNode k) ^ j

def nyquistWeightProducedCell (β : ℝ) (m : ℕ) (H : ℝ →ᵇ ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (m + 1), nyquistWeightJet β j (nyquistResidualNode k) /
    (j.factorial : ℝ) * nyquistWeightCellMoment H j k

def nyquistWeightCellError (β : ℝ) (m : ℕ) (H : ℝ →ᵇ ℝ) (k : ℕ) : ℝ :=
  ∫ x in nyquistResidualCell k, H x * nyquistWeightCellResidual β m k x

def nyquistWeightProducer (β : ℝ) (m N : ℕ) (H : ℝ →ᵇ ℝ) : ℝ :=
  ∑' k : ℕ, nyquistWeightProducedCell β m H (N + k)

def nyquistWeightPolarTail (β : ℝ) (N : ℕ) (H : ℝ →ᵇ ℝ) : ℝ :=
  ∫ x in Ioi (nyquistResidualNode N), H x * nyquistWeight β x

theorem integral_nyquistWeightTaylor_mul (β : ℝ) (m k : ℕ) (H : ℝ →ᵇ ℝ) :
    (∫ x in nyquistResidualCell k, H x * nyquistWeightTaylor β m (nyquistResidualNode k) x) =
      nyquistWeightProducedCell β m H k := by
  have he : (fun x => H x * nyquistWeightTaylor β m (nyquistResidualNode k) x) =
      fun x => ∑ j ∈ Finset.range (m + 1),
        (nyquistWeightJet β j (nyquistResidualNode k) / (j.factorial : ℝ)) *
          (H x * (x - nyquistResidualNode k) ^ j) := by
    funext x
    unfold nyquistWeightTaylor
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he, integral_finsetSum]
  · simp only [integral_const_mul]
    rfl
  · intro j _
    exact ((H.continuous.mul ((continuous_id.sub continuous_const).pow j)).const_mul
      (nyquistWeightJet β j (nyquistResidualNode k) / (j.factorial : ℝ))).integrableOn_Ioc

theorem integral_nyquistWeight_cell_decomposition (β : ℝ) (m k : ℕ) (H : ℝ →ᵇ ℝ) :
    (∫ x in nyquistResidualCell k, H x * nyquistWeight β x) =
      nyquistWeightProducedCell β m H k + nyquistWeightCellError β m H k := by
  have he : (fun x => H x * nyquistWeight β x) = fun x =>
      H x * nyquistWeightTaylor β m (nyquistResidualNode k) x +
        H x * nyquistWeightCellResidual β m k x := by
    funext x
    dsimp [nyquistWeightCellResidual, nyquistWeightTaylorResidual]
    ring
  rw [he, integral_add]
  · rw [integral_nyquistWeightTaylor_mul]
    rfl
  · exact (H.continuous.mul
      (contDiff_nyquistWeightTaylor β m (nyquistResidualNode k) 1).continuous).integrableOn_Ioc
  · exact (H.continuous.mul (continuous_nyquistWeightCellResidual β m k)).integrableOn_Ioc

theorem nyquistWeightCellError_eq_integral_kernel (β : ℝ) (m N k : ℕ) (H : ℝ →ᵇ ℝ) :
    nyquistWeightCellError β m H (N + k) =
      ∫ x in nyquistResidualCell (N + k), H x * nyquistWeightKernel β m N x := by
  apply setIntegral_congr_fun (measurableSet_nyquistResidualCell (N + k))
  intro x hx
  change H x * nyquistWeightCellResidual β m (N + k) x = H x * nyquistWeightKernel β m N x
  rw [nyquistWeightKernel_on_cell β m N k hx]

theorem hasSum_nyquistWeightCellError_of_integrable (β : ℝ) (m N : ℕ) (H : ℝ →ᵇ ℝ)
    (hi : Integrable (fun x => H x * nyquistWeightKernel β m N x)) :
    HasSum (fun k => nyquistWeightCellError β m H (N + k))
      (∫ x, H x * nyquistWeightKernel β m N x) := by
  have hs := hasSum_integral_iUnion
    (fun k : ℕ => measurableSet_nyquistResidualCell (N + k))
    (fun i j hij => pairwise_disjoint_nyquistResidualCell (by omega : N + i ≠ N + j))
    hi.integrableOn
  have hind : (Ioi (nyquistResidualNode N)).indicator
      (fun x => H x * nyquistWeightKernel β m N x) =
      (fun x => H x * nyquistWeightKernel β m N x) := by
    simpa only [smul_eq_mul, nyquistWeightKernel_indicator] using
      indicator_smul (Ioi (nyquistResidualNode N)) (fun x => H x) (nyquistWeightKernel β m N)
  rw [iUnion_nyquistResidualCell, ← integral_indicator measurableSet_Ioi, hind] at hs
  simpa only [nyquistWeightCellError_eq_integral_kernel β m N] using hs

theorem hasSum_nyquistWeightCellError_compact {β : ℝ} (hβ : 0 ≤ β) (m N : ℕ)
    (H : ℝ →ᵇ ℝ) (hH : HasCompactSupport (⇑H)) :
    HasSum (fun k => nyquistWeightCellError β m H (N + k))
      (∫ x, H x * nyquistWeightKernel β m N x) :=
  hasSum_nyquistWeightCellError_of_integrable β m N H
    (integrable_compact_mul_nyquistWeightKernel hβ m N H.continuous hH)

theorem hasSum_nyquistWeightCellError {β : ℝ} (hβ : 0 ≤ β) (m N : ℕ)
    (hlt : β < (m : ℝ) + 1) (H : ℝ →ᵇ ℝ) :
    HasSum (fun k => nyquistWeightCellError β m H (N + k))
      (nyquistWeightOperator hβ m N hlt H) :=
  hasSum_nyquistWeightCellError_of_integrable β m N H
    (integrable_mul_nyquistWeightKernel hβ m N hlt H)

theorem summable_norm_nyquistWeightCellError {β : ℝ} (hβ : 0 ≤ β) (m N : ℕ)
    (hlt : β < (m : ℝ) + 1) (H : ℝ →ᵇ ℝ) :
    Summable (fun k => ‖nyquistWeightCellError β m H (N + k)‖) :=
  (hasSum_nyquistWeightCellError hβ m N hlt H).summable.norm

theorem nyquistWeightProducedCell_eventually_zero (β : ℝ) (m : ℕ) (H : ℝ →ᵇ ℝ)
    (hH : HasCompactSupport (⇑H)) :
    ∃ M : ℕ, ∀ k : ℕ, M ≤ k →
      nyquistWeightProducedCell β m H k = 0 ∧ nyquistWeightCellError β m H k = 0 := by
  obtain ⟨R, _, hz⟩ := hH.exists_pos_le_norm
  obtain ⟨M, hM⟩ := (tendsto_nyquistResidualNode.eventually (eventually_ge_atTop R)).exists
  refine ⟨M, ?_⟩
  intro k hk
  have hzero (x : ℝ) (hx : x ∈ nyquistResidualCell k) : H x = 0 := by
    apply hz
    rw [Real.norm_eq_abs]
    exact (hM.trans (strictMono_nyquistResidualNode.monotone hk)).trans
      (hx.1.le.trans (le_abs_self x))
  have hzmul (f : ℝ → ℝ) : (∫ x in nyquistResidualCell k, H x * f x) = 0 := by
    calc
      _ = ∫ _x in nyquistResidualCell k, (0 : ℝ) := by
        apply setIntegral_congr_fun (measurableSet_nyquistResidualCell k)
        intro x hx
        change H x * f x = 0
        rw [hzero x hx, zero_mul]
      _ = 0 := by simp
  constructor
  · rw [← integral_nyquistWeightTaylor_mul]
    exact hzmul _
  · exact hzmul _

theorem hasSum_nyquistWeightProducedCell {β : ℝ} (hβ : 0 ≤ β) (m N : ℕ)
    (H : ℝ →ᵇ ℝ) (hH : HasCompactSupport (⇑H)) :
    HasSum (fun k => nyquistWeightProducedCell β m H (N + k))
      (nyquistWeightPolarTail β N H - ∫ x, H x * nyquistWeightKernel β m N x) := by
  have hi : Integrable (fun x => H x * nyquistWeight β x) :=
    (H.continuous.mul (contDiff_nyquistWeight β 1).continuous).integrable_of_hasCompactSupport
      hH.mul_right
  have hs := hasSum_integral_iUnion
    (fun k : ℕ => measurableSet_nyquistResidualCell (N + k))
    (fun i j hij => pairwise_disjoint_nyquistResidualCell (by omega : N + i ≠ N + j))
    hi.integrableOn
  rw [iUnion_nyquistResidualCell] at hs
  have hh := hs.sub (hasSum_nyquistWeightCellError_compact hβ m N H hH)
  simpa only [integral_nyquistWeight_cell_decomposition β m, add_sub_cancel_right,
    nyquistWeightPolarTail] using hh

theorem nyquistWeightPolarTail_decomposition {β : ℝ} (hβ : 0 ≤ β) (m N : ℕ)
    (H : ℝ →ᵇ ℝ) (hH : HasCompactSupport (⇑H)) :
    nyquistWeightPolarTail β N H = nyquistWeightProducer β m N H +
      ∫ x, H x * nyquistWeightKernel β m N x := by
  have hs := (hasSum_nyquistWeightProducedCell hβ m N H hH).tsum_eq
  change nyquistWeightProducer β m N H = _ at hs
  linarith

theorem nyquistWeightProducer_error_le {β : ℝ} (hβ : 0 < β) (m N : ℕ)
    (hlt : β < (m : ℝ) + 1) (H : ℝ →ᵇ ℝ) (hH : HasCompactSupport (⇑H)) :
    |nyquistWeightPolarTail β N H - nyquistWeightProducer β m N H| ≤
      nyquistWeightTailBound β m N * ‖H‖ := by
  rw [nyquistWeightPolarTail_decomposition hβ.le m N H hH, add_sub_cancel_left]
  exact (integral_mul_nyquistWeightKernel_le hβ.le m N hlt H).trans
    (mul_le_mul_of_nonneg_right (nyquistWeightTailMass_le hβ m N hlt) (norm_nonneg H))

theorem nyquistWeightOperator_abs_sub_le {β : ℝ} (hβ : 0 ≤ β) (m N : ℕ)
    (hlt : β < (m : ℝ) + 1) (H G : ℝ →ᵇ ℝ) :
    |nyquistWeightOperator hβ m N hlt H - nyquistWeightOperator hβ m N hlt G| ≤
      nyquistWeightTailMass β m N * ‖H - G‖ := by
  rw [← map_sub]
  exact integral_mul_nyquistWeightKernel_le hβ m N hlt (H - G)

theorem nyquistWeightPolar_convergence_iff_producer {β : ℝ} (hβ : 0 ≤ β) (m N : ℕ)
    (hlt : β < (m : ℝ) + 1) {H : ℝ →ᵇ ℝ} {F : ℕ → ℝ →ᵇ ℝ}
    (hH : HasCompactSupport (⇑H)) (hF : ∀ n, HasCompactSupport (⇑(F n)))
    (hu : TendstoUniformly (fun n => ⇑(F n)) (⇑H) atTop) :
    Tendsto (fun n => nyquistWeightPolarTail β N (F n)) atTop (𝓝 (nyquistWeightPolarTail β N H)) ↔
      Tendsto (fun n => nyquistWeightProducer β m N (F n)) atTop
        (𝓝 (nyquistWeightProducer β m N H)) := by
  have hr : Tendsto (fun n => ∫ x, F n x * nyquistWeightKernel β m N x) atTop
      (𝓝 (∫ x, H x * nyquistWeightKernel β m N x)) :=
    (nyquistWeightOperator hβ m N hlt).continuous.tendsto H |>.comp
      (BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mpr hu)
  constructor
  · intro hp
    simpa only [nyquistWeightPolarTail_decomposition hβ m N H hH,
      nyquistWeightPolarTail_decomposition hβ m N (F _) (hF _), add_sub_cancel_right] using hp.sub hr
  · intro hq
    simpa only [← nyquistWeightPolarTail_decomposition hβ m N H hH,
      ← nyquistWeightPolarTail_decomposition hβ m N (F _) (hF _)] using hq.add hr

end
end GaloisForLFunctions.BiScaleUncertainty
