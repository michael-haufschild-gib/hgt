import GaloisForLFunctions.BiScaleUncertainty.NyquistWeightCellAsymptotic
import GaloisForLFunctions.BiScaleUncertainty.NyquistResidualPartition

/-! # The actual positive Nyquist residual kernel and its integrability threshold -/

open Set Filter Topology MeasureTheory
open scoped BigOperators

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

def nyquistWeightKernel (β : ℝ) (m N : ℕ) (x : ℝ) : ℝ :=
  ∑' k : ℕ, (nyquistResidualCell (N + k)).indicator (nyquistWeightCellResidual β m (N + k)) x

theorem measurable_nyquistWeightKernel (β : ℝ) (m N : ℕ) :
    Measurable (nyquistWeightKernel β m N) :=
  Measurable.tsum (fun k => (continuous_nyquistWeightCellResidual β m (N + k)).measurable.indicator
    (measurableSet_nyquistResidualCell (N + k)))

theorem nyquistWeightKernel_on_cell (β : ℝ) (m N k : ℕ) {x : ℝ}
    (hx : x ∈ nyquistResidualCell (N + k)) :
    nyquistWeightKernel β m N x = nyquistWeightCellResidual β m (N + k) x := by
  unfold nyquistWeightKernel
  rw [tsum_eq_single k]
  · exact indicator_of_mem hx _
  · intro j hj
    apply indicator_of_notMem
    intro hjx
    exact (disjoint_left.mp (pairwise_disjoint_nyquistResidualCell
      (by omega : N + j ≠ N + k))) hjx hx

theorem nyquistWeightKernel_eq_zero (β : ℝ) (m N : ℕ) {x : ℝ}
    (hx : x ≤ nyquistResidualNode N) : nyquistWeightKernel β m N x = 0 := by
  unfold nyquistWeightKernel
  have hz (k : ℕ) : (nyquistResidualCell (N + k)).indicator
      (nyquistWeightCellResidual β m (N + k)) x = 0 := by
    apply indicator_of_notMem
    intro hk
    have hh := strictMono_nyquistResidualNode.monotone (Nat.le_add_right N k)
    exact (not_lt_of_ge (hx.trans hh)) hk.1
  rw [tsum_eq_single 0 (fun k _ => hz k), hz 0]

theorem nyquistWeightKernel_nonneg {β : ℝ} (hβ : 0 ≤ β) (m N : ℕ) (x : ℝ) :
    0 ≤ nyquistWeightKernel β m N x := by
  apply tsum_nonneg
  intro k
  by_cases hx : x ∈ nyquistResidualCell (N + k)
  · rw [indicator_of_mem hx]
    exact nyquistWeightCellResidual_nonneg hβ m (N + k) hx.1.le
  · rw [indicator_of_notMem hx]

theorem nyquistWeightKernel_indicator (β : ℝ) (m N : ℕ) :
    (Ioi (nyquistResidualNode N)).indicator (nyquistWeightKernel β m N) =
      nyquistWeightKernel β m N := by
  funext x
  by_cases hx : x ∈ Ioi (nyquistResidualNode N)
  · exact indicator_of_mem hx _
  · rw [indicator_of_notMem hx, nyquistWeightKernel_eq_zero β m N (le_of_not_gt hx)]

theorem nyquistWeightKernel_eq_tail_indicator (β : ℝ) (m N : ℕ) :
    nyquistWeightKernel β m N =
      (Ioi (nyquistResidualNode N)).indicator (nyquistWeightKernel β m 0) := by
  funext x
  by_cases hx : x ∈ Ioi (nyquistResidualNode N)
  · rw [indicator_of_mem hx]
    obtain ⟨k, hk⟩ := mem_iUnion.mp ((iUnion_nyquistResidualCell N).symm ▸ hx)
    rw [nyquistWeightKernel_on_cell β m N k hk]
    simpa only [Nat.zero_add] using
      (nyquistWeightKernel_on_cell β m 0 (N + k) (by simpa only [Nat.zero_add] using hk)).symm
  · rw [indicator_of_notMem hx, nyquistWeightKernel_eq_zero β m N (le_of_not_gt hx)]

theorem nyquistWeightTaylor_nonneg {β a x : ℝ} (hβ : 0 ≤ β) (ha : 0 ≤ a)
    (hax : a ≤ x) (m : ℕ) : 0 ≤ nyquistWeightTaylor β m a x := by
  unfold nyquistWeightTaylor
  apply Finset.sum_nonneg
  intro j _
  exact div_nonneg (mul_nonneg (nyquistWeightJet_nonneg hβ ha j)
    (pow_nonneg (sub_nonneg.mpr hax) _)) (Nat.cast_nonneg _)

theorem nyquistWeightKernel_le_weight {β : ℝ} (hβ : 0 ≤ β) (m N : ℕ) (x : ℝ) :
    nyquistWeightKernel β m N x ≤ nyquistWeight β x := by
  by_cases hx : x ∈ Ioi (nyquistResidualNode N)
  · obtain ⟨k, hk⟩ := mem_iUnion.mp ((iUnion_nyquistResidualCell N).symm ▸ hx)
    rw [nyquistWeightKernel_on_cell β m N k hk]
    exact sub_le_self _ (nyquistWeightTaylor_nonneg hβ (nyquistResidualNode_nonneg (N + k))
      hk.1.le m)
  · rw [nyquistWeightKernel_eq_zero β m N (le_of_not_gt hx)]
    exact (Real.cosh_pos _).le

theorem nyquistWeightKernel_zero_parameter (m N : ℕ) :
    nyquistWeightKernel 0 m N = fun _ => 0 := by
  funext x
  have hz (k : ℕ) : (nyquistResidualCell (N + k)).indicator
      (nyquistWeightCellResidual 0 m (N + k)) x = 0 := by
    by_cases hx : x ∈ nyquistResidualCell (N + k)
    · rw [indicator_of_mem hx, nyquistWeightCellResidual_zero_parameter]
    · exact indicator_of_notMem hx _
  rw [nyquistWeightKernel, tsum_eq_single 0 (fun k _ => hz k), hz 0]

/-- Compact inputs remain integrable even when the unrestricted tail mass is infinite. -/
theorem integrable_compact_mul_nyquistWeightKernel {β : ℝ} (hβ : 0 ≤ β) (m N : ℕ)
    {H : ℝ → ℝ} (hH : Continuous H) (hHc : HasCompactSupport H) :
    Integrable (fun x => H x * nyquistWeightKernel β m N x) := by
  have hc : Continuous (fun x => H x * nyquistWeight β x) :=
    hH.mul (contDiff_nyquistWeight β 1).continuous
  have hs : HasCompactSupport (fun x => H x * nyquistWeight β x) := hHc.mul_right
  apply (hc.integrable_of_hasCompactSupport hs).norm.mono'
    (hH.aestronglyMeasurable.mul (measurable_nyquistWeightKernel β m N).aestronglyMeasurable)
  filter_upwards with x
  change ‖H x * nyquistWeightKernel β m N x‖ ≤ ‖H x * nyquistWeight β x‖
  have hw : 0 ≤ nyquistWeight β x := (Real.cosh_pos _).le
  simp only [norm_mul, Real.norm_eq_abs,
    abs_of_nonneg (nyquistWeightKernel_nonneg hβ m N x), abs_of_nonneg hw]
  exact mul_le_mul_of_nonneg_left (nyquistWeightKernel_le_weight hβ m N x) (abs_nonneg _)

theorem integrableOn_nyquistWeightKernel_cell (β : ℝ) (m N k : ℕ) :
    IntegrableOn (nyquistWeightKernel β m N) (nyquistResidualCell (N + k)) := by
  apply (continuous_nyquistWeightCellResidual β m (N + k)).integrableOn_Ioc.congr_fun
    (fun x hx => (nyquistWeightKernel_on_cell β m N k hx).symm)
    (measurableSet_nyquistResidualCell (N + k))

theorem integral_nyquistWeightKernel_cell (β : ℝ) (m N k : ℕ) :
    (∫ x in nyquistResidualCell (N + k), nyquistWeightKernel β m N x) =
      nyquistWeightCellMass β m (N + k) := by
  rw [nyquistWeightCellMass, nyquistWeightTaylorMass, intervalIntegral.integral_of_le
    (strictMono_nyquistResidualNode.monotone (by omega : N + k ≤ N + k + 1))]
  exact setIntegral_congr_fun (measurableSet_nyquistResidualCell (N + k))
    (fun x hx => nyquistWeightKernel_on_cell β m N k hx)

theorem integral_norm_nyquistWeightKernel_cell {β : ℝ} (hβ : 0 ≤ β) (m N k : ℕ) :
    (∫ x in nyquistResidualCell (N + k), ‖nyquistWeightKernel β m N x‖) =
      nyquistWeightCellMass β m (N + k) := by
  simp_rw [Real.norm_eq_abs, abs_of_nonneg (nyquistWeightKernel_nonneg hβ m N _)]
  exact integral_nyquistWeightKernel_cell β m N k

theorem integrable_nyquistWeightKernel_iff {β : ℝ} (hβ : 0 < β) (m N : ℕ) :
    Integrable (nyquistWeightKernel β m N) ↔ β < (m : ℝ) + 1 := by
  constructor
  · intro hi
    have hs := (hasSum_integral_iUnion (fun k => measurableSet_nyquistResidualCell (N + k))
      (fun i j hij => pairwise_disjoint_nyquistResidualCell (by omega : N + i ≠ N + j))
      hi.integrableOn).summable
    simp only [integral_nyquistWeightKernel_cell] at hs
    exact (summable_nyquistWeightCellMass_tail_iff hβ m N).mp hs
  · intro hlt
    have hs := (summable_nyquistWeightCellMass_tail_iff hβ m N).mpr hlt
    have hi := integrableOn_iUnion_of_summable_integral_norm
      (integrableOn_nyquistWeightKernel_cell β m N)
      (by simpa only [integral_norm_nyquistWeightKernel_cell hβ.le] using hs)
    rw [iUnion_nyquistResidualCell] at hi
    have hh := hi.integrable_indicator measurableSet_Ioi
    rwa [nyquistWeightKernel_indicator] at hh

theorem tendsto_sum_nyquistWeightCellMass_atTop {β : ℝ} (hβ : 0 < β) (m N : ℕ)
    (hcrit : (m : ℝ) + 1 ≤ β) :
    Tendsto (fun M => ∑ k ∈ Finset.range M, nyquistWeightCellMass β m (N + k)) atTop atTop := by
  apply (not_summable_iff_tendsto_nat_atTop_of_nonneg
    (fun k => nyquistWeightCellMass_nonneg hβ.le m (N + k))).mp
  rw [summable_nyquistWeightCellMass_tail_iff hβ m N]
  exact not_lt_of_ge hcrit

theorem integrable_nyquistWeightKernel_iff_nonneg {β : ℝ} (hβ : 0 ≤ β) (m N : ℕ) :
    Integrable (nyquistWeightKernel β m N) ↔ β < (m : ℝ) + 1 := by
  rcases eq_or_lt_of_le hβ with hzero | hpos
  · subst β
    rw [nyquistWeightKernel_zero_parameter]
    constructor
    · intro _
      positivity
    · intro _
      exact integrable_zero
  · exact integrable_nyquistWeightKernel_iff hpos m N

/-- Below the threshold this is the actual positive tail mass. -/
def nyquistWeightTailMass (β : ℝ) (m N : ℕ) : ℝ :=
  ∑' k : ℕ, nyquistWeightCellMass β m (N + k)

theorem nyquistWeightTailMass_nonneg {β : ℝ} (hβ : 0 ≤ β) (m N : ℕ) :
    0 ≤ nyquistWeightTailMass β m N :=
  tsum_nonneg (fun k => nyquistWeightCellMass_nonneg hβ m (N + k))

theorem integral_nyquistWeightKernel {β : ℝ} (hβ : 0 ≤ β) (m N : ℕ)
    (hlt : β < (m : ℝ) + 1) :
    (∫ x, nyquistWeightKernel β m N x) = nyquistWeightTailMass β m N := by
  calc
    _ = ∫ x in Ioi (nyquistResidualNode N), nyquistWeightKernel β m N x := by
      rw [← integral_indicator measurableSet_Ioi, nyquistWeightKernel_indicator]
    _ = ∫ x in ⋃ k : ℕ, nyquistResidualCell (N + k), nyquistWeightKernel β m N x := by
      rw [iUnion_nyquistResidualCell]
    _ = ∑' k : ℕ, ∫ x in nyquistResidualCell (N + k), nyquistWeightKernel β m N x :=
      integral_iUnion (fun k => measurableSet_nyquistResidualCell (N + k))
        (fun i j hij => pairwise_disjoint_nyquistResidualCell (by omega : N + i ≠ N + j))
        ((integrable_nyquistWeightKernel_iff_nonneg hβ m N).mpr hlt).integrableOn
    _ = nyquistWeightTailMass β m N := by
      simp only [integral_nyquistWeightKernel_cell, nyquistWeightTailMass]

theorem integral_norm_nyquistWeightKernel {β : ℝ} (hβ : 0 ≤ β) (m N : ℕ)
    (hlt : β < (m : ℝ) + 1) :
    (∫ x, ‖nyquistWeightKernel β m N x‖) = nyquistWeightTailMass β m N := by
  simp_rw [Real.norm_eq_abs, abs_of_nonneg (nyquistWeightKernel_nonneg hβ m N _)]
  exact integral_nyquistWeightKernel hβ m N hlt

end
end GaloisForLFunctions.BiScaleUncertainty
