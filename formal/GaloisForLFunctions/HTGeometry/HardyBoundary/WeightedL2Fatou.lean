import GaloisForLFunctions.HTGeometry.MultiplierClosedGraph
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Weighted Fatou bounds for strong L² limits

Almost-everywhere subsequences transfer nonnegative weighted energies to
strong limits. Two successive extractions retain a joint bound on the sum
of physical and transformed energies, including varying scalar bounds.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology


namespace GaloisForLFunctions.HTGeometry

/-- A uniformly bounded nonnegative integral remains finite under almost-everywhere convergence. -/
theorem integrable_and_integral_le_of_ae_limit
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : ℕ → α → ℝ} {g : α → ℝ}
    (hfi : ∀ n, Integrable (f n) μ) (hfnn : ∀ n, 0 ≤ᵐ[μ] f n)
    (hgm : AEStronglyMeasurable g μ) (hgnn : 0 ≤ᵐ[μ] g)
    (hae : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x)))
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ n, (∫ x, f n x ∂μ) ≤ M) :
    Integrable g μ ∧ (∫ x, g x ∂μ) ≤ M := by
  have hlim : (fun x => liminf (fun n => ENNReal.ofReal (f n x)) atTop) =ᵐ[μ]
      (fun x => ENNReal.ofReal (g x)) :=
    hae.mono fun x hx => ((ENNReal.continuous_ofReal.tendsto (g x)).comp hx).liminf_eq
  have hFatou := lintegral_liminf_le' (μ := μ) (u := atTop)
    (f := fun n x => ENNReal.ofReal (f n x)) (fun n =>
      ENNReal.continuous_ofReal.measurable.comp_aemeasurable
        (hfi n).aestronglyMeasurable.aemeasurable)
  rw [lintegral_congr_ae hlim] at hFatou
  have hlin : (∫⁻ x, ENNReal.ofReal (g x) ∂μ) ≤ ENNReal.ofReal M := by
    refine hFatou.trans (liminf_le_of_frequently_le' (Frequently.of_forall fun n => ?_))
    rw [← ofReal_integral_eq_lintegral_ofReal (hfi n) (hfnn n)]
    exact ENNReal.ofReal_le_ofReal (hbound n)
  have hgi : Integrable g μ := ⟨hgm, (hasFiniteIntegral_iff_ofReal hgnn).mpr
    (hlin.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hgi, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hgnn hgm]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hlin).trans_eq
    (ENNReal.toReal_ofReal hM)

/-- Fatou preserves a convergent sequence of integral bounds. -/
theorem integrable_and_integral_le_of_ae_limit_bound
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : ℕ → α → ℝ} {g : α → ℝ}
    (hfi : ∀ n, Integrable (f n) μ) (hfnn : ∀ n, 0 ≤ᵐ[μ] f n)
    (hgm : AEStronglyMeasurable g μ) (hgnn : 0 ≤ᵐ[μ] g)
    (hae : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x)))
    {b : ℕ → ℝ} {B : ℝ} (hb : Tendsto b atTop (𝓝 B))
    (hbound : ∀ n, (∫ x, f n x ∂μ) ≤ b n) :
    Integrable g μ ∧ (∫ x, g x ∂μ) ≤ B := by
  have hB : 0 ≤ B := ge_of_tendsto hb (Eventually.of_forall fun n =>
    (integral_nonneg_of_ae (hfnn n)).trans (hbound n))
  have hε (ε : ℝ) (hε : 0 < ε) : Integrable g μ ∧ (∫ x, g x ∂μ) ≤ B + ε := by
    obtain ⟨N, hN⟩ := eventually_atTop.mp
      (hb.eventually (ge_mem_nhds (lt_add_of_pos_right B hε)))
    apply integrable_and_integral_le_of_ae_limit (fun n => hfi (n + N))
      (fun n => hfnn (n + N)) hgm hgnn ?_ (add_nonneg hB hε.le)
      (fun n => (hbound (n + N)).trans (hN _ (by omega)))
    filter_upwards [hae] with x hx
    exact hx.comp (tendsto_add_atTop_nat N)
  exact ⟨(hε 1 zero_lt_one).1, le_of_forall_pos_le_add fun ε hpos => (hε ε hpos).2⟩

/-- Strong L² convergence preserves a limiting upper bound on a nonnegative weighted square moment. -/
theorem weighted_norm_sq_of_L2_limit
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : ℕ → Lp ℂ 2 μ} {g : Lp ℂ 2 μ} (hf : Tendsto f atTop (𝓝 g))
    {w : α → ℝ} (hwm : Measurable w) (hw0 : ∀ x, 0 ≤ w x)
    (hwi : ∀ n, Integrable (fun x => w x * ‖f n x‖ ^ 2) μ)
    {b : ℕ → ℝ} {B : ℝ} (hb : Tendsto b atTop (𝓝 B))
    (hbound : ∀ n, (∫ x, w x * ‖f n x‖ ^ 2 ∂μ) ≤ b n) :
    Integrable (fun x => w x * ‖g x‖ ^ 2) μ ∧
      (∫ x, w x * ‖g x‖ ^ 2 ∂μ) ≤ B := by
  obtain ⟨ns, hns, hae⟩ := GaloisForLFunctions.HTGeometry.exists_subseq_ae_tendsto hf
  apply integrable_and_integral_le_of_ae_limit_bound (fun n => hwi (ns n))
    (fun n => Eventually.of_forall fun x => mul_nonneg (hw0 x) (sq_nonneg _))
    (hwm.aestronglyMeasurable.mul ((Lp.aestronglyMeasurable g).norm.pow 2))
    (Eventually.of_forall fun x => mul_nonneg (hw0 x) (sq_nonneg _))
    ?_ (hb.comp hns.tendsto_atTop) (fun n => hbound (ns n))
  filter_upwards [hae] with x hx
  exact (hx.norm.pow 2).const_mul (w x)

#print axioms integrable_and_integral_le_of_ae_limit
#print axioms integrable_and_integral_le_of_ae_limit_bound
#print axioms weighted_norm_sq_of_L2_limit

/-- A common subsequence preserves the joint bound on two nonnegative weighted energies. -/
theorem weighted_norm_sq_add_of_L2_limits
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : ℕ → Lp ℂ 2 μ} {u v : Lp ℂ 2 μ}
    (hf : Tendsto f atTop (𝓝 u)) (hg : Tendsto g atTop (𝓝 v))
    {w z : α → ℝ} (hwm : Measurable w) (hzm : Measurable z)
    (hw0 : ∀ x, 0 ≤ w x) (hz0 : ∀ x, 0 ≤ z x)
    (hi : ∀ n, Integrable (fun x => w x * ‖f n x‖ ^ 2 + z x * ‖g n x‖ ^ 2) μ)
    {b : ℕ → ℝ} {B : ℝ} (hb : Tendsto b atTop (𝓝 B))
    (hbound : ∀ n, (∫ x, w x * ‖f n x‖ ^ 2 + z x * ‖g n x‖ ^ 2 ∂μ) ≤ b n) :
    Integrable (fun x => w x * ‖u x‖ ^ 2 + z x * ‖v x‖ ^ 2) μ ∧
      (∫ x, w x * ‖u x‖ ^ 2 + z x * ‖v x‖ ^ 2 ∂μ) ≤ B := by
  obtain ⟨ns, hns, hae⟩ := GaloisForLFunctions.HTGeometry.exists_subseq_ae_tendsto hf
  obtain ⟨ms, hms, hbe⟩ := GaloisForLFunctions.HTGeometry.exists_subseq_ae_tendsto
    (hg.comp hns.tendsto_atTop)
  apply integrable_and_integral_le_of_ae_limit_bound (fun n => hi (ns (ms n)))
    (fun n => Eventually.of_forall fun x =>
      add_nonneg (mul_nonneg (hw0 x) (sq_nonneg _)) (mul_nonneg (hz0 x) (sq_nonneg _)))
    ((hwm.aestronglyMeasurable.mul ((Lp.aestronglyMeasurable u).norm.pow 2)).add
      (hzm.aestronglyMeasurable.mul ((Lp.aestronglyMeasurable v).norm.pow 2)))
    (Eventually.of_forall fun x =>
      add_nonneg (mul_nonneg (hw0 x) (sq_nonneg _)) (mul_nonneg (hz0 x) (sq_nonneg _)))
    ?_ ((hb.comp hns.tendsto_atTop).comp hms.tendsto_atTop)
    (fun n => hbound (ns (ms n)))
  filter_upwards [hae, hbe] with x hx hy
  exact (((hx.comp hms.tendsto_atTop).norm.pow 2).const_mul (w x)).add
    ((hy.norm.pow 2).const_mul (z x))

#print axioms weighted_norm_sq_add_of_L2_limits
end GaloisForLFunctions.HTGeometry
