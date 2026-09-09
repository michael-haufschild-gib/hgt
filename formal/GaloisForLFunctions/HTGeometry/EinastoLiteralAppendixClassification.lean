import GaloisForLFunctions.HTGeometry.EinastoShapeMetricClassification

/-!
# The printed appendix's literal integral has the same sharp curvature threshold

Apply the all-shape theorem directly to the metric defined by the literal
appendix source and equation (15) of arXiv:2608.23600. On a whole neighborhood
of every sufficiently small positive radius it equals the audited integral
construction. This equality transfers through both actual derivatives, so the
curvature classification applies to the printed formula itself, without an
assumed smoothness condition or a replacement of curvature by metric values.
-/
noncomputable section
open Filter Real
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

/-- The first-order metric written directly with the paper's printed appendix source. -/
def einastoLiteralAppendixMetric (d l a β r : ℝ) : ℝ :=
  einastoMetric d l a r + β * ((∫ v in 0..r, 8 * Real.pi * v ^ 2 * quadraticAppendixSource (einastoMetric d l a) v) / r)

theorem einastoLiteralAppendixMetric_center (d l a β : ℝ) : einastoLiteralAppendixMetric d l a β 0 = 1 := by
  simp only [einastoLiteralAppendixMetric, einastoMetric_zero, intervalIntegral.integral_same, zero_div, mul_zero, add_zero]

theorem einastoLiteralAppendixMetric_eventually_equal (d l a β : ℝ) :
    (fun t => einastoLiteralAppendixMetric d l a β (exp t)) =ᶠ[atBot]
      (fun t => einastoShapePerturbedMetric d l a (-1) β (exp t)) := by
  filter_upwards [einastoShapeCorrection_appendix_integral d l a] with t ht
  unfold einastoLiteralAppendixMetric einastoShapePerturbedMetric
  rw [ht]

/-- Equality holds locally in radius, which is the input needed to identify derivatives. -/
theorem einastoLiteralAppendixMetric_locally_equal (d l a β : ℝ) :
    ∀ᶠ t in atBot, einastoLiteralAppendixMetric d l a β =ᶠ[𝓝 (exp t)] einastoShapePerturbedMetric d l a (-1) β := by
  obtain ⟨T, hT⟩ := eventually_atBot.mp (einastoLiteralAppendixMetric_eventually_equal d l a β)
  filter_upwards [eventually_le_atBot (T - 1)] with t ht
  have htT : t < T := by linarith
  filter_upwards [eventually_gt_nhds (exp_pos t), eventually_lt_nhds (exp_lt_exp.mpr htT)] with r hr hR
  have hl : log r < T := by
    apply exp_lt_exp.mp
    rw [exp_log hr]
    exact hR
  have h := hT (log r) hl.le
  dsimp only at h ⊢
  simpa only [exp_log hr] using h

/-- Both actual curvature expressions agree with the audited construction near the center. -/
theorem einastoLiteralAppendixMetric_curvatures_eventually (d l a β : ℝ) :
    ((fun t => radialKretschmannScalar (einastoLiteralAppendixMetric d l a β) (exp t)) =ᶠ[atBot]
      (fun t => radialKretschmannScalar (einastoShapePerturbedMetric d l a (-1) β) (exp t))) ∧
    ((fun t => radialRicciScalar (einastoLiteralAppendixMetric d l a β) (exp t)) =ᶠ[atBot]
      (fun t => radialRicciScalar (einastoShapePerturbedMetric d l a (-1) β) (exp t))) := by
  constructor
  · filter_upwards [einastoLiteralAppendixMetric_locally_equal d l a β] with t h
    unfold radialKretschmannScalar
    rw [h.self_of_nhds, h.deriv_eq, h.deriv.deriv_eq]
  · filter_upwards [einastoLiteralAppendixMetric_locally_equal d l a β] with t h
    unfold radialRicciScalar
    rw [h.self_of_nhds, h.deriv_eq, h.deriv.deriv_eq]

/-- Exact finite curvature classification for the literal printed integral. -/
theorem einastoLiteralAppendixMetric_Kretschmann_finite_limit_iff (d l a β K : ℝ) :
    Tendsto (fun t => radialKretschmannScalar (einastoLiteralAppendixMetric d l a β) (exp t)) atBot (𝓝 K) ↔
      (β = 0 ∨ 2 ≤ exp (-a)) ∧
        K = (512 * Real.pi ^ 2 * exp d ^ 2 / 3) * einastoShapeCoreMultiplier d l a (-1) β ^ 2 := by
  rw [tendsto_congr' (einastoLiteralAppendixMetric_curvatures_eventually d l a β).1]
  exact einastoShapeMetric_Kretschmann_finite_limit_iff d l a (-1) β K

theorem einastoLiteralAppendixMetric_regular_iff (d l a β : ℝ) :
    (∃ K : ℝ, Tendsto (fun t => radialKretschmannScalar (einastoLiteralAppendixMetric d l a β) (exp t)) atBot (𝓝 K)) ↔
      β = 0 ∨ 2 ≤ exp (-a) := by
  simp only [einastoLiteralAppendixMetric_Kretschmann_finite_limit_iff, exists_eq_right]

theorem einastoLiteralAppendixMetric_Kretschmann_diverges_iff (d l a β : ℝ) :
    Tendsto (fun t => radialKretschmannScalar (einastoLiteralAppendixMetric d l a β) (exp t)) atBot atTop ↔
      β ≠ 0 ∧ exp (-a) < 2 := by
  rw [tendsto_congr' (einastoLiteralAppendixMetric_curvatures_eventually d l a β).1]
  exact einastoShapeMetric_Kretschmann_diverges_iff d l a (-1) β

/-- In the paper's parameter α, every nonzero coupling is regular exactly for α≤1/2. -/
theorem einastoLiteralAppendixMetric_physical_shape_regular_iff (d l a β : ℝ) :
    (∃ K : ℝ, Tendsto (fun t => radialKretschmannScalar (einastoLiteralAppendixMetric d l a β) (exp t)) atBot (𝓝 K)) ↔
      β = 0 ∨ exp a ≤ (1 / 2 : ℝ) := by
  have he : (∃ K : ℝ, Tendsto (fun t => radialKretschmannScalar (einastoLiteralAppendixMetric d l a β) (exp t)) atBot (𝓝 K)) ↔
      (∃ K : ℝ, Tendsto (fun t => radialKretschmannScalar (einastoShapePerturbedMetric d l a (-1) β) (exp t)) atBot (𝓝 K)) := by
    apply exists_congr
    intro K
    exact tendsto_congr' (einastoLiteralAppendixMetric_curvatures_eventually d l a β).1
  exact he.trans (einastoShapeMetric_physical_shape_regular_iff d l a (-1) β)

end GaloisForLFunctions.HTGeometry
