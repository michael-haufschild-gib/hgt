import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.TheNaturalScaleOfTheShortRatioEnergy
import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.TheIsolatedDiagonalOfTheShortMoebiusWindows

/-!
# The growth rate of the short-ratio form

Multiplying the triangular ratio form by the inverse bandwidth exposes
its unavoidable diagonal growth. The normalized form tends to infinity at
every positive polynomial length. Its logarithmic height exponent tends
to zero at all those lengths exactly when the Riemann hypothesis holds.
-/

namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.MoebiusGram

open Filter Topology MeasureTheory
open GaloisForLFunctions.SquareRootThreshold (zetaZeroWidth zetaZeroWidth_nonneg
  zetaZeroWidth_le_iff_xiZeroHalfPlaneBound)

noncomputable section

/-- The compensated finite ratio sum at length ⌊T^θ⌋ and bandwidth 1/T. -/
def normalizedRatioForm (θ T : ℝ) : ℝ := T * shortRatioForm ⌊T^θ⌋₊ T

theorem normalizedRatioForm_tendsto_atTop {θ : ℝ} (hθ : 0 < θ) :
    Tendsto (normalizedRatioForm θ) atTop atTop := by
  have hN : Tendsto (fun T : ℝ => ⌊T^θ⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp (tendsto_rpow_atTop hθ)
  apply (normalized_energy_tendsto_atTop _ id hN tendsto_id).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  simp only [normalizedRatioForm, shortRatioForm_eq_bandEnergy _ hT, id_eq]

/-- The least length slope in the normalized arithmetic form is twice
the width of the zeta zeros. All positive height losses are allowed. -/
theorem width_iff_normalized_ratio_growth {β : ℝ} (hβ : 0 ≤ β) :
    zetaZeroWidth ≤ β ↔ ∀ θ : ℝ, 0 < θ → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ T : ℝ in atTop, normalizedRatioForm θ T ≤ T^(2*β*θ+ε) := by
  constructor
  · intro hwidth θ hθ ε hε
    have he := half_pos hε
    obtain ⟨C, _, hC⟩ := short_ratio_bound_with_bandwidth hθ he
    filter_upwards [eventually_ge_atTop (1 : ℝ), (tendsto_rpow_atTop he).eventually_ge_atTop C]
      with T hT hc
    have ht := zero_lt_one.trans_le hT
    rw [normalizedRatioForm, shortRatioForm_eq_bandEnergy _ ht]
    calc
      _ ≤ T * (C * T^(-1+2*zetaZeroWidth*θ+ε/2)) :=
        mul_le_mul_of_nonneg_left (hC T hT) ht.le
      _ ≤ T * (T^(ε/2) * T^(-1+2*zetaZeroWidth*θ+ε/2)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg ht.le _)) ht.le
      _ = T^(2*zetaZeroWidth*θ+ε) := by
        conv_lhs => lhs; rw [← Real.rpow_one T]
        rw [← Real.rpow_add ht, ← Real.rpow_add ht]
        congr 1
        ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hT (by
        linarith only [mul_le_mul_of_nonneg_right hwidth hθ.le])
  · intro hg
    apply (shortRatioGrowth_iff_zero_width hβ).mp
    refine ⟨1, zero_le_one, fun θ hθ => ⟨θ, le_rfl, 1, zero_le_one, ?_⟩⟩
    apply Filter.Eventually.frequently
    filter_upwards [eventually_ge_atTop (1 : ℝ), hg θ hθ 1 zero_lt_one] with T hT hb
    have ht := zero_lt_one.trans_le hT
    rw [normalizedRatioForm, shortRatioForm_eq_bandEnergy _ ht] at hb
    have hnon : 0 ≤ bandEnergy ⌊T^θ⌋₊ T⁻¹ := integral_nonneg fun _ => sq_nonneg _
    rw [one_mul, add_comm 1]
    exact (le_mul_of_one_le_left hnon hT).trans hb

/-- The logarithmic exponent vanishes at every power length exactly on RH,
even though the underlying positive form diverges at every such length. -/
theorem riemannHypothesis_iff_normalized_ratio_log_rate :
    RiemannHypothesis ↔ ∀ θ : ℝ, 0 < θ →
      Tendsto (fun T : ℝ => Real.log (normalizedRatioForm θ T)/Real.log T) atTop (𝓝 0) := by
  rw [_root_.RHTower.riemannHypothesis_iff_xiZeroHalfPlaneBound_zero,
    ← zetaZeroWidth_le_iff_xiZeroHalfPlaneBound le_rfl,
    width_iff_normalized_ratio_growth le_rfl]
  simp only [mul_zero, zero_mul, zero_add]
  constructor
  · intro h θ hθ
    have hg := (normalizedRatioForm_tendsto_atTop hθ).eventually_ge_atTop 1
    apply tendsto_order.mpr
    constructor
    · intro a ha
      filter_upwards [eventually_gt_atTop (1 : ℝ), hg] with T hT hE
      exact ha.trans_le (div_nonneg (Real.log_nonneg hE) (Real.log_pos hT).le)
    · intro b hb
      filter_upwards [eventually_gt_atTop (1 : ℝ), hg, h θ hθ _ (half_pos hb)] with T hT hE hr
      have ht := zero_lt_one.trans hT
      have hl := Real.log_le_log (zero_lt_one.trans_le hE) hr
      rw [Real.log_rpow ht] at hl
      exact ((div_le_iff₀ (Real.log_pos hT)).mpr hl).trans_lt (half_lt_self hb)
  · intro h θ hθ ε hε
    filter_upwards [eventually_gt_atTop (1 : ℝ),
        (normalizedRatioForm_tendsto_atTop hθ).eventually_ge_atTop 1,
        (tendsto_order.mp (h θ hθ)).2 ε hε] with T hT hE hr
    have ht := zero_lt_one.trans hT
    apply (Real.log_le_log_iff (zero_lt_one.trans_le hE) (Real.rpow_pos_of_pos ht _)).mp
    rw [Real.log_rpow ht]
    exact ((div_lt_iff₀ (Real.log_pos hT)).mp hr).le

#print axioms normalizedRatioForm_tendsto_atTop
#print axioms width_iff_normalized_ratio_growth
#print axioms riemannHypothesis_iff_normalized_ratio_log_rate
end
end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.MoebiusGram
