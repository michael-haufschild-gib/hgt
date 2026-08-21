import GaloisForLFunctions.RHTower.ConnesSobolevWeight
import GaloisForLFunctions.HTGeometry.WeightedDensityL2

/-!
# Connes' Sobolev measure `ρ_δ(u) du`

Appendix I (1) of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

The Hilbert space `L²_δ(ℝ)` of Appendix I is `L²` of the measure `ρ_δ(u) du` with
`ρ_δ(u) = (1+u²)^{δ/2}`.  Because `ρ_δ` is continuous the measure is finite on compact sets,
hence weakly regular, so continuous compactly supported functions are dense in it; and the
submultiplicativity of `ρ_δ` gives the operator bound `‖V(v)‖ ≤ (2^{δ/2} ρ_δ(v))^{1/2}` for the
translation `V(v)ξ = ξ(· − v)`.
-/

open MeasureTheory Set
open scoped ENNReal

namespace GaloisForLFunctions.RHTower

noncomputable section

theorem continuous_connesSobolevWeight (δ : ℝ) : Continuous (connesSobolevWeight δ) := by
  unfold connesSobolevWeight
  refine (continuous_const.add (continuous_pow 2)).rpow_const fun x => Or.inl ?_
  have : (0 : ℝ) < 1 + x ^ 2 := by positivity
  exact this.ne'

theorem measurable_connesSobolevWeight (δ : ℝ) : Measurable (connesSobolevWeight δ) :=
  (continuous_connesSobolevWeight δ).measurable

/-- Connes' Sobolev measure `ρ_δ(u) du` on the line. -/
def connesSobolevMeasure (δ : ℝ) : Measure ℝ :=
  volume.withDensity (HTGeometry.realDensity (connesSobolevWeight δ))

instance connesSobolevMeasure_isFiniteMeasureOnCompacts (δ : ℝ) :
    IsFiniteMeasureOnCompacts (connesSobolevMeasure δ) := by
  constructor
  intro K hK
  rw [connesSobolevMeasure, withDensity_apply _ hK.measurableSet]
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn
    (continuous_connesSobolevWeight δ).continuousOn
  have hbound : ∫⁻ u in K, HTGeometry.realDensity (connesSobolevWeight δ) u
      ≤ ∫⁻ _u in K, ENNReal.ofReal M := by
    refine setLIntegral_mono' hK.measurableSet fun u hu => ?_
    refine ENNReal.ofReal_le_ofReal ?_
    have := hM u hu
    rw [Real.norm_eq_abs, abs_of_nonneg (connesSobolevWeight_pos δ u).le] at this
    exact this
  refine lt_of_le_of_lt hbound ?_
  rw [setLIntegral_const]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK.measure_lt_top

instance connesSobolevMeasure_sigmaFinite (δ : ℝ) : SigmaFinite (connesSobolevMeasure δ) := by
  unfold connesSobolevMeasure HTGeometry.realDensity
  infer_instance

/-- The `L²(ρ_δ du)` energy of a function is its weighted lower Lebesgue energy. -/
theorem connes_lintegral_sobolevMeasure {δ : ℝ} {f : ℝ → ℂ}
    (hf : AEStronglyMeasurable f volume) :
    ∫⁻ u, ‖f u‖ₑ ^ 2 ∂(connesSobolevMeasure δ)
      = ∫⁻ u, ‖f u‖ₑ ^ 2 * ENNReal.ofReal (connesSobolevWeight δ u) := by
  rw [connesSobolevMeasure,
    lintegral_withDensity_eq_lintegral_mul₀
      (HTGeometry.measurable_realDensity (measurable_connesSobolevWeight δ)).aemeasurable
      (hf.enorm.pow_const 2)]
  refine lintegral_congr fun u => ?_
  simp only [Pi.mul_apply, HTGeometry.realDensity]
  ring

theorem connes_eLpNorm_two_sq {δ : ℝ} (f : ℝ → ℂ) :
    eLpNorm f 2 (connesSobolevMeasure δ)
      = (∫⁻ u, ‖f u‖ₑ ^ 2 ∂(connesSobolevMeasure δ)) ^ (1 / (2 : ℝ)) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [h2]
  congr 1
  refine lintegral_congr fun u => ?_
  rw [← ENNReal.rpow_natCast ‖f u‖ₑ 2]
  norm_num

theorem aestronglyMeasurable_translate {ξ : ℝ → ℂ} (hξ : AEStronglyMeasurable ξ volume)
    (v : ℝ) : AEStronglyMeasurable (fun u => ξ (u - v)) volume :=
  hξ.comp_measurePreserving (measurePreserving_sub_right volume v)

/-- **Appendix I (4).**  The translation `V(v)ξ = ξ(· − v)` is bounded on `L²_δ(ℝ)` with norm at
most `(2^{δ/2} ρ_δ(v))^{1/2}`. -/
theorem connes_eLpNorm_translate_le {δ : ℝ} (hδ : 0 ≤ δ) {ξ : ℝ → ℂ}
    (hξ : AEStronglyMeasurable ξ volume) (v : ℝ) :
    eLpNorm (fun u => ξ (u - v)) 2 (connesSobolevMeasure δ)
      ≤ ENNReal.ofReal (Real.sqrt (2 ^ (δ / 2) * connesSobolevWeight δ v))
          * eLpNorm ξ 2 (connesSobolevMeasure δ) := by
  have hshift := aestronglyMeasurable_translate hξ v
  have hnn : (0 : ℝ) ≤ 2 ^ (δ / 2) * connesSobolevWeight δ v := by
    have h1 : (0 : ℝ) < (2 : ℝ) ^ (δ / 2) := Real.rpow_pos_of_pos (by norm_num) _
    have h2 := connesSobolevWeight_pos δ v
    positivity
  rw [connes_eLpNorm_two_sq, connes_eLpNorm_two_sq,
    connes_lintegral_sobolevMeasure hshift, connes_lintegral_sobolevMeasure hξ]
  calc (∫⁻ u, ‖ξ (u - v)‖ₑ ^ 2 * ENNReal.ofReal (connesSobolevWeight δ u)) ^ (1 / (2 : ℝ))
      ≤ (ENNReal.ofReal (2 ^ (δ / 2) * connesSobolevWeight δ v) *
          ∫⁻ u, ‖ξ u‖ₑ ^ 2 * ENNReal.ofReal (connesSobolevWeight δ u)) ^ (1 / (2 : ℝ)) :=
        ENNReal.rpow_le_rpow (connesSobolevWeight_lintegral_translate_le hδ ξ v) (by norm_num)
    _ = ENNReal.ofReal (2 ^ (δ / 2) * connesSobolevWeight δ v) ^ (1 / (2 : ℝ)) *
          (∫⁻ u, ‖ξ u‖ₑ ^ 2 * ENNReal.ofReal (connesSobolevWeight δ u)) ^ (1 / (2 : ℝ)) :=
        ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
    _ = ENNReal.ofReal (Real.sqrt (2 ^ (δ / 2) * connesSobolevWeight δ v)) *
          (∫⁻ u, ‖ξ u‖ₑ ^ 2 * ENNReal.ofReal (connesSobolevWeight δ u)) ^ (1 / (2 : ℝ)) := by
        congr 1
        rw [Real.sqrt_eq_rpow, ENNReal.ofReal_rpow_of_nonneg hnn (by norm_num)]

/-- On the unit interval the Sobolev weight is at most `2^{δ/2}`. -/
theorem connesSobolevWeight_le_of_abs_le_one {δ : ℝ} (hδ : 0 ≤ δ) {v : ℝ} (hv : |v| ≤ 1) :
    connesSobolevWeight δ v ≤ 2 ^ (δ / 2) := by
  have hsq : v ^ 2 ≤ 1 := by
    have := abs_nonneg v
    nlinarith [sq_abs v]
  have hbase : (1 : ℝ) + v ^ 2 ≤ 2 := by linarith
  have hpos : (0 : ℝ) < 1 + v ^ 2 := by positivity
  exact Real.rpow_le_rpow hpos.le hbase (by linarith)

end

end GaloisForLFunctions.RHTower
