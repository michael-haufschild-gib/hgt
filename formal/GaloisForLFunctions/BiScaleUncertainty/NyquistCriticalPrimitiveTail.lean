import GaloisForLFunctions.BiScaleUncertainty.NyquistCriticalPrimitive

/-!
# Absolute tails of the critical Nyquist primitive

The finite part is the unique continuous-primitive limit. Its error has an
integrable exponential envelope, including an explicit bound at every tail.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace GaloisForLFunctions.BiScaleUncertainty
set_option autoImplicit false

/-- The continuous primitive error is absolutely integrable on every nonnegative tail. -/
theorem integrableOn_nyquistCriticalPrimitive_sub_finitePart (m : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    IntegrableOn (fun x => nyquistCriticalPrimitive m x - nyquistCriticalFinitePart m) (Ioi T) := by
  apply ((integrableOn_exp_neg_Ioi T).const_mul
    (2 * (3 * nyquistCriticalDiscrepancyScale m + 2 * nyquistCriticalConstant m))).mono'
  · exact ((continuous_nyquistCriticalPrimitive m).sub continuous_const).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.norm_eq_abs]
    exact abs_nyquistCriticalPrimitive_sub_finitePart_le m (hT.trans hx.le)

/-- The total absolute error after any nonnegative endpoint decays exponentially. -/
theorem integral_abs_nyquistCriticalPrimitive_tail_le (m : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    (∫ x in Ioi T, |nyquistCriticalPrimitive m x - nyquistCriticalFinitePart m|) ≤
      2 * (3 * nyquistCriticalDiscrepancyScale m + 2 * nyquistCriticalConstant m) *
        Real.exp (-T) := by
  have h := integral_mono_ae
    (integrableOn_nyquistCriticalPrimitive_sub_finitePart m hT).abs
    ((integrableOn_exp_neg_Ioi T).const_mul
      (2 * (3 * nyquistCriticalDiscrepancyScale m + 2 * nyquistCriticalConstant m)))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact abs_nyquistCriticalPrimitive_sub_finitePart_le m (hT.trans hx.le))
  rw [integral_const_mul, integral_exp_neg_Ioi] at h
  exact h

/-- The absolutely convergent cell sum is the unique limit of the continuous primitive. -/
theorem tendsto_nyquistCriticalPrimitive_iff (m : ℕ) (b : ℝ) :
    Tendsto (nyquistCriticalPrimitive m) atTop (𝓝 b) ↔ b = nyquistCriticalFinitePart m := by
  constructor
  · intro hb
    exact tendsto_nhds_unique hb (tendsto_nyquistCriticalPrimitive m)
  · rintro rfl
    exact tendsto_nyquistCriticalPrimitive m

/-- Total cell mass plus its mean density obeys the width-dependent majorant. -/
theorem nyquistCriticalCellMass_add_mean_le_width (m k : ℕ) :
    nyquistWeightCellMass ((m : ℝ) + 1) m k +
      nyquistCriticalConstant m * nyquistWeightCellWidth k ≤
      (2 * nyquistCriticalConstant m + nyquistCriticalDiscrepancyScale m) *
        nyquistWeightCellWidth k := by
  have hn : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
  have hd := (nyquistCriticalCellDiscrepancy_bounds m k).2
  change nyquistWeightCellMass ((m : ℝ) + 1) m k -
    nyquistCriticalConstant m * nyquistWeightCellWidth k ≤ _ at hd
  have hD := div_le_self
    (mul_nonneg (nyquistCriticalDiscrepancyScale_pos m).le (nyquistWeightCellWidth_pos k).le) hn
  nlinarith only [hd, hD]

/-- Positivity of the actual residual controls its absolute deviation from the mean on each cell. -/
theorem integral_abs_nyquistCriticalCell_centered_le (m k : ℕ) :
    (∫ x in nyquistResidualCell k,
      |nyquistWeightKernel ((m : ℝ) + 1) m 0 x - nyquistCriticalConstant m|) ≤
      (2 * nyquistCriticalConstant m + nyquistCriticalDiscrepancyScale m) *
        nyquistWeightCellWidth k := by
  have hloc := locallyIntegrable_nyquistWeightKernel (by positivity : 0 ≤ (m : ℝ) + 1) m 0
  have hk : IntegrableOn (nyquistWeightKernel ((m : ℝ) + 1) m 0)
      (nyquistResidualCell k) :=
    (hloc.integrableOn_isCompact (isCompact_Icc : IsCompact
      (Icc (nyquistResidualNode k) (nyquistResidualNode (k + 1))))).mono_set Ioc_subset_Icc_self
  have hc : IntegrableOn (fun _ : ℝ => nyquistCriticalConstant m) (nyquistResidualCell k) :=
    continuous_const.integrableOn_Ioc
  have hb : (∫ x in nyquistResidualCell k,
      |nyquistWeightKernel ((m : ℝ) + 1) m 0 x - nyquistCriticalConstant m|) ≤
      ∫ x in nyquistResidualCell k,
        nyquistWeightKernel ((m : ℝ) + 1) m 0 x + nyquistCriticalConstant m := by
    apply integral_mono_ae (hk.sub hc).abs (hk.add hc)
    exact Eventually.of_forall fun x => by
      change |nyquistWeightKernel ((m : ℝ) + 1) m 0 x - nyquistCriticalConstant m| ≤
        nyquistWeightKernel ((m : ℝ) + 1) m 0 x + nyquistCriticalConstant m
      have hp := nyquistWeightKernel_nonneg (by positivity : 0 ≤ (m : ℝ) + 1) m 0 x
      have hp' := (nyquistCriticalConstant_pos m).le
      apply abs_le.mpr
      constructor <;> linarith only [hp, hp']
  have hm : (∫ x in nyquistResidualCell k, nyquistWeightKernel ((m : ℝ) + 1) m 0 x) =
      nyquistWeightCellMass ((m : ℝ) + 1) m k := by
    simpa only [Nat.zero_add] using integral_nyquistWeightKernel_cell ((m : ℝ) + 1) m 0 k
  have hconst : (∫ _x in nyquistResidualCell k, nyquistCriticalConstant m) =
      nyquistCriticalConstant m * nyquistWeightCellWidth k := by
    rw [nyquistResidualCell, ← intervalIntegral.integral_of_le
      (strictMono_nyquistResidualNode.monotone (Nat.le_succ k)), intervalIntegral.integral_const]
    simp only [smul_eq_mul, nyquistWeightCellWidth]
    ring
  rw [integral_add hk hc, hm, hconst] at hb
  exact hb.trans (nyquistCriticalCellMass_add_mean_le_width m k)

end GaloisForLFunctions.BiScaleUncertainty
