import GaloisForLFunctions.BiScaleUncertainty.NyquistCriticalFinitePartAndBroadClassification

/-!
# The continuous primitive of the critical Nyquist residual

The nodal finite part extends to every positive endpoint. Positivity controls
the unfinished cell and preserves an explicit exponentially decaying error.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators

namespace GaloisForLFunctions.BiScaleUncertainty
set_option autoImplicit false

private theorem intervalIntegrable_criticalKernel (m : ℕ) (a b : ℝ) :
    IntervalIntegrable (nyquistWeightKernel ((m : ℝ) + 1) m 0) volume a b := by
  have hloc := locallyIntegrable_nyquistWeightKernel
    (by positivity : 0 ≤ (m : ℝ) + 1) m 0
  have hi : IntegrableOn (nyquistWeightKernel ((m : ℝ) + 1) m 0) (uIcc a b) :=
    hloc.integrableOn_isCompact isCompact_uIcc
  exact hi.intervalIntegrable

/-- Integral of the actual kernel up to a grid node equals its finite cell sum. -/
theorem integral_criticalKernel_to_node (m N : ℕ) :
    (∫ x in 0..nyquistResidualNode N, nyquistWeightKernel ((m : ℝ) + 1) m 0 x) =
      nyquistWeightPrefixMass ((m : ℝ) + 1) m 0 N := by
  have hs := intervalIntegral.sum_integral_adjacent_intervals
    (a := nyquistResidualNode) (n := N)
    (fun k _ => intervalIntegrable_criticalKernel m (nyquistResidualNode k)
      (nyquistResidualNode (k + 1)))
  rw [nyquistResidualNode_zero] at hs
  rw [← hs, nyquistWeightPrefixMass]
  apply Finset.sum_congr rfl
  intro k _
  rw [intervalIntegral.integral_of_le
    (strictMono_nyquistResidualNode.monotone (Nat.le_succ k))]
  simpa only [Nat.zero_add, nyquistResidualCell] using
    integral_nyquistWeightKernel_cell ((m : ℝ) + 1) m 0 k

/-- The finite-part primitive uses the actual kernel and a continuous mean density. -/
def nyquistCriticalPrimitive (m : ℕ) (T : ℝ) : ℝ :=
  (∫ x in 0..T, nyquistWeightKernel ((m : ℝ) + 1) m 0 x) -
    nyquistCriticalConstant m * T

theorem continuous_nyquistCriticalPrimitive (m : ℕ) :
    Continuous (nyquistCriticalPrimitive m) :=
  (intervalIntegral.continuous_primitive (intervalIntegrable_criticalKernel m) 0).sub
    (continuous_const.mul continuous_id)

theorem nyquistCriticalPrimitive_node (m N : ℕ) :
    nyquistCriticalPrimitive m (nyquistResidualNode N) =
      nyquistCriticalPrefixPrimitive m N := by
  rw [nyquistCriticalPrimitive, integral_criticalKernel_to_node]
  rfl

/-- A critical cell and its mean counterterm have an explicit inverse-index mass bound. -/
theorem nyquistCriticalCellMass_add_mean_le (m k : ℕ) :
    nyquistWeightCellMass ((m : ℝ) + 1) m k +
      nyquistCriticalConstant m * nyquistWeightCellWidth k ≤
      (nyquistCriticalDiscrepancyScale m + 2 * nyquistCriticalConstant m) /
        ((k + 1 : ℕ) : ℝ) := by
  have hn : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  have hn1 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le k))
  have hd := (nyquistWeightCellWidth_bounds k).2
  have hd1 : nyquistWeightCellWidth k ≤ 1 :=
    hd.trans (div_le_one_of_le₀ hn1 hn.le)
  have hc := (nyquistCriticalConstant_pos m).le
  have hD := (nyquistCriticalDiscrepancyScale_pos m).le
  have hmass := (nyquistCriticalCellDiscrepancy_bounds m k).2
  change nyquistWeightCellMass ((m : ℝ) + 1) m k -
    nyquistCriticalConstant m * nyquistWeightCellWidth k ≤ _ at hmass
  have hDd : nyquistCriticalDiscrepancyScale m * nyquistWeightCellWidth k /
      ((k + 1 : ℕ) : ℝ) ≤ nyquistCriticalDiscrepancyScale m / ((k + 1 : ℕ) : ℝ) := by
    exact div_le_div_of_nonneg_right (mul_le_of_le_one_right hD hd1) hn.le
  have hcd := mul_le_mul_of_nonneg_left hd hc
  rw [mul_one_div] at hcd
  rw [add_div, mul_div_assoc]
  linarith only [hmass, hDd, hcd]

private theorem abs_criticalPrimitive_sub_node_le (m k : ℕ) {T : ℝ}
    (hT : T ∈ nyquistResidualCell k) :
    |nyquistCriticalPrimitive m T - nyquistCriticalPrimitive m (nyquistResidualNode k)| ≤
      (nyquistCriticalDiscrepancyScale m + 2 * nyquistCriticalConstant m) /
        ((k + 1 : ℕ) : ℝ) := by
  have hi := intervalIntegrable_criticalKernel m (nyquistResidualNode k)
    (nyquistResidualNode (k + 1))
  have hzero : 0 ≤ ∫ x in nyquistResidualNode k..T,
      nyquistWeightKernel ((m : ℝ) + 1) m 0 x := by
    rw [intervalIntegral.integral_of_le hT.1.le]
    exact integral_nonneg fun x => nyquistWeightKernel_nonneg (by positivity) m 0 x
  have hmass : (∫ x in nyquistResidualNode k..T,
      nyquistWeightKernel ((m : ℝ) + 1) m 0 x) ≤
        nyquistWeightCellMass ((m : ℝ) + 1) m k := by
    calc
      _ ≤ ∫ x in nyquistResidualNode k..nyquistResidualNode (k + 1),
          nyquistWeightKernel ((m : ℝ) + 1) m 0 x :=
        intervalIntegral.integral_mono_interval le_rfl hT.1.le hT.2
          (Eventually.of_forall fun x => nyquistWeightKernel_nonneg (by positivity) m 0 x) hi
      _ = _ := by
        rw [intervalIntegral.integral_of_le
          (strictMono_nyquistResidualNode.monotone (Nat.le_succ k))]
        simpa only [Nat.zero_add, nyquistResidualCell] using
          integral_nyquistWeightKernel_cell ((m : ℝ) + 1) m 0 k
  have hmean0 : 0 ≤ nyquistCriticalConstant m * (T - nyquistResidualNode k) :=
    mul_nonneg (nyquistCriticalConstant_pos m).le (sub_nonneg.mpr hT.1.le)
  have hmean : nyquistCriticalConstant m * (T - nyquistResidualNode k) ≤
      nyquistCriticalConstant m * nyquistWeightCellWidth k :=
    mul_le_mul_of_nonneg_left (sub_le_sub_right hT.2 _) (nyquistCriticalConstant_pos m).le
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_criticalKernel m 0 (nyquistResidualNode k))
    (intervalIntegrable_criticalKernel m (nyquistResidualNode k) T)
  have heq : nyquistCriticalPrimitive m T -
      nyquistCriticalPrimitive m (nyquistResidualNode k) =
        (∫ x in nyquistResidualNode k..T, nyquistWeightKernel ((m : ℝ) + 1) m 0 x) -
          nyquistCriticalConstant m * (T - nyquistResidualNode k) := by
    unfold nyquistCriticalPrimitive
    linarith only [hadd]
  rw [heq]
  apply le_trans _ (nyquistCriticalCellMass_add_mean_le m k)
  apply abs_le.mpr
  have ha := nyquistWeightCellMass_nonneg (by positivity : 0 ≤ (m : ℝ) + 1) m k
  have hc := mul_nonneg (nyquistCriticalConstant_pos m).le (nyquistWeightCellWidth_pos k).le
  constructor <;> linarith only [hzero, hmass, hmean0, hmean, ha, hc]

/-- Exponentially decaying finite-part error at every nonnegative real endpoint. -/
theorem abs_nyquistCriticalPrimitive_sub_finitePart_le (m : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    |nyquistCriticalPrimitive m T - nyquistCriticalFinitePart m| ≤
      2 * (3 * nyquistCriticalDiscrepancyScale m + 2 * nyquistCriticalConstant m) *
        Real.exp (-T) := by
  rcases eq_or_lt_of_le hT with rfl | hT
  · simp only [nyquistCriticalPrimitive, intervalIntegral.integral_same, mul_zero,
      sub_zero, zero_sub, abs_neg, neg_zero, Real.exp_zero, mul_one]
    have hb := abs_nyquistCriticalFinitePart_le m
    have hc := (nyquistCriticalConstant_pos m).le
    have hD := (nyquistCriticalDiscrepancyScale_pos m).le
    linarith only [hb, hc, hD]
  · have hx : T ∈ Ioi (nyquistResidualNode 0) := by
      rw [nyquistResidualNode_zero]
      exact mem_Ioi.mpr hT
    obtain ⟨k, hk⟩ := mem_iUnion.mp ((iUnion_nyquistResidualCell 0).symm ▸ hx)
    simp only [Nat.zero_add] at hk
    have hc := abs_criticalPrimitive_sub_node_le m k hk
    have hn := abs_nyquistCriticalPrefixPrimitive_sub_finitePart_le m k
    rw [← nyquistCriticalPrimitive_node] at hn
    have ht := abs_sub_le (nyquistCriticalPrimitive m T)
      (nyquistCriticalPrimitive m (nyquistResidualNode k)) (nyquistCriticalFinitePart m)
    have hnear : |nyquistCriticalPrimitive m T - nyquistCriticalFinitePart m| ≤
        (3 * nyquistCriticalDiscrepancyScale m + 2 * nyquistCriticalConstant m) /
          ((k + 1 : ℕ) : ℝ) := by
      calc
        _ ≤ |nyquistCriticalPrimitive m T - nyquistCriticalPrimitive m (nyquistResidualNode k)| +
            |nyquistCriticalPrimitive m (nyquistResidualNode k) - nyquistCriticalFinitePart m| := ht
        _ ≤ (nyquistCriticalDiscrepancyScale m + 2 * nyquistCriticalConstant m) /
              ((k + 1 : ℕ) : ℝ) + 2 * nyquistCriticalDiscrepancyScale m / ((k + 1 : ℕ) : ℝ) :=
          add_le_add hc hn
        _ = _ := by ring
    have hkpos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
    have he : Real.exp T ≤ 2 * ((k + 1 : ℕ) : ℝ) := by
      have he' := Real.exp_le_exp.mpr hk.2
      rw [nyquistResidualNode, Real.exp_log (by positivity : (0 : ℝ) < (k + 1 + 1 : ℕ))] at he'
      push_cast at he' ⊢
      have hk0 := Nat.cast_nonneg (α := ℝ) k
      linarith only [he', hk0]
    have hinv : 1 / ((k + 1 : ℕ) : ℝ) ≤ 2 * Real.exp (-T) := by
      rw [Real.exp_neg, ← div_eq_mul_inv]
      exact (div_le_div_iff₀ hkpos (Real.exp_pos T)).mpr (by simpa only [one_mul] using he)
    calc
      _ ≤ (3 * nyquistCriticalDiscrepancyScale m + 2 * nyquistCriticalConstant m) *
          (1 / ((k + 1 : ℕ) : ℝ)) := by simpa only [mul_one_div] using hnear
      _ ≤ (3 * nyquistCriticalDiscrepancyScale m + 2 * nyquistCriticalConstant m) *
          (2 * Real.exp (-T)) := mul_le_mul_of_nonneg_left hinv (by
            have hD := (nyquistCriticalDiscrepancyScale_pos m).le
            have hc := (nyquistCriticalConstant_pos m).le
            positivity)
      _ = _ := by ring

theorem tendsto_nyquistCriticalPrimitive (m : ℕ) :
    Tendsto (nyquistCriticalPrimitive m) atTop (𝓝 (nyquistCriticalFinitePart m)) := by
  rw [← tendsto_sub_nhds_zero_iff]
  apply squeeze_zero_norm'
    (a := fun T => 2 * (3 * nyquistCriticalDiscrepancyScale m + 2 * nyquistCriticalConstant m) *
      Real.exp (-T))
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    rw [Real.norm_eq_abs]
    exact abs_nyquistCriticalPrimitive_sub_finitePart_le m hT
  · simpa only [Function.comp_def, mul_zero] using
      (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot).const_mul
        (2 * (3 * nyquistCriticalDiscrepancyScale m + 2 * nyquistCriticalConstant m))

end GaloisForLFunctions.BiScaleUncertainty
