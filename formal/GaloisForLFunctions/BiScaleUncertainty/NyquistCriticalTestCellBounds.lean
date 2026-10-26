import GaloisForLFunctions.BiScaleUncertainty.NyquistCriticalPrimitive

/-!
# Summable error bounds for signed critical Nyquist tests

Freezing a Lipschitz test on each logarithmic cell separates oscillation from
the first moment of the cell discrepancies. Both have explicit summable bounds.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators CompactlySupported NNReal

namespace GaloisForLFunctions.BiScaleUncertainty
set_option autoImplicit false

/-- The first logarithmic moment of each discrepancy has a summable power bound. -/
theorem abs_nyquistCriticalCellDiscrepancy_mul_node_le (m k : ℕ) :
    |nyquistCriticalCellDiscrepancy m k| * nyquistResidualNode k ≤
      2 * nyquistCriticalDiscrepancyScale m * ((k + 1 : ℕ) : ℝ) ^ (-3 / 2 : ℝ) := by
  have hn : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  have hlog := Real.log_le_rpow_div hn.le (by norm_num : (0 : ℝ) < 1 / 2)
  calc
    _ ≤ (nyquistCriticalDiscrepancyScale m * ((k + 1 : ℕ) : ℝ) ^ (-2 : ℝ)) *
        nyquistResidualNode k :=
      mul_le_mul_of_nonneg_right (abs_nyquistCriticalCellDiscrepancy_le_inv_sq m k)
        (nyquistResidualNode_nonneg k)
    _ ≤ (nyquistCriticalDiscrepancyScale m * ((k + 1 : ℕ) : ℝ) ^ (-2 : ℝ)) *
        (((k + 1 : ℕ) : ℝ) ^ (1 / 2 : ℝ) / (1 / 2)) :=
      mul_le_mul_of_nonneg_left hlog
        (mul_nonneg (nyquistCriticalDiscrepancyScale_pos m).le (Real.rpow_nonneg hn.le _))
    _ = 2 * nyquistCriticalDiscrepancyScale m *
        (((k + 1 : ℕ) : ℝ) ^ (-2 : ℝ) * ((k + 1 : ℕ) : ℝ) ^ (1 / 2 : ℝ)) := by ring
    _ = _ := by rw [← Real.rpow_add hn]; norm_num

/-- Majorant for the sum of cell oscillation and frozen-discrepancy errors. -/
def nyquistCriticalTestCellMajorant (m k : ℕ) : ℝ :=
  2 * nyquistCriticalDiscrepancyScale m * ((k + 1 : ℕ) : ℝ) ^ (-3 / 2 : ℝ) +
    (nyquistCriticalDiscrepancyScale m + 2 * nyquistCriticalConstant m) *
      ((k + 1 : ℕ) : ℝ) ^ (-2 : ℝ)

theorem summable_nyquistCriticalTestCellMajorant (m : ℕ) :
    Summable (nyquistCriticalTestCellMajorant m) := by
  unfold nyquistCriticalTestCellMajorant
  simpa only [Nat.zero_add] using
    ((summable_nyquistPowerTail (by norm_num : (-3 / 2 : ℝ) < -1) 0).mul_left
      (2 * nyquistCriticalDiscrepancyScale m)).add
      ((summable_nyquistPowerTail (by norm_num : (-2 : ℝ) < -1) 0).mul_left
        (nyquistCriticalDiscrepancyScale m + 2 * nyquistCriticalConstant m))

/-- Exact constant required for the signed broad-test error. -/
theorem tsum_nyquistCriticalTestCellMajorant_le (m : ℕ) :
    (∑' k, nyquistCriticalTestCellMajorant m k) ≤
      8 * nyquistCriticalDiscrepancyScale m + 4 * nyquistCriticalConstant m := by
  have hs₁ : Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) ^ (-3 / 2 : ℝ)) := by
    simpa only [Nat.zero_add] using
      summable_nyquistPowerTail (by norm_num : (-3 / 2 : ℝ) < -1) 0
  have hs₂ : Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) ^ (-2 : ℝ)) := by
    simpa only [Nat.zero_add] using
      summable_nyquistPowerTail (by norm_num : (-2 : ℝ) < -1) 0
  have h₁ : nyquistPowerTail (-3 / 2) 0 ≤ 3 := by
    have h := nyquistPowerTail_le (by norm_num : (-3 / 2 : ℝ) < -1) 0
    norm_num at h ⊢
    exact h
  have h₂ : nyquistPowerTail (-2) 0 ≤ 2 := by
    have h := nyquistPowerTail_le (by norm_num : (-2 : ℝ) < -1) 0
    norm_num at h ⊢
    exact h
  have hD := (nyquistCriticalDiscrepancyScale_pos m).le
  have hc := (nyquistCriticalConstant_pos m).le
  unfold nyquistCriticalTestCellMajorant
  rw [Summable.tsum_add (hs₁.mul_left _) (hs₂.mul_left _),
    Summable.tsum_mul_left _ hs₁, Summable.tsum_mul_left _ hs₂]
  simp only [nyquistPowerTail, Nat.zero_add] at h₁ h₂
  have h₁' := mul_le_mul_of_nonneg_left h₁ (by positivity : 0 ≤ 2 * nyquistCriticalDiscrepancyScale m)
  have h₂' := mul_le_mul_of_nonneg_left h₂
    (by positivity : 0 ≤ nyquistCriticalDiscrepancyScale m + 2 * nyquistCriticalConstant m)
  linarith only [h₁', h₂']


private theorem integral_criticalCell_const (a : ℝ) (k : ℕ) :
    (∫ _x in nyquistResidualCell k, a) = a * nyquistWeightCellWidth k := by
  rw [nyquistResidualCell, ← intervalIntegral.integral_of_le
    (strictMono_nyquistResidualNode.monotone (Nat.le_succ k)), intervalIntegral.integral_const]
  simp only [smul_eq_mul, nyquistWeightCellWidth]
  ring

private theorem integral_criticalCell_residual (m k : ℕ) :
    (∫ x in nyquistResidualCell k, nyquistWeightCellResidual ((m : ℝ) + 1) m k x) =
      nyquistWeightCellMass ((m : ℝ) + 1) m k := by
  calc
    _ = ∫ x in nyquistResidualCell k, nyquistWeightKernel ((m : ℝ) + 1) m 0 x := by
      apply setIntegral_congr_fun (measurableSet_nyquistResidualCell k)
      intro x hx
      simpa only [Nat.zero_add] using
        (nyquistWeightKernel_on_cell ((m : ℝ) + 1) m 0 k
          (by simpa only [Nat.zero_add] using hx)).symm
    _ = _ := by simpa only [Nat.zero_add] using
      integral_nyquistWeightKernel_cell ((m : ℝ) + 1) m 0 k

/-- A cell's signed test error after subtracting its share of the finite part. -/
def nyquistCriticalCellTestError (m : ℕ) (G : ℝ → ℝ) (k : ℕ) : ℝ :=
  (∫ x in nyquistResidualCell k, G x * nyquistWeightKernel ((m : ℝ) + 1) m 0 x) -
    nyquistCriticalConstant m * (∫ x in nyquistResidualCell k, G x) -
    nyquistCriticalCellDiscrepancy m k * G 0

private theorem criticalCellTestError_decomposition (m k : ℕ) {G : ℝ → ℝ}
    (hG : Continuous G) :
    nyquistCriticalCellTestError m G k =
      (∫ x in nyquistResidualCell k,
        (G x - G (nyquistResidualNode k)) *
          (nyquistWeightCellResidual ((m : ℝ) + 1) m k x - nyquistCriticalConstant m)) +
        nyquistCriticalCellDiscrepancy m k * (G (nyquistResidualNode k) - G 0) := by
  have he := continuous_nyquistWeightCellResidual ((m : ℝ) + 1) m k
  have hi₁ : IntegrableOn (fun x => G x * nyquistWeightCellResidual ((m : ℝ) + 1) m k x)
      (nyquistResidualCell k) := (hG.mul he).integrableOn_Ioc
  have hi₂ : IntegrableOn (fun x => nyquistCriticalConstant m * G x)
      (nyquistResidualCell k) := (hG.const_mul (nyquistCriticalConstant m)).integrableOn_Ioc
  have hi₃ : IntegrableOn (fun x => G (nyquistResidualNode k) *
      nyquistWeightCellResidual ((m : ℝ) + 1) m k x)
      (nyquistResidualCell k) := (he.const_mul (G (nyquistResidualNode k))).integrableOn_Ioc
  have hi₄ : IntegrableOn (fun _x : ℝ => G (nyquistResidualNode k) * nyquistCriticalConstant m)
      (nyquistResidualCell k) := continuous_const.integrableOn_Ioc
  have hid : (fun x => (G x - G (nyquistResidualNode k)) *
      (nyquistWeightCellResidual ((m : ℝ) + 1) m k x - nyquistCriticalConstant m)) =
        fun x => ((G x * nyquistWeightCellResidual ((m : ℝ) + 1) m k x -
          nyquistCriticalConstant m * G x) -
            G (nyquistResidualNode k) * nyquistWeightCellResidual ((m : ℝ) + 1) m k x) +
              G (nyquistResidualNode k) * nyquistCriticalConstant m := by
    funext x
    ring
  have hi₁₂ : IntegrableOn (fun x => G x * nyquistWeightCellResidual ((m : ℝ) + 1) m k x -
      nyquistCriticalConstant m * G x) (nyquistResidualCell k) := hi₁.sub hi₂
  have hi₁₂₃ : IntegrableOn (fun x =>
      (G x * nyquistWeightCellResidual ((m : ℝ) + 1) m k x - nyquistCriticalConstant m * G x) -
        G (nyquistResidualNode k) * nyquistWeightCellResidual ((m : ℝ) + 1) m k x)
      (nyquistResidualCell k) := hi₁₂.sub hi₃
  rw [hid, integral_add hi₁₂₃ hi₄,
    integral_sub hi₁₂ hi₃, integral_sub hi₁ hi₂,
    integral_const_mul, integral_const_mul, integral_criticalCell_residual,
    integral_criticalCell_const]
  have hk : (∫ x in nyquistResidualCell k, G x * nyquistWeightKernel ((m : ℝ) + 1) m 0 x) =
      ∫ x in nyquistResidualCell k, G x * nyquistWeightCellResidual ((m : ℝ) + 1) m k x := by
    apply setIntegral_congr_fun (measurableSet_nyquistResidualCell k)
    intro x hx
    have heq := nyquistWeightKernel_on_cell ((m : ℝ) + 1) m 0 k
      (by simpa only [Nat.zero_add] using hx)
    simpa only [Nat.zero_add] using congrArg (fun z => G x * z) heq
  unfold nyquistCriticalCellTestError
  rw [hk]
  unfold nyquistCriticalCellDiscrepancy
  ring

private theorem abs_criticalCell_oscillation_le (m k : ℕ) {G : ℝ → ℝ}
    {A : ℝ≥0} (hG : LipschitzWith A G) :
    |∫ x in nyquistResidualCell k, (G x - G (nyquistResidualNode k)) *
        (nyquistWeightCellResidual ((m : ℝ) + 1) m k x - nyquistCriticalConstant m)| ≤
      (A : ℝ) * nyquistWeightCellWidth k *
        (nyquistWeightCellMass ((m : ℝ) + 1) m k +
          nyquistCriticalConstant m * nyquistWeightCellWidth k) := by
  have he := continuous_nyquistWeightCellResidual ((m : ℝ) + 1) m k
  have hi : IntegrableOn (fun x => (A : ℝ) * nyquistWeightCellWidth k *
      (nyquistWeightCellResidual ((m : ℝ) + 1) m k x + nyquistCriticalConstant m))
        (nyquistResidualCell k) :=
    ((he.add continuous_const).const_mul _).integrableOn_Ioc
  have hbound : ∀ᵐ x ∂volume.restrict (nyquistResidualCell k),
      ‖(G x - G (nyquistResidualNode k)) *
        (nyquistWeightCellResidual ((m : ℝ) + 1) m k x - nyquistCriticalConstant m)‖ ≤
          (A : ℝ) * nyquistWeightCellWidth k *
            (nyquistWeightCellResidual ((m : ℝ) + 1) m k x + nyquistCriticalConstant m) := by
    filter_upwards [ae_restrict_mem (measurableSet_nyquistResidualCell k)] with x hx
    have hpos := nyquistWeightCellResidual_nonneg (by positivity : 0 ≤ (m : ℝ) + 1) m k hx.1.le
    have hc := (nyquistCriticalConstant_pos m).le
    have hd := hG.dist_le_mul x (nyquistResidualNode k)
    rw [Real.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hx.1.le)] at hd
    have hd' : |G x - G (nyquistResidualNode k)| ≤ (A : ℝ) * nyquistWeightCellWidth k :=
      hd.trans (mul_le_mul_of_nonneg_left (sub_le_sub_right hx.2 _) A.coe_nonneg)
    have he' : |nyquistWeightCellResidual ((m : ℝ) + 1) m k x - nyquistCriticalConstant m| ≤
        nyquistWeightCellResidual ((m : ℝ) + 1) m k x + nyquistCriticalConstant m := by
      apply abs_le.mpr
      constructor <;> linarith only [hpos, hc]
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul hd' he' (abs_nonneg _)
      (mul_nonneg A.coe_nonneg (nyquistWeightCellWidth_pos k).le)
  have hei : IntegrableOn (nyquistWeightCellResidual ((m : ℝ) + 1) m k)
      (nyquistResidualCell k) := he.integrableOn_Ioc
  have hci : IntegrableOn (fun _x : ℝ => nyquistCriticalConstant m)
      (nyquistResidualCell k) := continuous_const.integrableOn_Ioc
  have hh := norm_integral_le_of_norm_le hi hbound
  rw [Real.norm_eq_abs, integral_const_mul,
    integral_add hei hci,
    integral_criticalCell_residual, integral_criticalCell_const] at hh
  exact hh

/-- Signed cell errors are dominated by one summable sequence, without differentiating the test. -/
theorem abs_nyquistCriticalCellTestError_le (m k : ℕ) {G : ℝ → ℝ}
    {A : ℝ≥0} (hG : LipschitzWith A G) :
    |nyquistCriticalCellTestError m G k| ≤ (A : ℝ) * nyquistCriticalTestCellMajorant m k := by
  have hn : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  have hD := (nyquistCriticalDiscrepancyScale_pos m).le
  have hc := (nyquistCriticalConstant_pos m).le
  have hp : ((k + 1 : ℕ) : ℝ) ^ (-2 : ℝ) = 1 / ((k + 1 : ℕ) : ℝ) ^ 2 := by
    rw [Real.rpow_neg hn.le, one_div]
    norm_cast
  have hm : (A : ℝ) * nyquistWeightCellWidth k *
      (nyquistWeightCellMass ((m : ℝ) + 1) m k +
        nyquistCriticalConstant m * nyquistWeightCellWidth k) ≤
      (A : ℝ) * ((nyquistCriticalDiscrepancyScale m + 2 * nyquistCriticalConstant m) *
        ((k + 1 : ℕ) : ℝ) ^ (-2 : ℝ)) := by
    calc
      _ ≤ (A : ℝ) * nyquistWeightCellWidth k *
          ((nyquistCriticalDiscrepancyScale m + 2 * nyquistCriticalConstant m) /
            ((k + 1 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left (nyquistCriticalCellMass_add_mean_le m k)
          (mul_nonneg A.coe_nonneg (nyquistWeightCellWidth_pos k).le)
      _ ≤ (A : ℝ) * (1 / ((k + 1 : ℕ) : ℝ)) *
          ((nyquistCriticalDiscrepancyScale m + 2 * nyquistCriticalConstant m) /
            ((k + 1 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (nyquistWeightCellWidth_bounds k).2 A.coe_nonneg) (by positivity)
      _ = _ := by rw [hp]; ring
  have hd := hG.dist_le_mul (nyquistResidualNode k) 0
  rw [Real.dist_eq, Real.dist_eq, sub_zero, abs_of_nonneg (nyquistResidualNode_nonneg k)] at hd
  have hdisc : |nyquistCriticalCellDiscrepancy m k * (G (nyquistResidualNode k) - G 0)| ≤
      (A : ℝ) * (2 * nyquistCriticalDiscrepancyScale m * ((k + 1 : ℕ) : ℝ) ^ (-3 / 2 : ℝ)) := by
    calc
      _ = |nyquistCriticalCellDiscrepancy m k| * |G (nyquistResidualNode k) - G 0| := abs_mul _ _
      _ ≤ |nyquistCriticalCellDiscrepancy m k| * ((A : ℝ) * nyquistResidualNode k) :=
        mul_le_mul_of_nonneg_left hd (abs_nonneg _)
      _ = (A : ℝ) * (|nyquistCriticalCellDiscrepancy m k| * nyquistResidualNode k) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (abs_nyquistCriticalCellDiscrepancy_mul_node_le m k) A.coe_nonneg
  rw [criticalCellTestError_decomposition m k hG.continuous]
  calc
    _ ≤ _ + _ := abs_add_le _ _
    _ ≤ (A : ℝ) * ((nyquistCriticalDiscrepancyScale m + 2 * nyquistCriticalConstant m) *
          ((k + 1 : ℕ) : ℝ) ^ (-2 : ℝ)) +
        (A : ℝ) * (2 * nyquistCriticalDiscrepancyScale m * ((k + 1 : ℕ) : ℝ) ^ (-3 / 2 : ℝ)) :=
      add_le_add ((abs_criticalCell_oscillation_le m k hG).trans hm) hdisc
    _ = _ := by unfold nyquistCriticalTestCellMajorant; ring

end GaloisForLFunctions.BiScaleUncertainty
