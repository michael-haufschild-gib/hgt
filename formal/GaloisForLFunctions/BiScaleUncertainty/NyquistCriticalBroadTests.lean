import GaloisForLFunctions.BiScaleUncertainty.NyquistCriticalTestCellBounds

/-!
# Signed compact tests at the critical Nyquist weight

Absolute control of the centered cell errors gives the finite-part expansion.
The test may change sign; the counterterm is integrated as continuous density.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators CompactlySupported NNReal

namespace GaloisForLFunctions.BiScaleUncertainty
set_option autoImplicit false

private theorem hasSum_nyquistCriticalCellTestError (m : ℕ) (G : C_c(ℝ, ℝ)) :
    HasSum (nyquistCriticalCellTestError m G)
      ((∫ x in Ioi (0 : ℝ), G x * nyquistWeightKernel ((m : ℝ) + 1) m 0 x) -
        nyquistCriticalConstant m * (∫ x in Ioi (0 : ℝ), G x) -
        nyquistCriticalFinitePart m * G 0) := by
  have hpart : (⋃ k : ℕ, nyquistResidualCell k) = Ioi (0 : ℝ) := by
    simpa only [Nat.zero_add, nyquistResidualNode_zero] using iUnion_nyquistResidualCell 0
  have hki := integrable_compact_mul_nyquistWeightKernel
    (by positivity : 0 ≤ (m : ℝ) + 1) m 0 G.continuous G.hasCompactSupport
  have hgi : Integrable (G : ℝ → ℝ) :=
    G.continuous.integrable_of_hasCompactSupport G.hasCompactSupport
  have hsk := hasSum_integral_iUnion measurableSet_nyquistResidualCell
    pairwise_disjoint_nyquistResidualCell hki.integrableOn
  have hsg := hasSum_integral_iUnion measurableSet_nyquistResidualCell
    pairwise_disjoint_nyquistResidualCell hgi.integrableOn
  rw [hpart] at hsk hsg
  have hsd : HasSum (nyquistCriticalCellDiscrepancy m) (nyquistCriticalFinitePart m) := by
    simpa only [nyquistCriticalFinitePart, nyquistCriticalFinitePartTail, Nat.zero_add] using
      (summable_nyquistCriticalCellDiscrepancy m).hasSum
  exact (hsk.sub (hsg.mul_left (nyquistCriticalConstant m))).sub (hsd.mul_right (G 0))

/-- The signed finite-part error is bounded by the test's actual Lipschitz constant. -/
theorem abs_nyquistCriticalTest_finitePart_error_le (m : ℕ) (G : C_c(ℝ, ℝ))
    {A : ℝ≥0} (hG : LipschitzWith A G) :
    |(∫ x in Ioi (0 : ℝ), G x * nyquistWeightKernel ((m : ℝ) + 1) m 0 x) -
        nyquistCriticalConstant m * (∫ x in Ioi (0 : ℝ), G x) -
        nyquistCriticalFinitePart m * G 0| ≤
      (8 * nyquistCriticalDiscrepancyScale m + 4 * nyquistCriticalConstant m) * (A : ℝ) := by
  have hs := hasSum_nyquistCriticalCellTestError m G
  have ha : Summable (fun k => |nyquistCriticalCellTestError m G k|) := by
    simpa only [Real.norm_eq_abs] using hs.summable.norm
  rw [← hs.tsum_eq]
  calc
    _ ≤ ∑' k, |nyquistCriticalCellTestError m G k| := by
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hs.summable.norm
    _ ≤ ∑' k, (A : ℝ) * nyquistCriticalTestCellMajorant m k :=
      Summable.tsum_le_tsum (fun k => abs_nyquistCriticalCellTestError_le m k hG) ha
        ((summable_nyquistCriticalTestCellMajorant m).mul_left (A : ℝ))
    _ = (A : ℝ) * ∑' k, nyquistCriticalTestCellMajorant m k :=
      Summable.tsum_mul_left _ (summable_nyquistCriticalTestCellMajorant m)
    _ ≤ (A : ℝ) * (8 * nyquistCriticalDiscrepancyScale m + 4 * nyquistCriticalConstant m) :=
      mul_le_mul_of_nonneg_left (tsum_nyquistCriticalTestCellMajorant_le m) A.coe_nonneg
    _ = _ := mul_comm _ _

/-- The actual kernel vanishes on the negative half-line, so both residual conventions agree. -/
theorem integral_criticalKernel_mul_eq_Ioi (m : ℕ) (G : ℝ → ℝ) :
    (∫ x, G x * nyquistWeightKernel ((m : ℝ) + 1) m 0 x) =
      ∫ x in Ioi (0 : ℝ), G x * nyquistWeightKernel ((m : ℝ) + 1) m 0 x := by
  rw [← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    by_cases hx : x ∈ Ioi (0 : ℝ)
    · rw [indicator_of_mem hx]
    · rw [indicator_of_notMem hx]
      change G x * nyquistWeightKernel ((m : ℝ) + 1) m 0 x = 0
      rw [nyquistWeightKernel_eq_zero ((m : ℝ) + 1) m 0
        (by simpa only [nyquistResidualNode_zero] using le_of_not_gt hx), mul_zero]


/-- Every positive broadening scale has the exact signed finite-part error bound. -/
theorem abs_nyquistCriticalBroadTest_error_le (m : ℕ) (H : C_c(ℝ, ℝ))
    {A : ℝ≥0} (hH : LipschitzWith A H) {L : ℝ} (hL : 0 < L) :
    |(∫ x in Ioi (0 : ℝ), H (x / L) * nyquistWeightKernel ((m : ℝ) + 1) m 0 x) -
        nyquistCriticalConstant m * L * (∫ x in Ioi (0 : ℝ), H x) -
        nyquistCriticalFinitePart m * H 0| ≤
      (8 * nyquistCriticalDiscrepancyScale m + 4 * nyquistCriticalConstant m) * (A : ℝ) / L := by
  let G : C_c(ℝ, ℝ) :=
    ⟨⟨sourceRescale H L⁻¹, H.continuous.comp (continuous_const.mul continuous_id)⟩,
      hasCompactSupport_sourceRescale H.hasCompactSupport (inv_pos.mpr hL)⟩
  have hG : LipschitzWith (A / ⟨L, hL.le⟩) G := by
    apply lipschitzWith_iff_dist_le_mul.mpr
    intro x y
    have hh := hH.dist_le_mul (L⁻¹ * x) (L⁻¹ * y)
    rw [Real.dist_eq, Real.dist_eq, ← mul_sub, abs_mul, abs_of_pos (inv_pos.mpr hL)] at hh
    change |H (L⁻¹ * x) - H (L⁻¹ * y)| ≤ ((A : ℝ) / L) * |x - y|
    calc
      _ ≤ (A : ℝ) * (L⁻¹ * |x - y|) := hh
      _ = _ := by ring
  have hi : (∫ x in Ioi (0 : ℝ), G x) = L * ∫ x in Ioi (0 : ℝ), H x := by
    change (∫ x in Ioi (0 : ℝ), H (L⁻¹ * x)) = _
    simpa only [mul_zero, inv_inv, smul_eq_mul] using
      integral_comp_mul_left_Ioi (H : ℝ → ℝ) 0 (inv_pos.mpr hL)
  have hzero : G 0 = H 0 := by change H (L⁻¹ * 0) = H 0; rw [mul_zero]
  have hfun : (fun x => G x * nyquistWeightKernel ((m : ℝ) + 1) m 0 x) =
      fun x => H (x / L) * nyquistWeightKernel ((m : ℝ) + 1) m 0 x := by
    funext x
    change H (L⁻¹ * x) * _ = _
    rw [div_eq_mul_inv, mul_comm L⁻¹ x]
  have hb := abs_nyquistCriticalTest_finitePart_error_le m G hG
  rw [hi, hzero, hfun, NNReal.coe_div] at hb
  change |(∫ x in Ioi (0 : ℝ), H (x / L) * nyquistWeightKernel ((m : ℝ) + 1) m 0 x) -
        nyquistCriticalConstant m * (L * ∫ x in Ioi (0 : ℝ), H x) -
        nyquistCriticalFinitePart m * H 0| ≤
      (8 * nyquistCriticalDiscrepancyScale m + 4 * nyquistCriticalConstant m) * ((A : ℝ) / L) at hb
  simpa only [mul_assoc, mul_div_assoc] using hb

/-- The same expansion for the full-line integral of the actual residual producer. -/
theorem abs_nyquistCriticalBroadTest_full_error_le (m : ℕ) (H : C_c(ℝ, ℝ))
    {A : ℝ≥0} (hH : LipschitzWith A H) {L : ℝ} (hL : 0 < L) :
    |(∫ x, H (x / L) * nyquistWeightKernel ((m : ℝ) + 1) m 0 x) -
        nyquistCriticalConstant m * L * (∫ x in Ioi (0 : ℝ), H x) -
        nyquistCriticalFinitePart m * H 0| ≤
      (8 * nyquistCriticalDiscrepancyScale m + 4 * nyquistCriticalConstant m) * (A : ℝ) / L := by
  rw [integral_criticalKernel_mul_eq_Ioi]
  exact abs_nyquistCriticalBroadTest_error_le m H hH hL

end GaloisForLFunctions.BiScaleUncertainty
