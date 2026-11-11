import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheDetectorEnergyIsStableUnderCoefficientChanges
import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheGateDisplacementsHaveOneNormalizedLimit
import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheShortMollifierMakesTheHeadAndGateErrorNegligible
import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheTaperBoundsTheActualDetectorBlock

/-!
# One fixed coefficient family on every detector block

The gate width changes the normalized coefficient exponent by at most
`13/(10(U−1))`. Its squared error is negligible on the entire height
range. Young's inequality therefore transfers matched block bounds to
one fixed family, while the Weyl estimate controls all low blocks.
-/

open Complex Filter MeasureTheory Set Topology
open RHTower RHTower.ZetaGateProductAFE

noncomputable section

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

/-- The detector energy with coefficients fixed at the upper-height displacement. -/
def shortFixedDetectorBlockEnergy (U d a v : ℝ) : ℝ :=
  ∫ t in a..v, ‖levinsonMollifiedDetector ((1 / Real.log U : ℝ) : ℂ)
    (shortLevinsonCoefficients (13 / 10) U) (Finset.Icc 1 (shortLevinsonCutoff U))
    (((1 / 2 - d : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2

private theorem short_coefficients_eq_linear (U : ℝ) :
    shortLevinsonCoefficients (13 / 10) U =
      fun n => (linearDetectorWeights (shortLevinsonCutoff U) ((13 / 10) / Real.log U) n : ℂ) := by
  funext n
  exact (coe_linearDetectorWeights _ _ n).symm

private theorem matched_energy_eq (N : ℕ) (d lam a v : ℝ) :
    (∫ t in a..v, ‖levinsonMollifiedDetector (lam : ℂ)
      (fun n => (linearDetectorWeights N d n : ℂ)) (Finset.Icc 1 N)
      (((1 / 2 - d : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) =
      matchedDetectorBlockEnergy N d lam a v := by
  unfold matchedDetectorBlockEnergy levinsonMollifiedDetector levinsonG
  simp only [displacedLinePt, Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_ofNat]

private theorem eventually_gate_cutoff_geometry :
    ∀ᶠ U : ℝ in atTop, 4 ≤ U ∧ 1 ≤ Real.log (U - 1) ∧ 1 ≤ Real.log U ∧
      1 < shortLevinsonCutoff U ∧ (shortLevinsonCutoff U : ℝ) ≤ U ∧
      (13 / 10 : ℝ) / (U - 1) ≤ 1 := by
  have hUm : Tendsto (fun U : ℝ => U - 1) atTop atTop := by
    apply Filter.tendsto_atTop.2
    intro A
    filter_upwards [eventually_ge_atTop (A + 1)] with U hU
    linarith only [hU]
  filter_upwards [eventually_ge_atTop (4 : ℝ),
    (Real.tendsto_log_atTop.comp hUm).eventually_ge_atTop 1,
    Real.tendsto_log_atTop.eventually_ge_atTop 1,
    tendsto_shortLevinsonCutoff.eventually_ge_atTop 2,
    eventually_shortLevinsonCutoff_add_one_le] with U hU hLm hLU hN hNU
  have hNU' : (shortLevinsonCutoff U : ℝ) ≤ U := by
    push_cast at hNU
    linarith only [hNU]
  exact ⟨hU, hLm, hLU, by omega, hNU',
    (div_le_one (by linarith only [hU] : 0 < U - 1)).mpr (by linarith only [hU])⟩

/-- The fixed-coefficient detector has negligible energy on every low block. -/
theorem eventually_shortFixedDetectorBlockEnergy_low_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ U : ℝ in atTop, ∀ a v d : ℝ,
      20 ≤ a → a ≤ v → v ≤ 2 * a → a ≤ U ^ (53 / 100 : ℝ) →
      13 / 10 ≤ d * Real.log U → d * Real.log (U - 1) ≤ 13 / 10 →
      shortFixedDetectorBlockEnergy U d a v ≤ ε * U / Real.log U := by
  obtain ⟨r, hr, hrhalf, C, hC, hhead⟩ := exists_integral_linearDetector_head_bound
  have hscale := eventually_short_detector_head_scale_le
    (C := C * Real.exp 1 ^ 2) (by positivity) hε
  filter_upwards [hscale, eventually_gate_cutoff_geometry,
    eventually_gate_displacements_small (by norm_num : (0 : ℝ) < 13 / 10) hr]
    with U hsi hUi hdi
  intro a v d ha hav hv2 halow hg0 hg1
  obtain ⟨hd0, hdr⟩ := hdi d hg0 hg1
  have hU2 : 2 < U := by linarith only [hUi.1]
  have hL : 0 < Real.log U := zero_lt_one.trans_le hUi.2.2.1
  have hw := levinsonGate_coefficient_shift_width hU2 hUi.2.1 (by norm_num : (0 : ℝ) ≤ 13 / 10)
    hUi.2.2.2.1 hUi.2.2.2.2.1 hg0 hg1
  have hen := linearDetectorWeights_fixed_envelopes hUi.2.2.2.1 hw.1 hw.2
  have hb : ∀ n ∈ Finset.Icc 1 (shortLevinsonCutoff U),
      ‖shortLevinsonCoefficients (13 / 10) U n‖ ≤ Real.exp 1 * (n : ℝ) ^ ((1 / 2 - d) - 1 / 2) := by
    intro n hn
    rw [short_coefficients_eq_linear, Complex.norm_real, Real.norm_eq_abs,
      show (1 / 2 - d) - 1 / 2 = -d by ring]
    exact (hen n hn).1.trans (mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr hUi.2.2.2.2.2) (Real.rpow_nonneg (Nat.cast_nonneg n) _))
  have hlam : |1 / Real.log U| ≤ 1 := by
    rw [abs_of_pos (one_div_pos.mpr hL)]
    simpa using one_div_le_one_div_of_le zero_lt_one hUi.2.2.1
  have hσ : |(1 / 2 - d) - 1 / 2| ≤ r := by
    rw [show (1 / 2 - d) - 1 / 2 = -d by ring, abs_neg, abs_of_pos hd0]
    exact hdr
  have he := hhead (shortLevinsonCutoff U) (shortLevinsonCoefficients (13 / 10) U)
    (1 / 2 - d) (1 / Real.log U) (Real.exp 1) a v (2 * U ^ (53 / 100 : ℝ))
    hσ hlam (Real.exp_pos 1).le hb (by linarith only [ha]) hav
    (by linarith only [hv2, halow])
  exact he.trans hsi

/-- Young's inequality transfers every matched block estimate to the same fixed coefficients. -/
theorem eventually_shortFixedDetectorBlockEnergy_stability {ε η : ℝ}
    (hε : 0 < ε) (hη : 0 < η) :
    ∀ᶠ U : ℝ in atTop, ∀ a v d : ℝ,
      20 ≤ a → a ≤ v → v ≤ U →
      13 / 10 ≤ d * Real.log U → d * Real.log (U - 1) ≤ 13 / 10 →
      shortFixedDetectorBlockEnergy U d a v ≤
        (1 + ε) * matchedDetectorBlockEnergy (shortLevinsonCutoff U) d (1 / Real.log U) a v +
          η * U / Real.log U := by
  obtain ⟨r, hr, hrhalf, C, hC, hstable⟩ := exists_integral_detector_coefficient_stability
  have hscale := eventually_short_detector_coefficient_error_le
    (C := (1 + 1 / ε) * C) (by positivity) hη
  filter_upwards [hscale, eventually_gate_cutoff_geometry,
    eventually_gate_displacements_small (by norm_num : (0 : ℝ) < 13 / 10) hr]
    with U hsi hUi hdi
  intro a v d ha hav hvU hg0 hg1
  obtain ⟨hd0, hdr⟩ := hdi d hg0 hg1
  have hU2 : 2 < U := by linarith only [hUi.1]
  have hL : 0 < Real.log U := zero_lt_one.trans_le hUi.2.2.1
  have hw := levinsonGate_coefficient_shift_width hU2 hUi.2.1 (by norm_num : (0 : ℝ) ≤ 13 / 10)
    hUi.2.2.2.1 hUi.2.2.2.2.1 hg0 hg1
  have hen := fixedLinearMollifier_difference_envelope hUi.2.2.2.1 hw.1 hw.2
  have hb : ∀ n ∈ Finset.Icc 1 (shortLevinsonCutoff U),
      ‖shortLevinsonCoefficients (13 / 10) U n - (linearDetectorWeights (shortLevinsonCutoff U) d n : ℂ)‖ ≤
        (((13 / 10) / (U - 1)) * Real.exp ((13 / 10) / (U - 1))) *
          (n : ℝ) ^ ((1 / 2 - d) - 1 / 2) := by
    simpa only [short_coefficients_eq_linear] using hen
  have hlam : |1 / Real.log U| ≤ 1 := by
    rw [abs_of_pos (one_div_pos.mpr hL)]
    simpa using one_div_le_one_div_of_le zero_lt_one hUi.2.2.1
  have hσ : |(1 / 2 - d) - 1 / 2| ≤ r := by
    rw [show (1 / 2 - d) - 1 / 2 = -d by ring, abs_neg, abs_of_pos hd0]
    exact hdr
  have he := hstable (shortLevinsonCutoff U) (shortLevinsonCoefficients (13 / 10) U)
    (fun n => (linearDetectorWeights (shortLevinsonCutoff U) d n : ℂ))
    (1 / 2 - d) (1 / Real.log U)
    (((13 / 10) / (U - 1)) * Real.exp ((13 / 10) / (U - 1))) ε a v U
    hσ hlam (mul_nonneg (div_nonneg (by norm_num) (by linarith only [hUi.1])) (Real.exp_pos _).le)
    hε hb (by linarith only [ha]) hav hvU
  rw [matched_energy_eq] at he
  change shortFixedDetectorBlockEnergy U d a v ≤ _ at he
  refine he.trans (add_le_add_left ?_ _)
  simpa only [mul_assoc] using hsi

end GaloisForLFunctions.MultiscaleMollifiedZetaField
