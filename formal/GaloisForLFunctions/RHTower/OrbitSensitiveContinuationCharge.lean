import GaloisForLFunctions.RHTower.FiniteOfflineCauchyL2
import GaloisForLFunctions.RHTower.XiThetaSquareRateBoundary
import GaloisForLFunctions.RHTower.XiRationalQuartetGauge

open Complex MeasureTheory Set
open scoped BigOperators

noncomputable section

namespace RHTower

/-- A simple pole, sampled on the fixed horizontal line `Im z = Y`. -/
def fixedLinePoleProfile (Y a gamma : ℝ) (c : ℂ) (x : ℝ) : ℂ :=
  c / (((x : ℂ) + (Y : ℂ) * I) - ((-gamma : ℝ) : ℂ) - (a : ℂ) * I)

/-- The causal contour-jump mode produced by the same pole. -/
def crossedPoleResidueProfile (a gamma : ℝ) (c : ℂ) (t : ℝ) : ℂ :=
  c * Complex.exp (-((a : ℂ) * t) + I * (gamma : ℂ) * t)

theorem norm_fixedLinePoleProfile_sq (Y a gamma : ℝ) (c : ℂ) (x : ℝ) :
    ‖fixedLinePoleProfile Y a gamma c x‖ ^ 2 =
      ‖c‖ ^ 2 * (((Y - a) ^ 2 + (x + gamma) ^ 2)⁻¹) := by
  rw [fixedLinePoleProfile, norm_div, div_pow]
  have hden :
      ‖(x : ℂ) + (Y : ℂ) * I - ((-gamma : ℝ) : ℂ) - (a : ℂ) * I‖ ^ 2 =
        (Y - a) ^ 2 + (x + gamma) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  rw [hden, div_eq_mul_inv]

theorem integral_norm_sq_fixedLinePoleProfile
    {Y a : ℝ} (hYa : a < Y) (gamma : ℝ) (c : ℂ) :
    (∫ x : ℝ, ‖fixedLinePoleProfile Y a gamma c x‖ ^ 2) =
      Real.pi * ‖c‖ ^ 2 / (Y - a) := by
  have hpos : 0 < Y - a := sub_pos.mpr hYa
  have hshift :
      (∫ x : ℝ, (((Y - a) ^ 2 + (x + gamma) ^ 2)⁻¹)) =
        ∫ x : ℝ, (((Y - a) ^ 2 + x ^ 2)⁻¹) := by
    simpa only using
      (integral_add_right_eq_self
        (fun x : ℝ => (((Y - a) ^ 2 + x ^ 2)⁻¹)) gamma)
  simp_rw [norm_fixedLinePoleProfile_sq]
  rw [integral_const_mul, hshift, integral_inv_sq_add_sq_univ hpos]
  field_simp [ne_of_gt hpos]

theorem norm_crossedPoleResidueProfile_sq
    (a gamma : ℝ) (c : ℂ) (t : ℝ) :
    ‖crossedPoleResidueProfile a gamma c t‖ ^ 2 =
      ‖c‖ ^ 2 * Real.exp (-2 * a * t) := by
  rw [crossedPoleResidueProfile, norm_mul, mul_pow, Complex.norm_exp]
  simp only [add_re, neg_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero,
    I_re, I_im, mul_zero, add_zero]
  have hexp : Real.exp (-(a * t)) ^ 2 = Real.exp (-2 * a * t) := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  rw [hexp]

theorem integral_norm_sq_crossedPoleResidueProfile
    {a : ℝ} (ha : 0 < a) (gamma : ℝ) (c : ℂ) :
    (∫ t in Ioi (0 : ℝ), ‖crossedPoleResidueProfile a gamma c t‖ ^ 2) =
      ‖c‖ ^ 2 / (2 * a) := by
  simp_rw [norm_crossedPoleResidueProfile_sq]
  rw [integral_const_mul, integral_exp_mul_Ioi (by linarith : -2 * a < 0) 0]
  simp only [mul_zero, Real.exp_zero]
  field_simp [ne_of_gt ha]

/-- Exact amplification from a fixed Euler line to the crossed residue channel. -/
theorem crossedPole_energy_ratio
    {Y a : ℝ} (ha : 0 < a) (hYa : a < Y) (gamma : ℝ) {c : ℂ} (hc : c ≠ 0) :
    (∫ t in Ioi (0 : ℝ), ‖crossedPoleResidueProfile a gamma c t‖ ^ 2) /
        (∫ x : ℝ, ‖fixedLinePoleProfile Y a gamma c x‖ ^ 2) =
      (Y - a) / (2 * Real.pi * a) := by
  rw [integral_norm_sq_crossedPoleResidueProfile ha,
    integral_norm_sq_fixedLinePoleProfile hYa]
  have hcNorm : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp [hcNorm, ne_of_gt ha, hpi]

/-- No finite squared operator bound can dominate all pole depths on a fixed line. -/
theorem exists_crossedPole_energy_ratio_gt
    {Y M : ℝ} (hY : 0 < Y) :
    ∃ a : ℝ, 0 < a ∧ a < Y ∧
      M ^ 2 < (Y - a) / (2 * Real.pi * a) := by
  let D : ℝ := 2 + 2 * Real.pi * M ^ 2
  have hD : 1 < D := by
    dsimp [D]
    nlinarith [Real.pi_pos, sq_nonneg M]
  have hD0 : 0 < D := lt_trans zero_lt_one hD
  refine ⟨Y / D, div_pos hY hD0, ?_, ?_⟩
  · exact (div_lt_iff₀ hD0).2 (by nlinarith [hY])
  · have hpi : 0 < Real.pi := Real.pi_pos
    have hY0 : Y ≠ 0 := ne_of_gt hY
    have hDne : D ≠ 0 := ne_of_gt hD0
    dsimp [D] at *
    field_simp [hY0, hDne, ne_of_gt hpi]
    nlinarith [hY, hpi]

/-- There is no uniform fixed-line energy bound for all contour-crossing depths. -/
theorem no_uniform_crossedPole_energy_bound {Y : ℝ} (hY : 0 < Y) :
    ¬ ∃ M : ℝ, ∀ a : ℝ, 0 < a → a < Y → ∀ gamma : ℝ,
      (∫ t in Ioi (0 : ℝ), ‖crossedPoleResidueProfile a gamma 1 t‖ ^ 2) ≤
        M ^ 2 * (∫ x : ℝ, ‖fixedLinePoleProfile Y a gamma 1 x‖ ^ 2) := by
  rintro ⟨M, hM⟩
  obtain ⟨a, ha, hYa, hratio⟩ := exists_crossedPole_energy_ratio_gt (Y := Y) (M := M) hY
  have hinput :
      0 < ∫ x : ℝ, ‖fixedLinePoleProfile Y a 0 1 x‖ ^ 2 := by
    rw [integral_norm_sq_fixedLinePoleProfile hYa]
    norm_num
    exact div_pos Real.pi_pos (sub_pos.mpr hYa)
  have hratio_le :
      (∫ t in Ioi (0 : ℝ), ‖crossedPoleResidueProfile a 0 1 t‖ ^ 2) /
          (∫ x : ℝ, ‖fixedLinePoleProfile Y a 0 1 x‖ ^ 2) ≤ M ^ 2 :=
    (div_le_iff₀ hinput).2 (hM a ha hYa 0)
  rw [crossedPole_energy_ratio ha hYa 0 (by norm_num : (1 : ℂ) ≠ 0)] at hratio_le
  exact (not_lt_of_ge hratio_le) hratio

/-- Positive carrier law: any domain estimate for the residue map must pay the inverse-horizontal
charge in its domain budget. -/
theorem domainBudget_ge_inverseHorizontalCharge
    {a M D : ℝ} (ha : 0 < a) (hM : 0 < M) (gamma : ℝ) (c : ℂ)
    (hbound :
      (∫ t in Ioi (0 : ℝ), ‖crossedPoleResidueProfile a gamma c t‖ ^ 2) ≤
        M ^ 2 * D) :
    (‖c‖ ^ 2 / (2 * a)) / M ^ 2 ≤ D := by
  rw [integral_norm_sq_crossedPoleResidueProfile ha] at hbound
  apply (div_le_iff₀ (sq_pos_of_pos hM)).2
  simpa [mul_comm] using hbound

/-- The two right-half members of a centered FE--Schwarz quartet have common depth `a`. -/
def symmetricQuartetDepth (a : ℝ) (_j : Fin 2) : ℝ := a

/-- The two right-half ordinates of a centered FE--Schwarz quartet are `gamma` and `-gamma`. -/
def symmetricQuartetHeight (gamma : ℝ) (j : Fin 2) : ℝ :=
  if j = 0 then gamma else -gamma

/-- Both right-half members of a multiplicity-`m` quartet carry multiplicity `m`. -/
def symmetricQuartetMultiplicity (m : ℕ) (_j : Fin 2) : ℕ := m

/-- The actual two right-half zero locations of the centered quartet gauge. -/
def symmetricQuartetPoint (a gamma : ℝ) (j : Fin 2) : ℂ :=
  (1 / 2 : ℂ) + (a : ℂ) + (symmetricQuartetHeight gamma j : ℂ) * I

/-- The Cauchy-energy pair is exactly the right-half pair of the formalized FE--Schwarz gauge. -/
theorem centeredQuartetGauge_symmetricQuartetPoint_zero
    (a gamma : ℝ) (j : Fin 2) :
    centeredQuartetGauge a gamma (symmetricQuartetPoint a gamma j) = 0 := by
  fin_cases j
  · simpa [symmetricQuartetPoint, symmetricQuartetHeight, quartetPoint] using
      centeredQuartetGauge_quartetPoint a gamma
  · have hsign : centeredQuartetGauge a gamma = centeredQuartetGauge a (-gamma) := by
      funext s
      simp only [centeredQuartetGauge]
      push_cast
      ring
    rw [hsign]
    simpa [symmetricQuartetPoint, symmetricQuartetHeight, quartetPoint] using
      centeredQuartetGauge_quartetPoint a (-gamma)

/-- Exact Cauchy energy of the two crossed right-half modes in a centered FE--Schwarz quartet. -/
theorem symmetricQuartet_cauchyEnergy
    {a : ℝ} (ha : 0 < a) (gamma : ℝ) (m : ℕ) :
    finiteOfflineCauchyEnergy (symmetricQuartetDepth a)
        (symmetricQuartetHeight gamma) (symmetricQuartetMultiplicity m) =
      4 * (m : ℝ) ^ 2 / a +
        4 * (m : ℝ) ^ 2 * a / (a ^ 2 + gamma ^ 2) := by
  simp [finiteOfflineCauchyEnergy, symmetricQuartetDepth, symmetricQuartetHeight,
    symmetricQuartetMultiplicity, transverseCauchyKernel]
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hsum0 : a ^ 2 + gamma ^ 2 ≠ 0 := by positivity
  field_simp [ha0, hsum0]
  ring

/-- The symmetric quartet profile has the exact paper energy, now as an actual `L²` integral. -/
theorem integral_norm_sq_symmetricQuartetProfile
    {a : ℝ} (ha : 0 < a) (gamma : ℝ) (m : ℕ) :
    (∫ t in Ioi (0 : ℝ),
        ‖finiteOfflineProfile (symmetricQuartetDepth a)
          (symmetricQuartetHeight gamma) (symmetricQuartetMultiplicity m) t‖ ^ 2) =
      4 * (m : ℝ) ^ 2 / a +
        4 * (m : ℝ) ^ 2 * a / (a ^ 2 + gamma ^ 2) := by
  calc
    (∫ t in Ioi (0 : ℝ),
        ‖finiteOfflineProfile (symmetricQuartetDepth a)
          (symmetricQuartetHeight gamma) (symmetricQuartetMultiplicity m) t‖ ^ 2) =
        finiteOfflineCauchyEnergy (symmetricQuartetDepth a)
          (symmetricQuartetHeight gamma) (symmetricQuartetMultiplicity m) :=
      integral_norm_sq_finiteOfflineProfile
        (symmetricQuartetMultiplicity m) (fun _ => ha)
    _ = 4 * (m : ℝ) ^ 2 / a +
        4 * (m : ℝ) ^ 2 * a / (a ^ 2 + gamma ^ 2) :=
      symmetricQuartet_cauchyEnergy ha gamma m

/-- A nonzero symmetric quartet already pays at least the inverse-horizontal charge `4m²/a`. -/
theorem symmetricQuartet_cauchyEnergy_ge_inverseHorizontal
    {a : ℝ} (ha : 0 < a) (gamma : ℝ) (m : ℕ) :
    4 * (m : ℝ) ^ 2 / a ≤
      finiteOfflineCauchyEnergy (symmetricQuartetDepth a)
        (symmetricQuartetHeight gamma) (symmetricQuartetMultiplicity m) := by
  rw [symmetricQuartet_cauchyEnergy ha]
  exact le_add_of_nonneg_right (by positivity)

end RHTower
