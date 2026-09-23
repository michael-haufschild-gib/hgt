import GaloisForLFunctions.RHTower.FiniteOfflineCauchyL2
import GaloisForLFunctions.RHTower.XiThetaSquareRateBoundary
import GaloisForLFunctions.RHTower.XiRationalQuartetGauge
import GaloisForLFunctions.HTGeometry.WeightedHolder
import GaloisForLFunctions.HTGeometry.PoissonKernelIntegrals
import GaloisForLFunctions.HTGeometry.AnalyticBallFinsetFactorization

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
    ‖fixedLinePoleProfile Y a gamma c x‖ ^ (2 : ℕ) =
      ‖c‖ ^ (2 : ℕ) * (((Y - a) ^ (2 : ℕ) + (x + gamma) ^ (2 : ℕ))⁻¹) := by
  rw [fixedLinePoleProfile, norm_div, div_pow]
  have hden :
      ‖(x : ℂ) + (Y : ℂ) * I - ((-gamma : ℝ) : ℂ) - (a : ℂ) * I‖ ^ (2 : ℕ) =
        (Y - a) ^ (2 : ℕ) + (x + gamma) ^ (2 : ℕ) := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  rw [hden, div_eq_mul_inv]

theorem integral_norm_sq_fixedLinePoleProfile
    {Y a : ℝ} (hYa : a < Y) (gamma : ℝ) (c : ℂ) :
    (∫ x : ℝ, ‖fixedLinePoleProfile Y a gamma c x‖ ^ (2 : ℕ)) =
      Real.pi * ‖c‖ ^ (2 : ℕ) / (Y - a) := by
  have hpos : 0 < Y - a := sub_pos.mpr hYa
  have hshift :
      (∫ x : ℝ, (((Y - a) ^ (2 : ℕ) + (x + gamma) ^ (2 : ℕ))⁻¹)) =
        ∫ x : ℝ, (((Y - a) ^ (2 : ℕ) + x ^ (2 : ℕ))⁻¹) := by
    simpa only using
      (integral_add_right_eq_self
        (fun x : ℝ => (((Y - a) ^ (2 : ℕ) + x ^ (2 : ℕ))⁻¹)) gamma)
  simp_rw [norm_fixedLinePoleProfile_sq]
  rw [integral_const_mul, hshift, integral_inv_sq_add_sq_univ hpos]
  field_simp [ne_of_gt hpos]

/-- A pole strictly below the sampling line gives a continuous boundary profile. -/
theorem continuous_fixedLinePoleProfile
    {Y a : ℝ} (hYa : a < Y) (gamma : ℝ) (c : ℂ) :
    Continuous (fixedLinePoleProfile Y a gamma c) := by
  unfold fixedLinePoleProfile
  refine continuous_const.div (by fun_prop) ?_
  intro x hx
  have him := congrArg Complex.im hx
  simp at him
  linarith

/-- The squared boundary profile of a pole below the sampling line is integrable. -/
theorem integrable_norm_sq_fixedLinePoleProfile
    {Y a : ℝ} (hYa : a < Y) (gamma : ℝ) (c : ℂ) :
    Integrable (fun x : ℝ => ‖fixedLinePoleProfile Y a gamma c x‖ ^ (2 : ℕ)) := by
  have hpos : 0 < Y - a := sub_pos.mpr hYa
  have hbase : Integrable (fun x : ℝ => (((Y - a) ^ (2 : ℕ) + (x + gamma) ^ (2 : ℕ))⁻¹)) :=
    (GaloisForLFunctions.HTGeometry.integrable_inv_sq_add_sq hpos).comp_add_right gamma
  simpa only [norm_fixedLinePoleProfile_sq] using hbase.const_mul (‖c‖ ^ (2 : ℕ))

/-- One of the four fixed-line Cauchy terms of the multiplicity-`m` symmetric quartet
logarithmic-source correction. The common residue is `-2mi`. -/
def symmetricQuartetFixedLineTerm
    (Y a gamma : ℝ) (m : ℕ) (j : Fin 4) (x : ℝ) : ℂ :=
  ![fixedLinePoleProfile Y a gamma (-(2 : ℂ) * (m : ℂ) * I) x,
    fixedLinePoleProfile Y a (-gamma) (-(2 : ℂ) * (m : ℂ) * I) x,
    fixedLinePoleProfile Y (-a) gamma (-(2 : ℂ) * (m : ℂ) * I) x,
    fixedLinePoleProfile Y (-a) (-gamma) (-(2 : ℂ) * (m : ℂ) * I) x] j

/-- The actual four-pole symmetric logarithmic-source correction sampled on `Im z = Y`. -/
def symmetricQuartetFixedLineProfile
    (Y a gamma : ℝ) (m : ℕ) (x : ℝ) : ℂ :=
  ∑ j : Fin 4, symmetricQuartetFixedLineTerm Y a gamma m j x

/-- The four zeros of the centered quartet gauge, with repetitions retained when `gamma = 0`. -/
def symmetricQuartetRoot (a gamma : ℝ) (j : Fin 4) : ℂ :=
  ![(1 / 2 : ℂ) + a + gamma * I,
    (1 / 2 : ℂ) + a - gamma * I,
    (1 / 2 : ℂ) - a + gamma * I,
    (1 / 2 : ℂ) - a - gamma * I] j

/-- The paper's completed logarithmic-source correction
`-2 Dlog(centeredQuartetGauge(a,gamma)^m)(1/2-iz)`. -/
def symmetricQuartetLogSourceCorrection
    (a gamma : ℝ) (m : ℕ) (z : ℂ) : ℂ :=
  -2 * logDeriv (fun s => centeredQuartetGauge a gamma s ^ m) ((1 / 2 : ℂ) - I * z)

/-- Exact four-pole partial fraction of the symmetric logarithmic-source correction on a line
strictly above the quartet. This identifies the fixed-line profile with the actual rational gauge,
including its common residue `-2mi`. -/
theorem symmetricQuartetLogSourceCorrection_fixedLine
    {Y a : ℝ} (ha : 0 < a) (hYa : a < Y) (gamma : ℝ) (m : ℕ) (x : ℝ) :
    symmetricQuartetLogSourceCorrection a gamma m ((x : ℂ) + (Y : ℂ) * I) =
      symmetricQuartetFixedLineProfile Y a gamma m x := by
  let s : ℂ := (1 / 2 : ℂ) - I * ((x : ℂ) + (Y : ℂ) * I)
  have hne : ∀ j : Fin 4, s ≠ symmetricQuartetRoot a gamma j := by
    intro j
    fin_cases j <;> intro h <;>
      have hre := congrArg Complex.re h <;>
      simp [s, symmetricQuartetRoot] at hre <;> linarith
  have hfactor :
      (fun w : ℂ => centeredQuartetGauge a gamma w ^ m) =
        fun w => ∏ j : Fin 4, (w - symmetricQuartetRoot a gamma j) ^ m := by
    funext w
    rw [Finset.prod_pow]
    congr 1
    rw [Fin.prod_univ_four]
    simp [symmetricQuartetRoot, centeredQuartetGauge]
    ring_nf
    rw [Complex.I_sq]
    have hI4 : (I : ℂ) ^ (4 : ℕ) = 1 := by
      calc
        (I : ℂ) ^ (4 : ℕ) = ((I : ℂ) ^ (2 : ℕ)) ^ (2 : ℕ) := by ring
        _ = 1 := by rw [Complex.I_sq]; norm_num
    rw [hI4]
    ring
  rw [symmetricQuartetLogSourceCorrection, hfactor]
  change -2 * logDeriv
      (fun w => ∏ j : Fin 4, (w - symmetricQuartetRoot a gamma j) ^ m) s = _
  rw [logDeriv_prod (𝕜 := ℂ) (𝕜' := ℂ) (s := Finset.univ)
    (f := fun j w => (w - symmetricQuartetRoot a gamma j) ^ m)
    (fun j _ => pow_ne_zero _ (sub_ne_zero.mpr (hne j)))
    (fun _ _ => by fun_prop)]
  simp_rw [HTGeometry.logDeriv_sub_const_pow m (hne _)]
  have hd0 : (x : ℂ) + (Y : ℂ) * I + gamma - a * I ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp at him
    linarith
  have hd1 : (x : ℂ) + (Y : ℂ) * I - gamma - a * I ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp at him
    linarith
  have hd2 : (x : ℂ) + (Y : ℂ) * I + gamma + a * I ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp at him
    linarith
  have hd3 : (x : ℂ) + (Y : ℂ) * I - gamma + a * I ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp at him
    linarith
  have hq0 : (m : ℂ) / (s - symmetricQuartetRoot a gamma 0) =
      (m : ℂ) * I / ((x : ℂ) + (Y : ℂ) * I + gamma - a * I) := by
    have heq : s - symmetricQuartetRoot a gamma 0 =
        -I * ((x : ℂ) + (Y : ℂ) * I + gamma - a * I) := by
      simp [s, symmetricQuartetRoot]
      ring_nf
      rw [Complex.I_sq]
      ring
    rw [heq]
    field_simp [hd0]
    rw [Complex.I_sq]
    ring
  have hq1 : (m : ℂ) / (s - symmetricQuartetRoot a gamma 1) =
      (m : ℂ) * I / ((x : ℂ) + (Y : ℂ) * I - gamma - a * I) := by
    have heq : s - symmetricQuartetRoot a gamma 1 =
        -I * ((x : ℂ) + (Y : ℂ) * I - gamma - a * I) := by
      simp [s, symmetricQuartetRoot]
      ring_nf
      rw [Complex.I_sq]
      ring
    rw [heq]
    field_simp [hd1]
    rw [Complex.I_sq]
    ring
  have hq2 : (m : ℂ) / (s - symmetricQuartetRoot a gamma 2) =
      (m : ℂ) * I / ((x : ℂ) + (Y : ℂ) * I + gamma + a * I) := by
    have heq : s - symmetricQuartetRoot a gamma 2 =
        -I * ((x : ℂ) + (Y : ℂ) * I + gamma + a * I) := by
      simp [s, symmetricQuartetRoot]
      ring_nf
      rw [Complex.I_sq]
      ring
    rw [heq]
    field_simp [hd2]
    rw [Complex.I_sq]
    ring
  have hq3 : (m : ℂ) / (s - symmetricQuartetRoot a gamma 3) =
      (m : ℂ) * I / ((x : ℂ) + (Y : ℂ) * I - gamma + a * I) := by
    have heq : s - symmetricQuartetRoot a gamma 3 =
        -I * ((x : ℂ) + (Y : ℂ) * I - gamma + a * I) := by
      simp [s, symmetricQuartetRoot]
      ring_nf
      rw [Complex.I_sq]
      ring
    rw [heq]
    field_simp [hd3]
    rw [Complex.I_sq]
    ring
  rw [Fin.sum_univ_four, hq0, hq1, hq2, hq3]
  simp [symmetricQuartetFixedLineProfile, symmetricQuartetFixedLineTerm,
    fixedLinePoleProfile, Fin.sum_univ_four]
  ring

theorem norm_crossedPoleResidueProfile_sq
    (a gamma : ℝ) (c : ℂ) (t : ℝ) :
    ‖crossedPoleResidueProfile a gamma c t‖ ^ (2 : ℕ) =
      ‖c‖ ^ (2 : ℕ) * Real.exp (-2 * a * t) := by
  rw [crossedPoleResidueProfile, norm_mul, mul_pow, Complex.norm_exp]
  simp only [add_re, neg_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero,
    I_re, I_im, mul_zero, add_zero]
  have hexp : Real.exp (-(a * t)) ^ (2 : ℕ) = Real.exp (-2 * a * t) := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  rw [hexp]

theorem integral_norm_sq_crossedPoleResidueProfile
    {a : ℝ} (ha : 0 < a) (gamma : ℝ) (c : ℂ) :
    (∫ t in Ioi (0 : ℝ), ‖crossedPoleResidueProfile a gamma c t‖ ^ (2 : ℕ)) =
      ‖c‖ ^ (2 : ℕ) / (2 * a) := by
  simp_rw [norm_crossedPoleResidueProfile_sq]
  rw [integral_const_mul, integral_exp_mul_Ioi (by linarith : -2 * a < 0) 0]
  simp only [mul_zero, Real.exp_zero]
  field_simp [ne_of_gt ha]

/-- Exact amplification from a fixed Euler line to the crossed residue channel. -/
theorem crossedPole_energy_ratio
    {Y a : ℝ} (ha : 0 < a) (hYa : a < Y) (gamma : ℝ) {c : ℂ} (hc : c ≠ 0) :
    (∫ t in Ioi (0 : ℝ), ‖crossedPoleResidueProfile a gamma c t‖ ^ (2 : ℕ)) /
        (∫ x : ℝ, ‖fixedLinePoleProfile Y a gamma c x‖ ^ (2 : ℕ)) =
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
      M ^ (2 : ℕ) < (Y - a) / (2 * Real.pi * a) := by
  let D : ℝ := 2 + 2 * Real.pi * M ^ (2 : ℕ)
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
      (∫ t in Ioi (0 : ℝ), ‖crossedPoleResidueProfile a gamma 1 t‖ ^ (2 : ℕ)) ≤
        M ^ (2 : ℕ) * (∫ x : ℝ, ‖fixedLinePoleProfile Y a gamma 1 x‖ ^ (2 : ℕ)) := by
  rintro ⟨M, hM⟩
  obtain ⟨a, ha, hYa, hratio⟩ := exists_crossedPole_energy_ratio_gt (Y := Y) (M := M) hY
  have hinput :
      0 < ∫ x : ℝ, ‖fixedLinePoleProfile Y a 0 1 x‖ ^ (2 : ℕ) := by
    rw [integral_norm_sq_fixedLinePoleProfile hYa]
    norm_num
    exact div_pos Real.pi_pos (sub_pos.mpr hYa)
  have hratio_le :
      (∫ t in Ioi (0 : ℝ), ‖crossedPoleResidueProfile a 0 1 t‖ ^ (2 : ℕ)) /
          (∫ x : ℝ, ‖fixedLinePoleProfile Y a 0 1 x‖ ^ (2 : ℕ)) ≤ M ^ (2 : ℕ) :=
    (div_le_iff₀ hinput).2 (hM a ha hYa 0)
  rw [crossedPole_energy_ratio ha hYa 0 (by norm_num : (1 : ℂ) ≠ 0)] at hratio_le
  exact (not_lt_of_ge hratio_le) hratio

/-- Positive carrier law: any domain estimate for the residue map must pay the inverse-horizontal
charge in its domain budget. -/
theorem domainBudget_ge_inverseHorizontalCharge
    {a M D : ℝ} (ha : 0 < a) (hM : 0 < M) (gamma : ℝ) (c : ℂ)
    (hbound :
      (∫ t in Ioi (0 : ℝ), ‖crossedPoleResidueProfile a gamma c t‖ ^ (2 : ℕ)) ≤
        M ^ (2 : ℕ) * D) :
    (‖c‖ ^ (2 : ℕ) / (2 * a)) / M ^ (2 : ℕ) ≤ D := by
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
      4 * (m : ℝ) ^ (2 : ℕ) / a +
        4 * (m : ℝ) ^ (2 : ℕ) * a / (a ^ (2 : ℕ) + gamma ^ (2 : ℕ)) := by
  simp [finiteOfflineCauchyEnergy, symmetricQuartetDepth, symmetricQuartetHeight,
    symmetricQuartetMultiplicity, transverseCauchyKernel]
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hsum0 : a ^ (2 : ℕ) + gamma ^ (2 : ℕ) ≠ 0 := by positivity
  field_simp [ha0, hsum0]
  ring

/-- The symmetric quartet profile has the exact paper energy, now as an actual `L²` integral. -/
theorem integral_norm_sq_symmetricQuartetProfile
    {a : ℝ} (ha : 0 < a) (gamma : ℝ) (m : ℕ) :
    (∫ t in Ioi (0 : ℝ),
        ‖finiteOfflineProfile (symmetricQuartetDepth a)
          (symmetricQuartetHeight gamma) (symmetricQuartetMultiplicity m) t‖ ^ (2 : ℕ)) =
      4 * (m : ℝ) ^ (2 : ℕ) / a +
        4 * (m : ℝ) ^ (2 : ℕ) * a / (a ^ (2 : ℕ) + gamma ^ (2 : ℕ)) := by
  calc
    (∫ t in Ioi (0 : ℝ),
        ‖finiteOfflineProfile (symmetricQuartetDepth a)
          (symmetricQuartetHeight gamma) (symmetricQuartetMultiplicity m) t‖ ^ (2 : ℕ)) =
        finiteOfflineCauchyEnergy (symmetricQuartetDepth a)
          (symmetricQuartetHeight gamma) (symmetricQuartetMultiplicity m) :=
      integral_norm_sq_finiteOfflineProfile
        (symmetricQuartetMultiplicity m) (fun _ => ha)
    _ = 4 * (m : ℝ) ^ (2 : ℕ) / a +
        4 * (m : ℝ) ^ (2 : ℕ) * a / (a ^ (2 : ℕ) + gamma ^ (2 : ℕ)) :=
      symmetricQuartet_cauchyEnergy ha gamma m

/-- A nonzero symmetric quartet already pays at least the inverse-horizontal charge `4m²/a`. -/
theorem symmetricQuartet_cauchyEnergy_ge_inverseHorizontal
    {a : ℝ} (ha : 0 < a) (gamma : ℝ) (m : ℕ) :
    4 * (m : ℝ) ^ (2 : ℕ) / a ≤
      finiteOfflineCauchyEnergy (symmetricQuartetDepth a)
        (symmetricQuartetHeight gamma) (symmetricQuartetMultiplicity m) := by
  rw [symmetricQuartet_cauchyEnergy ha]
  exact le_add_of_nonneg_right (by positivity)

/-- Exact four-pole fixed-line triangle estimate. This is equation (16) of the paper card. -/
theorem sqrt_integral_norm_sq_symmetricQuartetFixedLineProfile_le
    {Y a : ℝ} (ha : 0 < a) (hYa : a < Y) (gamma : ℝ) (m : ℕ) :
    Real.sqrt (∫ x : ℝ, ‖symmetricQuartetFixedLineProfile Y a gamma m x‖ ^ (2 : ℕ)) ≤
      4 * (m : ℝ) * Real.sqrt Real.pi *
        (1 / Real.sqrt (Y - a) + 1 / Real.sqrt (Y + a)) := by
  have hYna : -a < Y := by linarith
  let g : Fin 4 → ℝ → ℂ := symmetricQuartetFixedLineTerm Y a gamma m
  have hm : ∀ j ∈ (Finset.univ : Finset (Fin 4)),
      AEStronglyMeasurable (g j) := by
    intro j _
    fin_cases j
    · change AEStronglyMeasurable
        (fixedLinePoleProfile Y a gamma (-(2 : ℂ) * (m : ℂ) * I)) volume
      exact (continuous_fixedLinePoleProfile hYa _ _).aestronglyMeasurable
    · change AEStronglyMeasurable
        (fixedLinePoleProfile Y a (-gamma) (-(2 : ℂ) * (m : ℂ) * I)) volume
      exact (continuous_fixedLinePoleProfile hYa _ _).aestronglyMeasurable
    · change AEStronglyMeasurable
        (fixedLinePoleProfile Y (-a) gamma (-(2 : ℂ) * (m : ℂ) * I)) volume
      exact (continuous_fixedLinePoleProfile hYna _ _).aestronglyMeasurable
    · change AEStronglyMeasurable
        (fixedLinePoleProfile Y (-a) (-gamma) (-(2 : ℂ) * (m : ℂ) * I)) volume
      exact (continuous_fixedLinePoleProfile hYna _ _).aestronglyMeasurable
  have hi : ∀ j ∈ (Finset.univ : Finset (Fin 4)),
      Integrable (fun x : ℝ => ‖g j x‖ ^ (2 : ℕ)) := by
    intro j _
    fin_cases j
    · change Integrable (fun x : ℝ =>
        ‖fixedLinePoleProfile Y a gamma (-(2 : ℂ) * (m : ℂ) * I) x‖ ^ (2 : ℕ))
      exact integrable_norm_sq_fixedLinePoleProfile hYa _ _
    · change Integrable (fun x : ℝ =>
        ‖fixedLinePoleProfile Y a (-gamma) (-(2 : ℂ) * (m : ℂ) * I) x‖ ^ (2 : ℕ))
      exact integrable_norm_sq_fixedLinePoleProfile hYa _ _
    · change Integrable (fun x : ℝ =>
        ‖fixedLinePoleProfile Y (-a) gamma (-(2 : ℂ) * (m : ℂ) * I) x‖ ^ (2 : ℕ))
      exact integrable_norm_sq_fixedLinePoleProfile hYna _ _
    · change Integrable (fun x : ℝ =>
        ‖fixedLinePoleProfile Y (-a) (-gamma) (-(2 : ℂ) * (m : ℂ) * I) x‖ ^ (2 : ℕ))
      exact integrable_norm_sq_fixedLinePoleProfile hYna _ _
  have hM := GaloisForLFunctions.HTGeometry.sqrt_integral_normSq_sum_le_measure
    (Finset.univ : Finset (Fin 4)) g hm hi
  change Real.sqrt (∫ x : ℝ,
      ‖∑ j : Fin 4, symmetricQuartetFixedLineTerm Y a gamma m j x‖ ^ (2 : ℕ)) ≤ _
  have hM' : Real.sqrt (∫ x : ℝ,
      ‖∑ j : Fin 4, symmetricQuartetFixedLineTerm Y a gamma m j x‖ ^ (2 : ℕ)) ≤
      ∑ j : Fin 4, Real.sqrt (∫ x : ℝ,
        ‖symmetricQuartetFixedLineTerm Y a gamma m j x‖ ^ (2 : ℕ)) := by
    simpa [g] using hM
  rw [Fin.sum_univ_four] at hM'
  simp [symmetricQuartetFixedLineTerm,
    integral_norm_sq_fixedLinePoleProfile hYa,
    integral_norm_sq_fixedLinePoleProfile hYna] at hM'
  have hpi : 0 ≤ Real.pi := Real.pi_pos.le
  have hma : 0 ≤ (2 : ℝ) * m := by positivity
  have hsqrt (b : ℝ) (hb : 0 < b) :
      Real.sqrt (Real.pi * ((2 : ℝ) * m) ^ (2 : ℕ) / b) =
        2 * (m : ℝ) * Real.sqrt Real.pi / Real.sqrt b := by
    rw [Real.sqrt_div (mul_nonneg hpi (sq_nonneg _)),
      Real.sqrt_mul hpi, Real.sqrt_sq_eq_abs, abs_of_nonneg hma]
    ring
  rw [hsqrt (Y - a) (sub_pos.mpr hYa), hsqrt (Y + a) (by linarith)] at hM'
  calc
    Real.sqrt (∫ x : ℝ,
        ‖∑ j : Fin 4, symmetricQuartetFixedLineTerm Y a gamma m j x‖ ^ (2 : ℕ)) ≤
        2 * (m : ℝ) * Real.sqrt Real.pi / Real.sqrt (Y - a) +
          2 * (m : ℝ) * Real.sqrt Real.pi / Real.sqrt (Y - a) +
          2 * (m : ℝ) * Real.sqrt Real.pi / Real.sqrt (Y + a) +
          2 * (m : ℝ) * Real.sqrt Real.pi / Real.sqrt (Y + a) := by
      simpa [symmetricQuartetFixedLineTerm] using hM'
    _ = 4 * (m : ℝ) * Real.sqrt Real.pi *
        (1 / Real.sqrt (Y - a) + 1 / Real.sqrt (Y + a)) := by ring

/-- Uniform four-pole fixed-line energy bound for `0 < a ≤ Y/2`. This is equation (17). -/
theorem integral_norm_sq_symmetricQuartetFixedLineProfile_le
    {Y a : ℝ} (ha : 0 < a) (haY : a ≤ Y / 2) (gamma : ℝ) (m : ℕ) :
    (∫ x : ℝ, ‖symmetricQuartetFixedLineProfile Y a gamma m x‖ ^ (2 : ℕ)) ≤
      16 * (m : ℝ) ^ (2 : ℕ) * Real.pi * (3 + 2 * Real.sqrt 2) / Y := by
  have hY : 0 < Y := by linarith
  have hYa : a < Y := by linarith
  have hYpa : 0 < Y + a := by linarith
  have hYma : 0 < Y - a := by linarith
  have hfracA : 1 / (Y - a) ≤ 2 / Y := by
    exact (div_le_div_iff₀ hYma hY).2 (by linarith)
  have hA : 1 / Real.sqrt (Y - a) ≤ Real.sqrt 2 / Real.sqrt Y := by
    rw [show 1 / Real.sqrt (Y - a) = Real.sqrt (1 / (Y - a)) by
        rw [Real.sqrt_div (show 0 ≤ (1 : ℝ) by positivity), Real.sqrt_one],
      show Real.sqrt 2 / Real.sqrt Y = Real.sqrt (2 / Y) by
        rw [Real.sqrt_div (show 0 ≤ (2 : ℝ) by positivity)]]
    simpa using Real.sqrt_le_sqrt hfracA
  have hfracB : 1 / (Y + a) ≤ 1 / Y := by
    exact (div_le_div_iff₀ hYpa hY).2 (by linarith)
  have hB : 1 / Real.sqrt (Y + a) ≤ 1 / Real.sqrt Y := by
    rw [show 1 / Real.sqrt (Y + a) = Real.sqrt (1 / (Y + a)) by
        rw [Real.sqrt_div (show 0 ≤ (1 : ℝ) by positivity), Real.sqrt_one],
      show 1 / Real.sqrt Y = Real.sqrt (1 / Y) by
        rw [Real.sqrt_div (show 0 ≤ (1 : ℝ) by positivity), Real.sqrt_one]]
    simpa using Real.sqrt_le_sqrt hfracB
  have hsum :
      1 / Real.sqrt (Y - a) + 1 / Real.sqrt (Y + a) ≤
        (Real.sqrt 2 + 1) / Real.sqrt Y := by
    calc
      1 / Real.sqrt (Y - a) + 1 / Real.sqrt (Y + a) ≤
          Real.sqrt 2 / Real.sqrt Y + 1 / Real.sqrt Y := add_le_add hA hB
      _ = (Real.sqrt 2 + 1) / Real.sqrt Y := by ring
  have hK : 0 ≤ 4 * (m : ℝ) * Real.sqrt Real.pi := by positivity
  have hroot :
      Real.sqrt (∫ x : ℝ,
          ‖symmetricQuartetFixedLineProfile Y a gamma m x‖ ^ (2 : ℕ)) ≤
        4 * (m : ℝ) * Real.sqrt Real.pi *
          ((Real.sqrt 2 + 1) / Real.sqrt Y) :=
    le_trans
      (sqrt_integral_norm_sq_symmetricQuartetFixedLineProfile_le ha hYa gamma m)
      (mul_le_mul_of_nonneg_left hsum hK)
  have hInt : 0 ≤ ∫ x : ℝ,
      ‖symmetricQuartetFixedLineProfile Y a gamma m x‖ ^ (2 : ℕ) :=
    integral_nonneg fun _ => sq_nonneg _
  have hsq := (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).2 hroot
  rw [Real.sq_sqrt hInt] at hsq
  calc
    (∫ x : ℝ, ‖symmetricQuartetFixedLineProfile Y a gamma m x‖ ^ (2 : ℕ)) ≤
        (4 * (m : ℝ) * Real.sqrt Real.pi *
          ((Real.sqrt 2 + 1) / Real.sqrt Y)) ^ (2 : ℕ) := hsq
    _ = 16 * (m : ℝ) ^ (2 : ℕ) * Real.pi * (3 + 2 * Real.sqrt 2) / Y := by
      rw [mul_pow, mul_pow, div_pow, Real.sq_sqrt Real.pi_pos.le,
        Real.sq_sqrt hY.le]
      have h2 : Real.sqrt 2 ^ (2 : ℕ) = 2 :=
        Real.sq_sqrt (show (0 : ℝ) ≤ 2 by positivity)
      field_simp [ne_of_gt hY]
      nlinarith

/-- Any linear energy estimate carrying the symmetric quartet from the fixed line to its crossed
residue profile has the inverse-horizontal squared operator-norm lower bound of equation (18). -/
theorem symmetricQuartet_operatorNorm_sq_ge
    {Y a M : ℝ} (ha : 0 < a) (haY : a ≤ Y / 2) (gamma : ℝ) (m : ℕ)
    (hm : 0 < m)
    (hbound :
      (∫ t in Ioi (0 : ℝ),
          ‖finiteOfflineProfile (symmetricQuartetDepth a)
            (symmetricQuartetHeight gamma) (symmetricQuartetMultiplicity m) t‖ ^ (2 : ℕ)) ≤
        M ^ (2 : ℕ) *
          (∫ x : ℝ,
            ‖symmetricQuartetFixedLineProfile Y a gamma m x‖ ^ (2 : ℕ))) :
    Y / (4 * Real.pi * (3 + 2 * Real.sqrt 2) * a) ≤ M ^ (2 : ℕ) := by
  have hY : 0 < Y := by linarith
  have hc : 0 < 3 + 2 * Real.sqrt 2 := by positivity
  have hinput :=
    integral_norm_sq_symmetricQuartetFixedLineProfile_le ha haY gamma m
  have hcharge :
      4 * (m : ℝ) ^ (2 : ℕ) / a ≤
        (∫ t in Ioi (0 : ℝ),
          ‖finiteOfflineProfile (symmetricQuartetDepth a)
            (symmetricQuartetHeight gamma) (symmetricQuartetMultiplicity m) t‖ ^ (2 : ℕ)) := by
    rw [integral_norm_sq_symmetricQuartetProfile ha]
    exact le_add_of_nonneg_right (by positivity)
  have hchain :
      4 * (m : ℝ) ^ (2 : ℕ) / a ≤
        M ^ (2 : ℕ) * (16 * (m : ℝ) ^ (2 : ℕ) * Real.pi *
          (3 + 2 * Real.sqrt 2) / Y) :=
    le_trans hcharge (le_trans hbound
      (mul_le_mul_of_nonneg_left hinput (sq_nonneg M)))
  have hcross :
      (4 * (m : ℝ) ^ (2 : ℕ)) * Y ≤
        (M ^ (2 : ℕ) * (16 * (m : ℝ) ^ (2 : ℕ) * Real.pi *
          (3 + 2 * Real.sqrt 2))) * a := by
    apply (div_le_div_iff₀ ha hY).1
    calc
      4 * (m : ℝ) ^ (2 : ℕ) / a ≤
          M ^ (2 : ℕ) * (16 * (m : ℝ) ^ (2 : ℕ) * Real.pi *
            (3 + 2 * Real.sqrt 2) / Y) := hchain
      _ = (M ^ (2 : ℕ) * (16 * (m : ℝ) ^ (2 : ℕ) * Real.pi *
            (3 + 2 * Real.sqrt 2))) / Y := by ring
  have hmR : 0 < (4 : ℝ) * (m : ℝ) ^ (2 : ℕ) := by positivity
  have hcancel :
      (4 * (m : ℝ) ^ (2 : ℕ)) * Y ≤
        (4 * (m : ℝ) ^ (2 : ℕ)) *
          (M ^ (2 : ℕ) * (4 * Real.pi * (3 + 2 * Real.sqrt 2) * a)) := by
    calc
      (4 * (m : ℝ) ^ (2 : ℕ)) * Y ≤
          (M ^ (2 : ℕ) * (16 * (m : ℝ) ^ (2 : ℕ) * Real.pi *
            (3 + 2 * Real.sqrt 2))) * a := hcross
      _ = (4 * (m : ℝ) ^ (2 : ℕ)) *
          (M ^ (2 : ℕ) * (4 * Real.pi * (3 + 2 * Real.sqrt 2) * a)) := by ring
  have hYle : Y ≤ M ^ (2 : ℕ) * (4 * Real.pi * (3 + 2 * Real.sqrt 2) * a) :=
    by nlinarith
  exact (div_le_iff₀ (by positivity : 0 < 4 * Real.pi *
    (3 + 2 * Real.sqrt 2) * a)).2 hYle

end RHTower
