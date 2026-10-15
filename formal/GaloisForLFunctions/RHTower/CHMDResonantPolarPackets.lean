import GaloisForLFunctions.RHTower.CHMDStage17ComplexWavePacketFactorizationAndCoshSinhDecomposition
import GaloisForLFunctions.RHTower.CHMDGrowthPositivityCollapseAndTwoPointCriterion
import GaloisForLFunctions.RHTower.XiRealAxisNonvanishing

/-!
# Resonant four-point polar packets

For a zero with Klein–Gordon frequency `u + iv`, set `h = 2π/u` and
`c = cos(h sqrt(7/4))`. The packet at `0,h,2h,3h` with coefficients
`1,-(1+2c),1+2c,-1` has exponential polynomial `(1-q)(1-2cq+q²)`.
Its spectral weight is exactly `8(1-cos(hw))(cos(hw)-c)²`.

The second factor removes the polar frequency. At the selected zero,
`cos(hw) = cosh(hv)`, so its multiplicity-weighted contribution is
`-8 m (cosh(hv)-1)(cosh(hv)-c)² Re(sech²(γ/2))`.
It is nonpositive and vanishes exactly on the critical line.

The complete packet has both an exact zero-side sum and an exact prime–archimedean
formula with no polar term. The selected summand's sign does not determine the
sign of that complete sum.
-/

open Complex MeasureTheory Set Zeta23
open scoped BigOperators ComplexConjugate
noncomputable section
namespace RHTower.CHMDPolarDetector
open WeilOneSided WeilSpectral RHTower.EvenSector
open RHTower.CHMDStage11 RHTower.CHMDStage13 RHTower.CHMDStage17
open RHTower.CHMDGrowthCollapse
open GaloisForLFunctions.HTGeometry (sechSqHalf)

/-- Four equally spaced sampling times. -/
def fourPointTimes (h : ℝ) : Fin 4 → ℝ := ![0, h, 2 * h, 3 * h]
/-- Coefficients of `(1-q)(1-2cq+q²)`. -/
def fourPointCoeff (c : ℝ) : Fin 4 → ℝ := ![1, -(1 + 2 * c), 1 + 2 * c, -1]

/-- Exact exponential factorization of the four-point packet. -/
theorem fourPoint_exp_sum (h c : ℝ) (w : ℂ) :
    (∑ i : Fin 4, (fourPointCoeff c i : ℂ) *
      Complex.exp (((fourPointTimes h i : ℂ) * w) * I)) =
    (1 - Complex.exp ((h : ℂ) * w * I)) *
      (1 - 2 * c * Complex.exp ((h : ℂ) * w * I) +
        Complex.exp ((h : ℂ) * w * I) ^ 2) := by
  simp only [fourPointTimes, fourPointCoeff, Fin.sum_univ_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.sum_univ_zero]
  push_cast
  simp only [zero_mul, Complex.exp_zero, one_mul, neg_mul, add_zero]
  rw [show 2 * (h : ℂ) * w * I = (2 : ℕ) * ((h : ℂ) * w * I) by ring,
    show 3 * (h : ℂ) * w * I = (3 : ℕ) * ((h : ℂ) * w * I) by ring,
    Complex.exp_nat_mul, Complex.exp_nat_mul]
  ring

/-- The spectral weight factors into a difference factor and a squared polar notch. -/
theorem fourPoint_weight (h c : ℝ) (w : ℂ) :
    complexTrigPacketWeight (fourPointTimes h) (fourPointCoeff c) w =
      8 * (1 - Complex.cos ((h : ℂ) * w)) *
        (Complex.cos ((h : ℂ) * w) - c) ^ 2 := by
  rw [complexTrigPacketWeight_eq_exp_mul_exp, fourPoint_exp_sum]
  have hneg :
      (∑ j : Fin 4, (fourPointCoeff c j : ℂ) *
        Complex.exp (-(((fourPointTimes h j : ℂ) * w) * I))) =
      (∑ j : Fin 4, (fourPointCoeff c j : ℂ) *
        Complex.exp (((fourPointTimes h j : ℂ) * (-w)) * I)) := by
    congr 1
    ext j
    congr 2
    ring
  rw [hneg, fourPoint_exp_sum]
  rw [show (h : ℂ) * -w * I = -((h : ℂ) * w * I) by ring,
    Complex.cos]
  simp only [neg_mul, Complex.exp_neg]
  have hne := Complex.exp_ne_zero ((h : ℂ) * w * I)
  field_simp
  ring

theorem fourPoint_weight_real (h c r : ℝ) :
    trigPacketWeight (fourPointTimes h) (fourPointCoeff c) r =
      8 * (1 - Real.cos (h * r)) * (Real.cos (h * r) - c) ^ 2 := by
  have hc := fourPoint_weight h c (r : ℂ)
  rw [complexTrigPacketWeight_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_cos] at hc
  exact_mod_cast hc

/-- One full period of the real part of the selected Klein–Gordon frequency. -/
def detectorStep (ρ : zetaZeroConfig.carrier) : ℝ := 2 * Real.pi / (kgFreq ρ).re
/-- The polar cosine at the selected period. -/
def detectorCos (ρ : zetaZeroConfig.carrier) : ℝ :=
  Real.cos (detectorStep ρ * Real.sqrt (7 / 4))
/-- Sampling times synchronized to the selected zero. -/
def detectorTimes (ρ : zetaZeroConfig.carrier) : Fin 4 → ℝ := fourPointTimes (detectorStep ρ)
/-- Real coefficients removing the polar frequency at the selected period. -/
def detectorCoeff (ρ : zetaZeroConfig.carrier) : Fin 4 → ℝ := fourPointCoeff (detectorCos ρ)

theorem detectorStep_pos (ρ : zetaZeroConfig.carrier) : 0 < detectorStep ρ :=
  div_pos (mul_pos (by norm_num) Real.pi_pos) (re_kgFreq_pos ρ)

/-- The synchronized packet annihilates the polar frequency exactly. -/
theorem detector_pole_zero (ρ : zetaZeroConfig.carrier) :
    trigPacketWeight (detectorTimes ρ) (detectorCoeff ρ) (Real.sqrt (7 / 4)) = 0 := by
  rw [detectorTimes, detectorCoeff, fourPoint_weight_real]
  simp [detectorCos]

/-- Synchronization removes the oscillatory phase at the selected zero. -/
theorem cos_detectorStep_kgFreq (ρ : zetaZeroConfig.carrier) :
    Complex.cos ((detectorStep ρ : ℂ) * kgFreq ρ) =
      (Real.cosh (detectorStep ρ * (kgFreq ρ).im) : ℂ) := by
  have hre : detectorStep ρ * (kgFreq ρ).re = 2 * Real.pi := by
    exact div_mul_cancel₀ _ (re_kgFreq_pos ρ).ne'
  have heq : (detectorStep ρ : ℂ) * kgFreq ρ =
      ((2 * Real.pi : ℝ) : ℂ) + ((detectorStep ρ * (kgFreq ρ).im : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, hre]
  rw [heq, cos_ofReal_add_mul_I, Real.cos_two_pi, Real.sin_two_pi]
  simp

/-- The selected zero's multiplicity-weighted contribution to its synchronized packet. -/
def selectedEnergy (ρ : zetaZeroConfig.carrier) : ℝ :=
  (zetaZeroConfig.mult ρ : ℝ) *
    (complexTrigPacketWeight (detectorTimes ρ) (detectorCoeff ρ) (kgFreq ρ) * kgWeight ρ).re

/-- Exact hyperbolic factorization of the selected contribution. -/
theorem selectedEnergy_eq (ρ : zetaZeroConfig.carrier) :
    selectedEnergy ρ =
      -8 * (zetaZeroConfig.mult ρ : ℝ) *
        (Real.cosh (detectorStep ρ * (kgFreq ρ).im) - 1) *
        (Real.cosh (detectorStep ρ * (kgFreq ρ).im) - detectorCos ρ) ^ 2 *
        (kgWeight ρ).re := by
  rw [selectedEnergy, detectorTimes, detectorCoeff, fourPoint_weight, cos_detectorStep_kgFreq]
  have hc :
      (8 : ℂ) * (1 - (Real.cosh (detectorStep ρ * (kgFreq ρ).im) : ℂ)) *
        ((Real.cosh (detectorStep ρ * (kgFreq ρ).im) : ℂ) - detectorCos ρ) ^ 2 =
      ((8 * (1 - Real.cosh (detectorStep ρ * (kgFreq ρ).im)) *
        (Real.cosh (detectorStep ρ * (kgFreq ρ).im) - detectorCos ρ) ^ 2 : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hc, Complex.re_ofReal_mul]
  ring

theorem selectedEnergy_nonpos (ρ : zetaZeroConfig.carrier) : selectedEnergy ρ ≤ 0 := by
  rw [selectedEnergy_eq]
  have hcosh : 0 ≤ Real.cosh (detectorStep ρ * (kgFreq ρ).im) - 1 :=
    sub_nonneg.mpr (Real.one_le_cosh _)
  have hw := (re_kgWeight_pos ρ).le
  have hp : 0 ≤ 8 * (zetaZeroConfig.mult ρ : ℝ) *
      (Real.cosh (detectorStep ρ * (kgFreq ρ).im) - 1) *
      (Real.cosh (detectorStep ρ * (kgFreq ρ).im) - detectorCos ρ) ^ 2 *
      (kgWeight ρ).re := by positivity
  nlinarith only [hp]

theorem selectedEnergy_neg_iff (ρ : zetaZeroConfig.carrier) :
    selectedEnergy ρ < 0 ↔ (kgFreq ρ).im ≠ 0 := by
  constructor
  · intro h hz
    rw [selectedEnergy_eq, hz, mul_zero, Real.cosh_zero, sub_self, mul_zero, zero_mul,
      zero_mul] at h
    exact lt_irrefl 0 h
  · intro hz
    have hcosh : 1 < Real.cosh (detectorStep ρ * (kgFreq ρ).im) :=
      Real.one_lt_cosh.mpr (mul_ne_zero (detectorStep_pos ρ).ne' hz)
    have hc : 0 < Real.cosh (detectorStep ρ * (kgFreq ρ).im) - detectorCos ρ :=
      sub_pos.mpr ((Real.cos_le_one _).trans_lt hcosh)
    have hm : (0 : ℝ) < zetaZeroConfig.mult ρ := by
      have h := zetaZeroConfig.one_le_mult _ ρ.2
      exact_mod_cast (by omega : 0 < zetaZeroConfig.mult ρ)
    have hw := re_kgWeight_pos ρ
    rw [selectedEnergy_eq]
    have hp : 0 < 8 * (zetaZeroConfig.mult ρ : ℝ) *
        (Real.cosh (detectorStep ρ * (kgFreq ρ).im) - 1) *
        (Real.cosh (detectorStep ρ * (kgFreq ρ).im) - detectorCos ρ) ^ 2 *
        (kgWeight ρ).re := by positivity
    nlinarith only [hp]

/-- Klein–Gordon transmutation preserves critical-line incidence at every nontrivial zero. -/
theorem im_kgFreq_eq_zero_iff_criticalLine (ρ : zetaZeroConfig.carrier) :
    (kgFreq ρ).im = 0 ↔ (ρ : ℂ).re = 1 / 2 := by
  have hmem : IsNontrivialZero (ρ : ℂ) := ρ.2
  have hρ1 : (ρ : ℂ) ≠ 1 := by
    intro h
    have := hmem.2.2
    simp [h] at this
  have hρim : (ρ : ℂ).im ≠ 0 := by
    intro h
    have hreal : (ρ : ℂ) = (((ρ : ℂ).re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [h]
    have hxi := (RHTower.xi_eq_zero_iff hmem.2.1 hρ1).mpr hmem.1
    rw [hreal] at hxi
    exact RHTower.xi_ne_zero_of_real _ hxi
  constructor
  · intro h
    have hkin := re_rhoC_mul_im_rhoC (Zeta23.gammaOf (ρ : ℂ))
    change (kgFreq ρ).re * (kgFreq ρ).im = _ at hkin
    rw [h, mul_zero, WeilEF.gammaOf_re, WeilEF.gammaOf_im] at hkin
    have := (mul_eq_zero.mp hkin.symm).resolve_left hρim
    linarith
  · intro h
    unfold kgFreq
    rw [RHTower.CHMDStage14.gammaOf_eq_ofReal_im_of_re_eq_half h,
      rhoC_ofReal, Complex.ofReal_im]

/-- The pole-free synchronized contribution is strictly negative exactly off the critical line. -/
theorem selectedEnergy_neg_iff_offLine (ρ : zetaZeroConfig.carrier) :
    selectedEnergy ρ < 0 ↔ (ρ : ℂ).re ≠ 1 / 2 := by
  rw [selectedEnergy_neg_iff, ne_eq, im_kgFreq_eq_zero_iff_criticalLine]

theorem selectedEnergy_eq_zero_iff_criticalLine (ρ : zetaZeroConfig.carrier) :
    selectedEnergy ρ = 0 ↔ (ρ : ℂ).re = 1 / 2 := by
  have hn := selectedEnergy_nonpos ρ
  have h := selectedEnergy_neg_iff_offLine ρ
  constructor
  · intro hz
    by_contra hoff
    have := h.mpr hoff
    linarith
  · intro hline
    by_contra hne
    have hn' : selectedEnergy ρ < 0 := lt_of_le_of_ne hn hne
    exact (h.mp hn') hline

/-- The complete CHMD Toeplitz energy of the synchronized packet. -/
def detectorEnergy (ρ : zetaZeroConfig.carrier) : ℝ :=
  ∑ i : Fin 4, ∑ j : Fin 4, detectorCoeff ρ i * detectorCoeff ρ j *
    chmdWave (detectorTimes ρ j - detectorTimes ρ i)

/-- All zero contributions are retained in the complete packet energy. -/
theorem detectorEnergy_zero_side (ρ : zetaZeroConfig.carrier) :
    detectorEnergy ρ = ∑' σ : zetaZeroConfig.carrier,
      (zetaZeroConfig.mult σ : ℝ) *
        (complexTrigPacketWeight (detectorTimes ρ) (detectorCoeff ρ) (kgFreq σ) *
          kgWeight σ).re :=
  sum_sum_cosineShiftFn_sechHalf_vonMangoldt_eq_tsum_complexTrigPacketWeight
    (detectorTimes ρ) (detectorCoeff ρ)

/-- Exact arithmetic source formula for the synchronized packet, with no polar term. -/
theorem detectorEnergy_prime_arch (ρ : zetaZeroConfig.carrier) :
    detectorEnergy ρ =
      1 / (2 * Real.pi) *
        (∫ r : ℝ, trigPacketWeight (detectorTimes ρ) (detectorCoeff ρ)
          (Real.sqrt (r ^ 2 + 2)) * sechSqHalf r * EF.gammaBracket r) -
      ∑' n : ℕ, (if 2 ≤ n then (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n else 0) *
        (1 / Real.pi * ∫ r : ℝ, trigPacketWeight (detectorTimes ρ) (detectorCoeff ρ)
          (Real.sqrt (r ^ 2 + 2)) * sechSqHalf r * Real.cos (r * Real.log n)) :=
  sum_sum_cosineShiftFn_sechHalf_of_pole_zero
    RHTower.CHMDStage3.abs_vonMangoldt_le_sqrt_mul_one_add_log
    (detectorTimes ρ) (detectorCoeff ρ) (detector_pole_zero ρ)

end RHTower.CHMDPolarDetector

end
