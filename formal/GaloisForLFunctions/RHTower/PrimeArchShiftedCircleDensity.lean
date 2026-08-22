import GaloisForLFunctions.HTGeometry.SummableCircleFourierDensity
import GaloisForLFunctions.RHTower.PrimeArchValuationSectorCones

/-!
# Positive shifted prime--archimedean circle densities

The reciprocal-square Xi source has a strictly positive circle density at
every shift from zero through twelve.  This module instantiates the generic
summable symmetric Fourier-density construction with the normalized
prime--archimedean moment tails and proves the strict tail gap from the
existing sector and endpoint estimates.

It constructs ordinary positive circle states only.  It does not assert the
reflected Hankel orientation, which remains the separate RH-bearing property.
-/

open scoped BigOperators
open MeasureTheory

namespace RHTower

noncomputable section

/-- The literal shifted prime--archimedean circle density
`m_s + 2 Σ_{n≥1} m_{s+n} Re(z^n)`. -/
def primeArchShiftCircleDensity (s : ℕ) (z : Circle) : ℝ :=
  GaloisForLFunctions.HTGeometry.symmetricCircleFourierDensity
    (primeArchShiftMoment s) z

/-- The shifted source density measure with respect to normalized circle Haar measure. -/
def primeArchShiftCircleDensityMeasure (s : ℕ) : Measure Circle :=
  GaloisForLFunctions.HTGeometry.symmetricCircleFourierDensityMeasure
    (primeArchShiftMoment s)

/-- The normalized shifted source density from the circle-state construction. -/
def primeArchShiftCircleProbabilityMeasure (s : ℕ) : Measure Circle :=
  GaloisForLFunctions.HTGeometry.circleLebesgue.withDensity fun z => ENNReal.ofReal
    (primeArchShiftCircleDensity s z / normalizedPrimeArchMoment s)

/-- Every shifted source density measure is finite. -/
theorem primeArchShiftCircleDensityMeasure_finite (s : ℕ) :
    IsFiniteMeasure (primeArchShiftCircleDensityMeasure s) := by
  exact GaloisForLFunctions.HTGeometry.symmetricCircleFourierDensityMeasure_finite
    (summable_abs_primeArchShiftMoment_tail s)

/-- The endpoint disk bound gives the quantitative lower density estimate at every shift. -/
theorem normalizedPrimeArchMoment_sub_four_over_thirtyNine_xiShiftAbsoluteMass_le_density
    (s : ℕ) (z : Circle) :
    normalizedPrimeArchMoment s - (4 / 39 : ℝ) * xiShiftAbsoluteMass s ≤
      primeArchShiftCircleDensity s z := by
  have hbase := GaloisForLFunctions.HTGeometry.symmetricCircleFourierDensity_lower
    (summable_abs_primeArchShiftMoment_tail s) z
  have htail := tsum_abs_primeArchShiftMoment_tail_le s
  change normalizedPrimeArchMoment s - (4 / 39 : ℝ) * xiShiftAbsoluteMass s ≤
    GaloisForLFunctions.HTGeometry.symmetricCircleFourierDensity
      (primeArchShiftMoment s) z
  change normalizedPrimeArchMoment s -
      2 * ∑' n : ℕ, |primeArchShiftMoment s (n + 1)| ≤
    GaloisForLFunctions.HTGeometry.symmetricCircleFourierDensity
      (primeArchShiftMoment s) z at hbase
  nlinarith

/-- The endpoint disk bound gives the quantitative upper density estimate at every shift. -/
theorem density_le_normalizedPrimeArchMoment_add_four_over_thirtyNine_xiShiftAbsoluteMass
    (s : ℕ) (z : Circle) :
    primeArchShiftCircleDensity s z ≤
      normalizedPrimeArchMoment s + (4 / 39 : ℝ) * xiShiftAbsoluteMass s := by
  have hbase := GaloisForLFunctions.HTGeometry.symmetricCircleFourierDensity_upper
    (summable_abs_primeArchShiftMoment_tail s) z
  have htail := tsum_abs_primeArchShiftMoment_tail_le s
  change GaloisForLFunctions.HTGeometry.symmetricCircleFourierDensity
      (primeArchShiftMoment s) z ≤
    normalizedPrimeArchMoment s + (4 / 39 : ℝ) * xiShiftAbsoluteMass s
  change GaloisForLFunctions.HTGeometry.symmetricCircleFourierDensity
      (primeArchShiftMoment s) z ≤
    normalizedPrimeArchMoment s +
      2 * ∑' n : ℕ, |primeArchShiftMoment s (n + 1)| at hbase
  nlinarith

private theorem two_tsum_abs_primeArchShiftMoment_tail_lt_head_of_le_eleven
    (s : ℕ) (hs : s ≤ 11) :
    2 * ∑' n : ℕ, |primeArchShiftMoment s (n + 1)| <
      primeArchShiftMoment s 0 := by
  have hApos : 0 < xiShiftAbsoluteMass s := xiShiftAbsoluteMass_pos s
  have hmass := sectorFactor_mul_xiShiftAbsoluteMass_le_normalizedPrimeArchMoment s
  have hsCast : (((s + 1 : ℕ) : ℝ)) ≤ 12 := by
    exact_mod_cast (show s + 1 ≤ 12 by omega)
  have hfactor : (4 / 39 : ℝ) < 1 - (((s + 1 : ℕ) : ℝ) ^ 2) / 168 := by
    nlinarith [sq_nonneg ((((s + 1 : ℕ) : ℝ)) - 12)]
  have hstrictA : (4 / 39 : ℝ) * xiShiftAbsoluteMass s <
      (1 - (((s + 1 : ℕ) : ℝ) ^ 2) / 168) * xiShiftAbsoluteMass s :=
    mul_lt_mul_of_pos_right hfactor hApos
  have hstrictM : (4 / 39 : ℝ) * xiShiftAbsoluteMass s <
      normalizedPrimeArchMoment s := hstrictA.trans_le hmass
  have htail := tsum_abs_primeArchShiftMoment_tail_le s
  have htail' : 2 * ∑' n : ℕ, |primeArchShiftMoment s (n + 1)| ≤
      (4 / 39 : ℝ) * xiShiftAbsoluteMass s := by
    nlinarith
  calc 2 * ∑' n : ℕ, |primeArchShiftMoment s (n + 1)|
      ≤ (4 / 39 : ℝ) * xiShiftAbsoluteMass s := htail'
    _ < normalizedPrimeArchMoment s := hstrictM
    _ = primeArchShiftMoment s 0 := by simp [primeArchShiftMoment]

private theorem two_tsum_abs_primeArchShiftMoment_tail_lt_head_twelve :
    2 * ∑' n : ℕ, |primeArchShiftMoment 12 (n + 1)| <
      primeArchShiftMoment 12 0 := by
  have hApos : 0 < xiShiftAbsoluteMass 12 := xiShiftAbsoluteMass_pos 12
  have hmass : (1 / 8 : ℝ) * xiShiftAbsoluteMass 12 ≤ normalizedPrimeArchMoment 12 := by
    simpa only [xiShiftAbsoluteMass, xiShiftThirteenAbsoluteMass, Nat.reduceAdd] using
      one_eighth_xiShiftThirteenAbsoluteMass_le_normalizedPrimeArchMoment_twelve
  have hstrictA : (4 / 39 : ℝ) * xiShiftAbsoluteMass 12 <
      (1 / 8 : ℝ) * xiShiftAbsoluteMass 12 :=
    mul_lt_mul_of_pos_right (by norm_num) hApos
  have hstrictM : (4 / 39 : ℝ) * xiShiftAbsoluteMass 12 <
      normalizedPrimeArchMoment 12 := hstrictA.trans_le hmass
  have htail := tsum_abs_primeArchShiftMoment_tail_le 12
  have htail' : 2 * ∑' n : ℕ, |primeArchShiftMoment 12 (n + 1)| ≤
      (4 / 39 : ℝ) * xiShiftAbsoluteMass 12 := by
    nlinarith
  calc 2 * ∑' n : ℕ, |primeArchShiftMoment 12 (n + 1)|
      ≤ (4 / 39 : ℝ) * xiShiftAbsoluteMass 12 := htail'
    _ < normalizedPrimeArchMoment 12 := hstrictM
    _ = primeArchShiftMoment 12 0 := by simp [primeArchShiftMoment]

/-- Every shifted prime--archimedean source density through shift twelve is strictly positive. -/
theorem primeArchShiftCircleDensity_pos_of_le_twelve
    (s : ℕ) (hs : s ≤ 12) (z : Circle) :
    0 < primeArchShiftCircleDensity s z := by
  have hgap : 2 * ∑' n : ℕ, |primeArchShiftMoment s (n + 1)| <
      primeArchShiftMoment s 0 := by
    by_cases hs11 : s ≤ 11
    · exact two_tsum_abs_primeArchShiftMoment_tail_lt_head_of_le_eleven s hs11
    · have hs12 : s = 12 := by omega
      subst s
      exact two_tsum_abs_primeArchShiftMoment_tail_lt_head_twelve
  exact GaloisForLFunctions.HTGeometry.symmetricCircleFourierDensity_pos
    (summable_abs_primeArchShiftMoment_tail s) hgap z

/-- Through shift twelve, the normalized source density defines an unconditional circle probability
carrier.  This is ordinary unitary positivity only; it contains no reflected Hankel assertion. -/
theorem isProbabilityMeasure_primeArchShiftCircleProbabilityMeasure_of_le_twelve
    (s : ℕ) (hs : s ≤ 12) :
    IsProbabilityMeasure (primeArchShiftCircleProbabilityMeasure s) := by
  have hM : 0 < normalizedPrimeArchMoment s :=
    normalizedPrimeArchMoment_pos_of_le_twelve s hs
  have hDensity : Integrable (primeArchShiftCircleDensity s)
      GaloisForLFunctions.HTGeometry.circleLebesgue := by
    change Integrable
      (GaloisForLFunctions.HTGeometry.symmetricCircleFourierDensity
        (primeArchShiftMoment s)) GaloisForLFunctions.HTGeometry.circleLebesgue
    exact GaloisForLFunctions.HTGeometry.integrable_symmetricCircleFourierDensity
      (summable_abs_primeArchShiftMoment_tail s)
  have hNormalized : Integrable (fun z : Circle =>
      primeArchShiftCircleDensity s z / normalizedPrimeArchMoment s)
      GaloisForLFunctions.HTGeometry.circleLebesgue := by
    rw [show (fun z : Circle => primeArchShiftCircleDensity s z /
        normalizedPrimeArchMoment s) =
        fun z => (normalizedPrimeArchMoment s)⁻¹ * primeArchShiftCircleDensity s z by
      funext z
      rw [div_eq_inv_mul]]
    exact hDensity.const_mul _
  have hnonneg : ∀ z : Circle,
      0 ≤ primeArchShiftCircleDensity s z / normalizedPrimeArchMoment s := by
    intro z
    exact div_nonneg (primeArchShiftCircleDensity_pos_of_le_twelve s hs z).le hM.le
  rw [isProbabilityMeasure_iff, primeArchShiftCircleProbabilityMeasure,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hmass : ∫ z : Circle,
      primeArchShiftCircleDensity s z / normalizedPrimeArchMoment s
        ∂GaloisForLFunctions.HTGeometry.circleLebesgue = 1 := by
    rw [show (fun z : Circle => primeArchShiftCircleDensity s z /
        normalizedPrimeArchMoment s) =
        fun z => (normalizedPrimeArchMoment s)⁻¹ * primeArchShiftCircleDensity s z by
      funext z
      rw [div_eq_inv_mul], integral_const_mul]
    change (normalizedPrimeArchMoment s)⁻¹ *
      (∫ z : Circle,
        GaloisForLFunctions.HTGeometry.symmetricCircleFourierDensity
          (primeArchShiftMoment s) z ∂GaloisForLFunctions.HTGeometry.circleLebesgue) = 1
    rw [GaloisForLFunctions.HTGeometry.integral_symmetricCircleFourierDensity
      (summable_abs_primeArchShiftMoment_tail s)]
    simp only [primeArchShiftMoment, Nat.add_zero]
    field_simp [hM.ne']
  have hlintegral := MeasureTheory.ofReal_integral_eq_lintegral_ofReal
    hNormalized (Filter.Eventually.of_forall hnonneg)
  rw [hmass] at hlintegral
  simpa using hlintegral.symm

end

end RHTower
