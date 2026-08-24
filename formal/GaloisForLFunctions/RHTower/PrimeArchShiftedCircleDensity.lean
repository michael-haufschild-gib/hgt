import GaloisForLFunctions.HTGeometry.SymmetricCircleReflection
import GaloisForLFunctions.HTGeometry.SymmetricCircleFourierAnalyticity
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

/-- Every strictly positive shifted carrier through shift twelve has exactly Haar null sets. -/
theorem primeArchShiftCircleProbabilityMeasure_mutuallyAbsolutelyContinuous_circleLebesgue
    (s : ℕ) (hs : s ≤ 12) :
    primeArchShiftCircleProbabilityMeasure s ≪
        GaloisForLFunctions.HTGeometry.circleLebesgue ∧
      GaloisForLFunctions.HTGeometry.circleLebesgue ≪
        primeArchShiftCircleProbabilityMeasure s := by
  change GaloisForLFunctions.HTGeometry.circleLebesgue.withDensity
      (fun z => ENNReal.ofReal
        (primeArchShiftCircleDensity s z / normalizedPrimeArchMoment s)) ≪
        GaloisForLFunctions.HTGeometry.circleLebesgue ∧
    GaloisForLFunctions.HTGeometry.circleLebesgue ≪
      GaloisForLFunctions.HTGeometry.circleLebesgue.withDensity
        (fun z => ENNReal.ofReal
          (primeArchShiftCircleDensity s z / normalizedPrimeArchMoment s))
  constructor
  · exact withDensity_absolutelyContinuous _ _
  · apply withDensity_absolutelyContinuous'
    · exact ((GaloisForLFunctions.HTGeometry.measurable_symmetricCircleFourierDensity
        (primeArchShiftMoment s)).div_const
          (normalizedPrimeArchMoment s)).ennreal_ofReal.aemeasurable
    · exact Filter.Eventually.of_forall fun z =>
        (ENNReal.ofReal_pos.mpr (div_pos
          (primeArchShiftCircleDensity_pos_of_le_twelve s hs z)
          (normalizedPrimeArchMoment_pos_of_le_twelve s hs))).ne'

/-- Exact shifted source moment recovery.  The ordinary circle carrier has Fourier moments
`m_(s+k) / m_s` for every nonnegative mode. -/
theorem integral_coe_pow_primeArchShiftCircleProbabilityMeasure
    (s : ℕ) (hs : s ≤ 12) (k : ℕ) :
    (∫ z : Circle, (z : ℂ) ^ k ∂primeArchShiftCircleProbabilityMeasure s) =
      (normalizedPrimeArchMoment (s + k) : ℂ) /
        (normalizedPrimeArchMoment s : ℂ) := by
  have h := GaloisForLFunctions.HTGeometry.integral_coe_pow_normalized_symmetricCircleFourierDensityMeasure
      (summable_abs_primeArchShiftMoment_tail s)
      (show 0 < primeArchShiftMoment s 0 by
        simpa [primeArchShiftMoment] using normalizedPrimeArchMoment_pos_of_le_twelve s hs)
      (fun z => (primeArchShiftCircleDensity_pos_of_le_twelve s hs z).le) k
  simpa [primeArchShiftCircleProbabilityMeasure, primeArchShiftCircleDensity,
    primeArchShiftMoment] using h

/-- Every normalized shifted prime--archimedean circle carrier is invariant under inversion. -/
theorem map_inv_primeArchShiftCircleProbabilityMeasure (s : ℕ) :
    Measure.map Inv.inv (primeArchShiftCircleProbabilityMeasure s) =
      primeArchShiftCircleProbabilityMeasure s := by
  have hmeas : Measurable (fun z : Circle => ENNReal.ofReal
      (primeArchShiftCircleDensity s z / normalizedPrimeArchMoment s)) := by
    apply Measurable.ennreal_ofReal
    simpa only [primeArchShiftCircleDensity] using
      (GaloisForLFunctions.HTGeometry.measurable_symmetricCircleFourierDensity
        (primeArchShiftMoment s)).div_const (normalizedPrimeArchMoment s)
  change Measure.map Inv.inv
      (GaloisForLFunctions.HTGeometry.circleLebesgue.withDensity fun z =>
        ENNReal.ofReal (primeArchShiftCircleDensity s z / normalizedPrimeArchMoment s)) =
    GaloisForLFunctions.HTGeometry.circleLebesgue.withDensity fun z =>
      ENNReal.ofReal (primeArchShiftCircleDensity s z / normalizedPrimeArchMoment s)
  have hmap := GaloisForLFunctions.HTGeometry.map_withDensity_of_involution
    (g := fun z : Circle => ENNReal.ofReal
      (primeArchShiftCircleDensity s z / normalizedPrimeArchMoment s))
    measurable_inv inv_inv GaloisForLFunctions.HTGeometry.map_inv_circleLebesgue hmeas
  rw [hmap]
  congr 1
  funext z
  change ENNReal.ofReal
      (GaloisForLFunctions.HTGeometry.symmetricCircleFourierDensity
        (primeArchShiftMoment s) z⁻¹ / normalizedPrimeArchMoment s) =
    ENNReal.ofReal
      (GaloisForLFunctions.HTGeometry.symmetricCircleFourierDensity
        (primeArchShiftMoment s) z / normalizedPrimeArchMoment s)
  rw [GaloisForLFunctions.HTGeometry.symmetricCircleFourierDensity_inv]

/-- Inversion is measure preserving on every shifted circle carrier. -/
theorem measurePreserving_inv_primeArchShiftCircleProbabilityMeasure (s : ℕ) :
    MeasurePreserving Inv.inv (primeArchShiftCircleProbabilityMeasure s)
      (primeArchShiftCircleProbabilityMeasure s) :=
  ⟨measurable_inv, map_inv_primeArchShiftCircleProbabilityMeasure s⟩

/-- The canonical shifted circle reflection `Theta f(z) = f(z⁻¹)`. -/
def primeArchShiftCircleReflectionLI (s : ℕ) :
    Lp ℂ 2 (primeArchShiftCircleProbabilityMeasure s) →ₗᵢ[ℂ]
      Lp ℂ 2 (primeArchShiftCircleProbabilityMeasure s) :=
  GaloisForLFunctions.HTGeometry.circleInvReflectionLI _
    (measurePreserving_inv_primeArchShiftCircleProbabilityMeasure s)

/-- The `n`th analytic orbit vector in the shifted circle carrier. -/
def primeArchShiftCircleMonomialLp
    (s : ℕ) (hs : s ≤ 12) (n : ℕ) :
    Lp ℂ 2 (primeArchShiftCircleProbabilityMeasure s) := by
  letI : IsProbabilityMeasure (primeArchShiftCircleProbabilityMeasure s) :=
    isProbabilityMeasure_primeArchShiftCircleProbabilityMeasure_of_le_twelve s hs
  exact GaloisForLFunctions.HTGeometry.circleMonomialLp
    (primeArchShiftCircleProbabilityMeasure s) n

/-- A finite real analytic polynomial in the shifted circle carrier. -/
def primeArchShiftFiniteRealCirclePolynomialLp
    (s : ℕ) (hs : s ≤ 12) {n : ℕ} (v : Fin n → ℝ) :
    Lp ℂ 2 (primeArchShiftCircleProbabilityMeasure s) :=
  ∑ i : Fin n, (v i : ℂ) • primeArchShiftCircleMonomialLp s hs i

/-- The reflected monomial Gram kernel is exactly the shifted prime--archimedean Hankel kernel. -/
theorem inner_primeArchShiftCircleReflectionLI_monomial
    (s : ℕ) (hs : s ≤ 12) (i j : ℕ) :
    inner ℂ
        (primeArchShiftCircleReflectionLI s
          (primeArchShiftCircleMonomialLp s hs i))
        (primeArchShiftCircleMonomialLp s hs j) =
      (normalizedPrimeArchMoment (s + (i + j)) : ℂ) /
        (normalizedPrimeArchMoment s : ℂ) := by
  letI : IsProbabilityMeasure (primeArchShiftCircleProbabilityMeasure s) :=
    isProbabilityMeasure_primeArchShiftCircleProbabilityMeasure_of_le_twelve s hs
  change inner ℂ
      (GaloisForLFunctions.HTGeometry.circleInvReflectionLI _
        (measurePreserving_inv_primeArchShiftCircleProbabilityMeasure s)
        (GaloisForLFunctions.HTGeometry.circleMonomialLp _ i))
      (GaloisForLFunctions.HTGeometry.circleMonomialLp _ j) = _
  rw [GaloisForLFunctions.HTGeometry.circleInvReflectionLI_monomial_inner,
    integral_coe_pow_primeArchShiftCircleProbabilityMeasure s hs]

/-- The reflected Gram value of a finite real polynomial is the normalized shifted Hankel sum. -/
theorem inner_primeArchShiftCircleReflectionLI_finitePolynomial
    (s : ℕ) (hs : s ≤ 12) {n : ℕ} (v : Fin n → ℝ) :
    let P := primeArchShiftFiniteRealCirclePolynomialLp s hs v
    inner ℂ (primeArchShiftCircleReflectionLI s P) P =
      ∑ i : Fin n, ∑ j : Fin n,
        (↑(v i * v j * normalizedPrimeArchMoment
          (s + ((i : ℕ) + (j : ℕ))) / normalizedPrimeArchMoment s) : ℂ) := by
  letI : IsProbabilityMeasure (primeArchShiftCircleProbabilityMeasure s) :=
    isProbabilityMeasure_primeArchShiftCircleProbabilityMeasure_of_le_twelve s hs
  dsimp only
  change inner ℂ
      (GaloisForLFunctions.HTGeometry.circleInvReflectionLI _
        (measurePreserving_inv_primeArchShiftCircleProbabilityMeasure s)
        (GaloisForLFunctions.HTGeometry.finiteRealCirclePolynomialLp _ v))
      (GaloisForLFunctions.HTGeometry.finiteRealCirclePolynomialLp _ v) = _
  rw [GaloisForLFunctions.HTGeometry.circleInvReflectionLI_finitePolynomial_inner]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [integral_coe_pow_primeArchShiftCircleProbabilityMeasure s hs]
  push_cast
  ring

/-- Reflected Gram value as the normalized shifted moment functional. -/
theorem inner_primeArchShiftCircleReflectionLI_finitePolynomial_eq_momentFunctional
    (s : ℕ) (hs : s ≤ 12) {n : ℕ} (v : Fin n → ℝ) :
    let P := primeArchShiftFiniteRealCirclePolynomialLp s hs v
    inner ℂ (primeArchShiftCircleReflectionLI s P) P =
      (HTGeometry.momentFunctional (primeArchShiftMoment s)
          ((∑ i : Fin n, v i • Polynomial.X ^ (i : ℕ)) ^ 2) /
        normalizedPrimeArchMoment s : ℂ) := by
  dsimp only
  rw [inner_primeArchShiftCircleReflectionLI_finitePolynomial s hs v,
    HTGeometry.momentFunctional_sq_eq_hankelForm]
  simp only [primeArchShiftMoment]
  push_cast
  rw [Finset.sum_div]
  simp_rw [Finset.sum_div]

/-- Exact shifted cosine--sine polarization identity. -/
theorem primeArchShiftCircle_cosine_sine_polarization
    (s : ℕ) (hs : s ≤ 12) {n : ℕ} (v : Fin n → ℝ) :
    let R := primeArchShiftCircleReflectionLI s
    let P := primeArchShiftFiniteRealCirclePolynomialLp s hs v
    ‖GaloisForLFunctions.HTGeometry.circleReflectionCosineChannel R P‖ ^ 2 -
        ‖GaloisForLFunctions.HTGeometry.circleReflectionSineChannel R P‖ ^ 2 =
      HTGeometry.momentFunctional (primeArchShiftMoment s)
          ((∑ i : Fin n, v i • Polynomial.X ^ (i : ℕ)) ^ 2) /
        normalizedPrimeArchMoment s := by
  letI : IsProbabilityMeasure (primeArchShiftCircleProbabilityMeasure s) :=
    isProbabilityMeasure_primeArchShiftCircleProbabilityMeasure_of_le_twelve s hs
  dsimp only
  rw [GaloisForLFunctions.HTGeometry.norm_circleReflectionCosineChannel_sq_sub_sine,
    inner_primeArchShiftCircleReflectionLI_finitePolynomial_eq_momentFunctional s hs v]
  norm_num

/-- `Theta U Theta = U⁻¹` on every shifted prime--archimedean circle carrier. -/
theorem primeArchShiftCircleReflectionLI_circleZMulLp_conj
    (s : ℕ) (hs : s ≤ 12)
    (f : Lp ℂ 2 (primeArchShiftCircleProbabilityMeasure s)) :
    letI : IsProbabilityMeasure (primeArchShiftCircleProbabilityMeasure s) :=
      isProbabilityMeasure_primeArchShiftCircleProbabilityMeasure_of_le_twelve s hs
    primeArchShiftCircleReflectionLI s
        (GaloisForLFunctions.HTGeometry.circleZMulLp _
          (primeArchShiftCircleReflectionLI s f)) =
      (GaloisForLFunctions.HTGeometry.circleZMulLIE _).symm f := by
  letI : IsProbabilityMeasure (primeArchShiftCircleProbabilityMeasure s) :=
    isProbabilityMeasure_primeArchShiftCircleProbabilityMeasure_of_le_twelve s hs
  exact GaloisForLFunctions.HTGeometry.circleInvReflectionLI_circleZMulLp_circleInvReflectionLI
    _ (measurePreserving_inv_primeArchShiftCircleProbabilityMeasure s) f

/-- Exact `41/2` geometric radius bound for the shifted Fourier tail. -/
theorem primeArchShiftMoment_mul_radius_bound (s n : ℕ) :
    ‖(primeArchShiftMoment s (n + 1) : ℂ)‖ * (41 / 2 : ℝ) ^ n ≤
      xiShiftAbsoluteMass s := by
  have h := abs_normalizedPrimeArchMoment_add_le_xiShiftAbsoluteMass s (n + 1)
  simp only [primeArchShiftMoment, Complex.norm_real, Real.norm_eq_abs] at h ⊢
  calc
    |normalizedPrimeArchMoment (s + (n + 1))| * (41 / 2 : ℝ) ^ n ≤
        ((2 / 41 : ℝ) ^ (n + 1) * xiShiftAbsoluteMass s) * (41 / 2 : ℝ) ^ n := by
      gcongr
    _ = (2 / 41 : ℝ) * xiShiftAbsoluteMass s := by
      rw [pow_succ]
      calc
        (((2 / 41 : ℝ) ^ n * (2 / 41)) * xiShiftAbsoluteMass s) *
            (41 / 2 : ℝ) ^ n =
          (2 / 41 : ℝ) * xiShiftAbsoluteMass s *
            ((2 / 41 : ℝ) * (41 / 2 : ℝ)) ^ n := by
              rw [mul_pow]
              ring
        _ = (2 / 41 : ℝ) * xiShiftAbsoluteMass s := by norm_num
    _ ≤ xiShiftAbsoluteMass s := by
      have hA := xiShiftAbsoluteMass_nonneg s
      nlinarith

/-- Explicit holomorphic Laurent extension of the shifted circle density. -/
def primeArchShiftCircleLaurentExtension (s : ℕ) (z : ℂ) : ℂ :=
  GaloisForLFunctions.HTGeometry.symmetricCircleFourierLaurentExtension
    (primeArchShiftMoment s) z

/-- The shifted source density is holomorphic on an ambient neighborhood of every unit-circle
point, hence its circle restriction is real analytic. -/
theorem analyticAt_primeArchShiftCircleLaurentExtension_on_unitCircle
    (s : ℕ) (z : Circle) :
    AnalyticAt ℂ (primeArchShiftCircleLaurentExtension s) (z : ℂ) := by
  apply GaloisForLFunctions.HTGeometry.analyticAt_symmetricCircleFourierLaurentExtension
    (B := xiShiftAbsoluteMass s) (r := 41 / 2)
  · norm_num
  · exact primeArchShiftMoment_mul_radius_bound s
  · exact Circle.coe_ne_zero z
  · norm_num [Circle.norm_coe]
  · rw [norm_inv, Circle.norm_coe]
    norm_num

/-- The Laurent extension restricts exactly to the shifted symmetric Fourier density. -/
theorem primeArchShiftCircleLaurentExtension_coe (s : ℕ) (z : Circle) :
    primeArchShiftCircleLaurentExtension s (z : ℂ) =
      (primeArchShiftCircleDensity s z : ℂ) := by
  exact GaloisForLFunctions.HTGeometry.symmetricCircleFourierLaurentExtension_coe
    (summable_abs_primeArchShiftMoment_tail s) z

/-- For shifts through eleven, the paper relative density error dominates the absolute tail. -/
theorem four_over_thirtyNine_xiShiftAbsoluteMass_le_shiftRelativeDelta_mul_head
    (s : ℕ) (hs : s ≤ 11) :
    (4 / 39 : ℝ) * xiShiftAbsoluteMass s ≤
      (224 / (13 * (168 - (((s + 1 : ℕ) : ℝ) ^ 2))) : ℝ) *
        normalizedPrimeArchMoment s := by
  let A := xiShiftAbsoluteMass s
  let m0 := normalizedPrimeArchMoment s
  let C : ℝ := 168 - (((s + 1 : ℕ) : ℝ) ^ 2)
  have hsCast : (((s + 1 : ℕ) : ℝ)) ≤ 12 := by
    exact_mod_cast (show s + 1 ≤ 12 by omega)
  have hC : 0 < C := by
    dsimp only [C]
    nlinarith [sq_nonneg ((((s + 1 : ℕ) : ℝ)) - 12)]
  have hmass := sectorFactor_mul_xiShiftAbsoluteMass_le_normalizedPrimeArchMoment s
  have hmass' : (C / 168) * A ≤ m0 := by
    dsimp only [A, m0, C]
    convert hmass using 1
    all_goals ring
  have hAupper : A ≤ (168 / C) * m0 := by
    have hCA : A * C ≤ 168 * m0 := by
      nlinarith
    calc
      A ≤ (168 * m0) / C := (le_div_iff₀ hC).2 hCA
      _ = (168 / C) * m0 := by ring
  calc
    (4 / 39 : ℝ) * xiShiftAbsoluteMass s = (4 / 39 : ℝ) * A := rfl
    _ ≤ (4 / 39 : ℝ) * ((168 / C) * m0) := by
      gcongr
    _ = (224 / (13 * C) : ℝ) * m0 := by
      field_simp
      ring
    _ = _ := rfl

/-- Exact paper lower density bound for every shift through eleven. -/
theorem primeArchShiftCircleDensity_lower_of_le_eleven
    (s : ℕ) (hs : s ≤ 11) (z : Circle) :
    (1 - (224 / (13 * (168 - (((s + 1 : ℕ) : ℝ) ^ 2))) : ℝ)) *
        normalizedPrimeArchMoment s ≤ primeArchShiftCircleDensity s z := by
  have hbase :=
    normalizedPrimeArchMoment_sub_four_over_thirtyNine_xiShiftAbsoluteMass_le_density s z
  have htail := four_over_thirtyNine_xiShiftAbsoluteMass_le_shiftRelativeDelta_mul_head s hs
  nlinarith

/-- Exact paper upper density bound for every shift through eleven. -/
theorem primeArchShiftCircleDensity_upper_of_le_eleven
    (s : ℕ) (hs : s ≤ 11) (z : Circle) :
    primeArchShiftCircleDensity s z ≤
      (1 + (224 / (13 * (168 - (((s + 1 : ℕ) : ℝ) ^ 2))) : ℝ)) *
        normalizedPrimeArchMoment s := by
  have hbase :=
    density_le_normalizedPrimeArchMoment_add_four_over_thirtyNine_xiShiftAbsoluteMass s z
  have htail := four_over_thirtyNine_xiShiftAbsoluteMass_le_shiftRelativeDelta_mul_head s hs
  nlinarith

/-- The first twelve paper relative errors are uniformly at most `28/39 < 1`. -/
theorem primeArchShiftRelativeDelta_le_twentyEight_over_thirtyNine
    (s : ℕ) (hs : s ≤ 11) :
    (224 / (13 * (168 - (((s + 1 : ℕ) : ℝ) ^ 2))) : ℝ) ≤ 28 / 39 := by
  have hsCast : (((s + 1 : ℕ) : ℝ)) ≤ 12 := by
    exact_mod_cast (show s + 1 ≤ 12 by omega)
  have hC : 0 < (168 - (((s + 1 : ℕ) : ℝ) ^ 2) : ℝ) := by
    nlinarith [sq_nonneg ((((s + 1 : ℕ) : ℝ)) - 12)]
  apply (div_le_iff₀ (show 0 < (13 : ℝ) *
    (168 - (((s + 1 : ℕ) : ℝ) ^ 2)) by positivity)).2
  nlinarith [sq_nonneg ((((s + 1 : ℕ) : ℝ)) - 12)]

/-- At shift twelve, the exact thirteenth-power mass bound gives relative error `32/39`. -/
theorem four_over_thirtyNine_xiShiftAbsoluteMass_twelve_le_relative_head :
    (4 / 39 : ℝ) * xiShiftAbsoluteMass 12 ≤
      (32 / 39 : ℝ) * normalizedPrimeArchMoment 12 := by
  have hmass : (1 / 8 : ℝ) * xiShiftAbsoluteMass 12 ≤ normalizedPrimeArchMoment 12 := by
    simpa only [xiShiftAbsoluteMass, xiShiftThirteenAbsoluteMass, Nat.reduceAdd] using
      one_eighth_xiShiftThirteenAbsoluteMass_le_normalizedPrimeArchMoment_twelve
  nlinarith

/-- Exact thirteenth-state lower density bound. -/
theorem primeArchShiftCircleDensity_twelve_lower (z : Circle) :
    (1 - (32 / 39 : ℝ)) * normalizedPrimeArchMoment 12 ≤
      primeArchShiftCircleDensity 12 z := by
  have hbase :=
    normalizedPrimeArchMoment_sub_four_over_thirtyNine_xiShiftAbsoluteMass_le_density 12 z
  have htail := four_over_thirtyNine_xiShiftAbsoluteMass_twelve_le_relative_head
  nlinarith

/-- Exact thirteenth-state upper density bound. -/
theorem primeArchShiftCircleDensity_twelve_upper (z : Circle) :
    primeArchShiftCircleDensity 12 z ≤
      (1 + (32 / 39 : ℝ)) * normalizedPrimeArchMoment 12 := by
  have hbase :=
    density_le_normalizedPrimeArchMoment_add_four_over_thirtyNine_xiShiftAbsoluteMass 12 z
  have htail := four_over_thirtyNine_xiShiftAbsoluteMass_twelve_le_relative_head
  nlinarith

end

end RHTower
