import GaloisForLFunctions.RHTower.PrimeArchGaussianHermiteDensity
import GaloisForLFunctions.RHTower.PrimeArchThetaGaussianScoreFloorEnvelope
import GaloisForLFunctions.RHTower.PrimeArchThetaPolynomialScoreGap
import GaloisForLFunctions.RHTower.PrimeArchThetaCumulantMomentThreeFour
import GaloisForLFunctions.RHTower.XiCentralDiscBound

/-!
# The literal-mass calibrated Gaussian–Hermite countermodel

Fix the literal actual raw mass `A = thetaCuspRawEvenMoment 0`; the certified central bound
`‖XiC 0‖ ≥ 9/20` gives `A ≥ 9/20`.  For the Gaussian–Hermite density `ρ_τ` the model raw moments
`R^τ_j = A ∫ x^{2j} ρ_τ` start at exactly `A`, and the model score gaps
`G^τ_j = (32j+17)R^τ_j - 303 R^τ_{j+1}` form the quadratic form
`Σ a_i a_j G^τ_{i+j} = A ∫ (Σ a_i x^{2i})² (ρ_τ - 16xρ_τ' - 303x²ρ_τ)`.

For small `τ > 0` the defect density dominates `(1 + 177x²)(9/10)ρ_0` on `x ≥ 0`, and the
strict Gaussian envelope of the actual first atom then gives

```text
Σ a_i a_j G^τ_{i+j} ≥ (111104/110843) · 2π ∫_0^∞ (Σ a_i x^{2i})² (x-1)² ψ_1(x)² dx ,
```

the complete prescribed first-atom polynomial floor with a uniform strict surplus.  Yet the
normalized moments `R^τ_j/R^τ_0 = 6^{-2j}(m_j + τ c_j)` have prime–archimedean size-three Hankel
determinant `6^{-18} τ²(-196 + 324τ + 16τ²) < 0`.  The same determinant map evaluates, on the
actual normalized moments, to the actual size-three determinant of `normalizedPrimeArchMoment`.
-/

open MeasureTheory Set Filter Topology Polynomial

noncomputable section

namespace RHTower

/-- The literal actual raw mass is at least `9/20`. -/
theorem nine_div_twenty_le_thetaCuspRawEvenMoment_zero : 9 / 20 ≤ thetaCuspRawEvenMoment 0 := by
  have h := norm_XiC_zero_ge
  have hX : XiC 0 = ((thetaCuspRawEvenMoment 0 : ℝ) : ℂ) := by
    simpa [iteratedDeriv_zero] using iteratedDeriv_XiC_zero_eq_rawEvenMoment 0
  rw [hX, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos thetaCuspRawEvenMoment_zero_pos] at h
  exact h

/-! ## Model raw moments and score gaps -/

/-- Model raw moments `R^τ_j = A ∫ x^{2j} ρ_τ` at the literal actual raw mass `A`. -/
def gaussianHermiteRawMoment (τ : ℝ) (j : ℕ) : ℝ :=
  thetaCuspRawEvenMoment 0 * ∫ x, x ^ (2 * j) * gaussianHermiteDensity τ x

theorem gaussianHermiteRawMoment_eq (τ : ℝ) (j : ℕ) :
    gaussianHermiteRawMoment τ j = thetaCuspRawEvenMoment 0 * ((1 / 6) ^ (2 * j) *
      (gaussianEvenWickMoment j + τ * hermiteBoundaryWickCorrection j)) := by
  rw [gaussianHermiteRawMoment, integral_even_pow_mul_gaussianHermiteDensity]

/-- **Literal raw mass.**  The model has exactly the actual raw mass. -/
theorem gaussianHermiteRawMoment_zero (τ : ℝ) :
    gaussianHermiteRawMoment τ 0 = thetaCuspRawEvenMoment 0 := by
  have h := integral_gaussianHermiteDensity τ
  simp only [gaussianHermiteRawMoment, mul_zero, pow_zero, one_mul, h, mul_one]

/-- Model raw score gaps. -/
def gaussianHermiteRawScoreGap (τ : ℝ) (j : ℕ) : ℝ :=
  (32 * (j : ℝ) + 17) * gaussianHermiteRawMoment τ j - 303 * gaussianHermiteRawMoment τ (j + 1)

/-- The model finite score-gap quadratic form. -/
def gaussianHermiteFiniteScoreGap (τ : ℝ) {N : ℕ} (a : Fin N → ℝ) : ℝ :=
  ∑ i, ∑ j, a i * a j * gaussianHermiteRawScoreGap τ ((i : ℕ) + (j : ℕ))

/-- The model polynomial score-gap form, with the corpus coefficient convention. -/
def gaussianHermitePolynomialScoreGap (τ : ℝ) (P : ℝ[X]) : ℝ :=
  gaussianHermiteFiniteScoreGap τ (fun i : Fin (P.natDegree + 1) => P.coeff i)

theorem gaussianHermiteRawScoreGap_eq_integral (τ : ℝ) (k : ℕ) :
    gaussianHermiteRawScoreGap τ k =
      thetaCuspRawEvenMoment 0 * ∫ x, x ^ (2 * k) * gaussianHermiteDefectDensity τ x := by
  rw [integral_even_pow_mul_gaussianHermiteDefectDensity, gaussianHermiteRawScoreGap,
    gaussianHermiteRawMoment, gaussianHermiteRawMoment]
  ring

private theorem sq_evenObservable_mul_eq {N : ℕ} (a : Fin N → ℝ) (D : ℝ → ℝ) (x : ℝ) :
    (∑ i, a i * x ^ (2 * (i : ℕ))) ^ 2 * D x =
      ∑ i, ∑ j, a i * a j * (x ^ (2 * ((i : ℕ) + (j : ℕ))) * D x) := by
  rw [sq, Finset.sum_mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show 2 * ((i : ℕ) + (j : ℕ)) = 2 * (i : ℕ) + 2 * (j : ℕ) by ring, pow_add]
  ring

/-- The model form is the defect-density integral of the squared even observable. -/
theorem gaussianHermiteFiniteScoreGap_eq_integral (τ : ℝ) {N : ℕ} (a : Fin N → ℝ) :
    gaussianHermiteFiniteScoreGap τ a = thetaCuspRawEvenMoment 0 *
      ∫ x, (∑ i, a i * x ^ (2 * (i : ℕ))) ^ 2 * gaussianHermiteDefectDensity τ x := by
  have hsq := sq_evenObservable_mul_eq a (gaussianHermiteDefectDensity τ)
  simp_rw [hsq]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ =>
    (integrable_pow_mul_gaussianHermiteDefectDensity τ _).const_mul _)]
  simp_rw [integral_finsetSum _ (fun j _ =>
    (integrable_pow_mul_gaussianHermiteDefectDensity τ _).const_mul _), integral_const_mul]
  unfold gaussianHermiteFiniteScoreGap
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [gaussianHermiteRawScoreGap_eq_integral]
  ring

/-! ## The calibrated floor -/

private theorem continuous_firstAtom : Continuous (thetaCuspBornWittenAmplitude 1) := by
  unfold thetaCuspBornWittenAmplitude thetaCuspBornWittenWeight
    thetaCuspMorseSuperpotential thetaCuspMorseGroundState
    thetaCuspMorseZeroMode thetaCuspMorseScale
  fun_prop

theorem gaussianHermiteDensity_zero_eq (x : ℝ) :
    gaussianHermiteDensity 0 x = 6 / Real.sqrt (2 * Real.pi) * Real.exp (-18 * x ^ 2) := by
  unfold gaussianHermiteDensity stdGaussianDensity
  rw [show -(1 / 2) * (6 * x) ^ 2 = -18 * x ^ 2 by ring]
  ring

section Small

variable {L τ : ℝ} (hL : 0 ≤ L) (hP : ∀ y : ℝ, y ^ 10 / 2 - L ≤ hermiteBoundaryPoly y)
  (hτ : 0 ≤ τ) (hτ₀ : τ ≤ gaussianHermiteThreshold L)
include hL hP hτ hτ₀

/-- **Pointwise calibrated floor.**  On `x ≥ 0`,
`π ψ_1(x)² (x-1)² ≤ (110843/111104) · A · (ρ_τ - 16xρ_τ' - 303x²ρ_τ)(x)`. -/
theorem firstAtom_le_calibrated_gaussianHermiteDefect {x : ℝ} (hx : 0 ≤ x) :
    Real.pi * thetaCuspBornWittenAmplitude 1 x ^ 2 * (x - 1) ^ 2 ≤
      (110843 / 111104 : ℝ) * (thetaCuspRawEvenMoment 0 * gaussianHermiteDefectDensity τ x) := by
  have henv := thetaCuspFirstAtom_gaussianScoreEnvelope hx
  have hA := nine_div_twenty_le_thetaCuspRawEvenMoment_zero
  have hD := one_add_mul_le_gaussianHermiteDefectDensity hL hP hτ hτ₀ hx
  have hρ := nine_tenths_mul_le_gaussianHermiteDensity hL hP hτ hτ₀ x
  rw [gaussianHermiteDensity_zero_eq] at hρ
  have hsq : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hE : 0 < Real.exp (-18 * x ^ 2) := Real.exp_pos _
  have hq : 0 ≤ 1 + 177 * x ^ 2 := by positivity
  have hρpos := gaussianHermiteDensity_pos hL hP hτ hτ₀ x
  -- `A · defect ≥ (9/20)(1+177x²)(9/10)(6/√(2π))e^{-18x²}`
  have hkey : 243 / (100 * Real.sqrt (2 * Real.pi)) * Real.exp (-18 * x ^ 2) * (1 + 177 * x ^ 2) ≤
      thetaCuspRawEvenMoment 0 * gaussianHermiteDefectDensity τ x := by
    have h1 : 9 / 10 * (6 / Real.sqrt (2 * Real.pi) * Real.exp (-18 * x ^ 2)) * (1 + 177 * x ^ 2) ≤
        gaussianHermiteDefectDensity τ x :=
      (mul_le_mul_of_nonneg_right hρ hq).trans (by nlinarith)
    have h2 := mul_le_mul hA h1 (by positivity) (by linarith)
    calc 243 / (100 * Real.sqrt (2 * Real.pi)) * Real.exp (-18 * x ^ 2) * (1 + 177 * x ^ 2) =
        9 / 20 * (9 / 10 * (6 / Real.sqrt (2 * Real.pi) * Real.exp (-18 * x ^ 2)) *
          (1 + 177 * x ^ 2)) := by field_simp; ring
      _ ≤ _ := h2
  calc Real.pi * thetaCuspBornWittenAmplitude 1 x ^ 2 * (x - 1) ^ 2 ≤
      (110843 / 111104 : ℝ) * (243 / (100 * Real.sqrt (2 * Real.pi))) *
        Real.exp (-18 * x ^ 2) * (1 + 177 * x ^ 2) := henv
    _ = (110843 / 111104 : ℝ) * (243 / (100 * Real.sqrt (2 * Real.pi)) *
        Real.exp (-18 * x ^ 2) * (1 + 177 * x ^ 2)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hkey (by norm_num)

/-- **Calibrated floor with uniform strict surplus.**  For every coefficient vector,
`(111104/110843) · 2π ∫_0^∞ (Σ a_i x^{2i})² (x-1)² ψ_1² ≤ Σ a_i a_j G^τ_{i+j}`. -/
theorem gaussianHermiteFiniteScoreGap_ge_firstAtomSquare {N : ℕ} (a : Fin N → ℝ) :
    (111104 / 110843 : ℝ) * (2 * Real.pi * ∫ x : ℝ in Ioi 0,
      (∑ i, a i * x ^ (2 * (i : ℕ))) ^ 2 * (x - 1) ^ 2 *
        thetaCuspBornWittenAmplitude 1 x ^ 2) ≤ gaussianHermiteFiniteScoreGap τ a := by
  set O : ℝ → ℝ := fun x => (∑ i, a i * x ^ (2 * (i : ℕ))) ^ 2 with hO
  set M : ℝ → ℝ := fun x => O x * (thetaCuspRawEvenMoment 0 * gaussianHermiteDefectDensity τ x)
    with hM
  have hOeven : ∀ x, O (-x) = O x := by
    intro x
    simp only [hO]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [pow_mul, pow_mul, neg_sq]
  have hMint : Integrable M := by
    have h := (integrable_finsetSum (Finset.univ : Finset (Fin N)) fun (i : Fin N) _ =>
      integrable_finsetSum (Finset.univ : Finset (Fin N)) fun (j : Fin N) _ =>
      (integrable_pow_mul_gaussianHermiteDefectDensity τ (2 * ((i : ℕ) + (j : ℕ)))).const_mul
        (a i * a j)).const_mul (thetaCuspRawEvenMoment 0)
    refine h.congr (Eventually.of_forall fun x => ?_)
    simp only [hM, hO]
    rw [← sq_evenObservable_mul_eq a (gaussianHermiteDefectDensity τ) x]
    ring
  have hMeven : ∀ x, M (-x) = M x := by
    intro x
    simp only [hM]
    rw [hOeven, gaussianHermiteDefectDensity_neg]
  have hform : gaussianHermiteFiniteScoreGap τ a = 2 * ∫ x in Ioi 0, M x := by
    rw [gaussianHermiteFiniteScoreGap_eq_integral, ← integral_const_mul]
    have hI := intervalIntegral.integral_Iic_add_Ioi (b := 0) hMint.integrableOn hMint.integrableOn
    have hneg : ∫ x in Iic 0, M x = ∫ x in Ioi 0, M x := by
      have := integral_comp_neg_Iic 0 M
      simp only [hMeven, neg_zero] at this
      exact this
    rw [hneg] at hI
    have : (∫ x, thetaCuspRawEvenMoment 0 *
        ((∑ i, a i * x ^ (2 * (i : ℕ))) ^ 2 * gaussianHermiteDefectDensity τ x)) = ∫ x, M x := by
      congr 1; funext x; simp only [hM, hO]; ring
    rw [this, ← hI]
    ring
  have hfloor_meas : AEStronglyMeasurable (fun x : ℝ =>
      (∑ i, a i * x ^ (2 * (i : ℕ))) ^ 2 * (x - 1) ^ 2 * thetaCuspBornWittenAmplitude 1 x ^ 2)
      (volume.restrict (Ioi 0)) := by
    have := continuous_firstAtom
    exact (by fun_prop : Continuous fun x : ℝ =>
      (∑ i, a i * x ^ (2 * (i : ℕ))) ^ 2 * (x - 1) ^ 2 *
        thetaCuspBornWittenAmplitude 1 x ^ 2).aestronglyMeasurable
  have hpt : ∀ x ∈ Ioi (0 : ℝ), Real.pi * ((∑ i, a i * x ^ (2 * (i : ℕ))) ^ 2 * (x - 1) ^ 2 *
      thetaCuspBornWittenAmplitude 1 x ^ 2) ≤ (110843 / 111104 : ℝ) * M x := by
    intro x hx
    have h := firstAtom_le_calibrated_gaussianHermiteDefect hL hP hτ hτ₀ (le_of_lt hx)
    have hO0 : 0 ≤ O x := by simp only [hO]; positivity
    simp only [hM]
    calc Real.pi * ((∑ i, a i * x ^ (2 * (i : ℕ))) ^ 2 * (x - 1) ^ 2 *
          thetaCuspBornWittenAmplitude 1 x ^ 2) =
        O x * (Real.pi * thetaCuspBornWittenAmplitude 1 x ^ 2 * (x - 1) ^ 2) := by
          simp only [hO]; ring
      _ ≤ O x * ((110843 / 111104 : ℝ) * (thetaCuspRawEvenMoment 0 *
          gaussianHermiteDefectDensity τ x)) := mul_le_mul_of_nonneg_left h hO0
      _ = _ := by ring
  have hfloor_int : IntegrableOn (fun x : ℝ =>
      (∑ i, a i * x ^ (2 * (i : ℕ))) ^ 2 * (x - 1) ^ 2 * thetaCuspBornWittenAmplitude 1 x ^ 2)
      (Ioi 0) := by
    refine Integrable.mono' ((hMint.integrableOn).const_mul
      ((110843 / 111104 : ℝ) / Real.pi)) hfloor_meas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have h := hpt x hx
    have hnn : 0 ≤ (∑ i, a i * x ^ (2 * (i : ℕ))) ^ 2 * (x - 1) ^ 2 *
        thetaCuspBornWittenAmplitude 1 x ^ 2 := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    have hpi := Real.pi_pos
    rw [div_mul_eq_mul_div, le_div_iff₀ hpi]
    linarith
  have hmono := setIntegral_mono_on (hfloor_int.const_mul Real.pi)
    ((hMint.integrableOn).const_mul (110843 / 111104 : ℝ)) measurableSet_Ioi hpt
  rw [integral_const_mul, integral_const_mul] at hmono
  rw [hform]
  have hc : (0 : ℝ) < 111104 / 110843 := by norm_num
  calc (111104 / 110843 : ℝ) * (2 * Real.pi * ∫ x : ℝ in Ioi 0,
        (∑ i, a i * x ^ (2 * (i : ℕ))) ^ 2 * (x - 1) ^ 2 *
          thetaCuspBornWittenAmplitude 1 x ^ 2) =
      (111104 / 110843 : ℝ) * 2 * (Real.pi * ∫ x : ℝ in Ioi 0,
        (∑ i, a i * x ^ (2 * (i : ℕ))) ^ 2 * (x - 1) ^ 2 *
          thetaCuspBornWittenAmplitude 1 x ^ 2) := by ring
    _ ≤ (111104 / 110843 : ℝ) * 2 * ((110843 / 111104 : ℝ) * ∫ x in Ioi 0, M x) :=
        mul_le_mul_of_nonneg_left hmono (by positivity)
    _ = 2 * ∫ x in Ioi 0, M x := by ring

omit hL hP hτ hτ₀ in
private theorem coefficientObservable_eq_eval (P : ℝ[X]) (x : ℝ) :
    (∑ i : Fin (P.natDegree + 1), P.coeff i * x ^ (2 * (i : ℕ))) = P.eval (x ^ 2) := by
  rw [Polynomial.eval_eq_sum_range, ← Fin.sum_univ_eq_sum_range]
  simp only [pow_mul]

/-- **Calibrated polynomial floor.**  Every polynomial, at every degree. -/
theorem gaussianHermitePolynomialScoreGap_ge_firstAtomSquare (P : ℝ[X]) :
    (111104 / 110843 : ℝ) * (2 * Real.pi * ∫ x : ℝ in Ioi 0,
      P.eval (x ^ 2) ^ 2 * (x - 1) ^ 2 * thetaCuspBornWittenAmplitude 1 x ^ 2) ≤
      gaussianHermitePolynomialScoreGap τ P := by
  have h := gaussianHermiteFiniteScoreGap_ge_firstAtomSquare hL hP hτ hτ₀
    (fun i : Fin (P.natDegree + 1) => P.coeff i)
  beta_reduce at h
  simp_rw [coefficientObservable_eq_eval] at h
  exact h

/-- **Strict surplus.**  Every nonzero polynomial strictly exceeds the prescribed floor. -/
theorem firstAtomSquare_lt_gaussianHermitePolynomialScoreGap {P : ℝ[X]} (hP0 : P ≠ 0) :
    2 * Real.pi * (∫ x : ℝ in Ioi 0,
      P.eval (x ^ 2) ^ 2 * (x - 1) ^ 2 * thetaCuspBornWittenAmplitude 1 x ^ 2) <
      gaussianHermitePolynomialScoreGap τ P := by
  have hpos := integral_thetaCuspFirstAtom_polynomialSquare_pos hP0
  have h := gaussianHermitePolynomialScoreGap_ge_firstAtomSquare hL hP hτ hτ₀ P
  have hF : 0 < 2 * Real.pi * (∫ x : ℝ in Ioi 0,
      P.eval (x ^ 2) ^ 2 * (x - 1) ^ 2 * thetaCuspBornWittenAmplitude 1 x ^ 2) := by
    have := Real.pi_pos; positivity
  nlinarith

end Small

/-! ## The prime–archimedean size-three determinant -/

/-- The prime–archimedean source moments as polynomials in normalized even moments. -/
def primeArchMomentOfEvenMoments (m : ℕ → ℝ) : ℕ → ℝ
  | 0 => m 1
  | 1 => m 1 ^ 2 / 2 - m 2 / 6
  | 2 => m 3 / 120 - m 1 * m 2 / 8 + m 1 ^ 3 / 4
  | 3 => -m 4 / 5040 + m 1 * m 3 / 180 + m 2 ^ 2 / 144 - m 1 ^ 2 * m 2 / 12 + m 1 ^ 4 / 8
  | _ => (m 5 - 9 * m 1 * m 4 + 504 * (m 1 ^ 2 / 2 - m 2 / 6) * m 3 -
      15120 * (m 3 / 120 - m 1 * m 2 / 8 + m 1 ^ 3 / 4) * m 2 +
      181440 * (-m 4 / 5040 + m 1 * m 3 / 180 + m 2 ^ 2 / 144 - m 1 ^ 2 * m 2 / 12 +
        m 1 ^ 4 / 8) * m 1) / 362880

/-- The size-three leading Hankel determinant of the prime–archimedean source moments. -/
def primeArchHankelDetOfEvenMoments (m : ℕ → ℝ) : ℝ :=
  let μ := primeArchMomentOfEvenMoments m
  (μ 0 * μ 2 - μ 1 ^ 2) * μ 4 - (μ 0 * μ 3 ^ 2 - 2 * μ 1 * μ 2 * μ 3 + μ 2 ^ 3)

/-- On the actual normalized moments the map is the actual source-moment determinant. -/
theorem primeArchHankelDetOfEvenMoments_actual :
    primeArchHankelDetOfEvenMoments thetaCuspNormalizedEvenMoment =
      (normalizedPrimeArchMoment 0 * normalizedPrimeArchMoment 2 -
          normalizedPrimeArchMoment 1 ^ 2) * normalizedPrimeArchMoment 4 -
        (normalizedPrimeArchMoment 0 * normalizedPrimeArchMoment 3 ^ 2 -
          2 * normalizedPrimeArchMoment 1 * normalizedPrimeArchMoment 2 *
            normalizedPrimeArchMoment 3 + normalizedPrimeArchMoment 2 ^ 3) := by
  rw [normalizedPrimeArchMoment_four_eq_thetaCuspNormalizedEvenMoment,
    normalizedPrimeArchMoment_three_eq_thetaCuspNormalizedEvenMoment,
    normalizedPrimeArchMoment_two_eq_thetaCuspNormalizedEvenMoment,
    normalizedPrimeArchMoment_one_eq_thetaCuspNormalizedEvenMoment,
    normalizedPrimeArchMoment_zero_eq_thetaCuspNormalizedEvenMoment]
  simp only [primeArchHankelDetOfEvenMoments, primeArchMomentOfEvenMoments]

/-- Normalized model moments `R^τ_j / R^τ_0`. -/
def gaussianHermiteNormalizedMoment (τ : ℝ) (j : ℕ) : ℝ :=
  gaussianHermiteRawMoment τ j / gaussianHermiteRawMoment τ 0

theorem gaussianHermiteNormalizedMoment_eq (τ : ℝ) (j : ℕ) :
    gaussianHermiteNormalizedMoment τ j =
      (1 / 6) ^ (2 * j) * (gaussianEvenWickMoment j + τ * hermiteBoundaryWickCorrection j) := by
  rw [gaussianHermiteNormalizedMoment, gaussianHermiteRawMoment_zero, gaussianHermiteRawMoment_eq]
  field_simp [thetaCuspRawEvenMoment_zero_pos.ne']

/-- **Normalized determinant of the countermodel.**  The amplitude cancels and
`det = 6^{-18} τ² (-196 + 324τ + 16τ²)`. -/
theorem primeArchHankelDetOfEvenMoments_gaussianHermite (τ : ℝ) :
    primeArchHankelDetOfEvenMoments (gaussianHermiteNormalizedMoment τ) =
      (1 / 6) ^ 18 * (τ ^ 2 * (-196 + 324 * τ + 16 * τ ^ 2)) := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hermiteBoundaryWickCorrection_exact
  have hm : ∀ j, gaussianHermiteNormalizedMoment τ j =
      (1 / 6) ^ (2 * j) * (gaussianEvenWickMoment j + τ * hermiteBoundaryWickCorrection j) :=
    gaussianHermiteNormalizedMoment_eq τ
  rw [← hermiteDet_eq, ← hermiteDet_spatialScale]
  simp only [primeArchHankelDetOfEvenMoments, primeArchMomentOfEvenMoments, hm, h1, h2, h3, h4,
    h5]
  simp only [hermiteV, hermiteW, hermiteZ, hermiteY, hermiteB, hermiteC, hermiteE, hermiteF,
    gaussianEvenWickMoment]
  ring

/-- The countermodel determinant is strictly negative for `0 < τ < 1/2`. -/
theorem primeArchHankelDetOfEvenMoments_gaussianHermite_neg {τ : ℝ} (hτ : 0 < τ)
    (hτ1 : τ < 1 / 2) :
    primeArchHankelDetOfEvenMoments (gaussianHermiteNormalizedMoment τ) < 0 := by
  rw [primeArchHankelDetOfEvenMoments_gaussianHermite, ← hermiteDet_eq]
  exact mul_neg_of_pos_of_neg (by positivity) (hermitePerturbation_det_neg hτ hτ1)

/-! ## The packaged countermodel -/

/-- **Literal-mass calibrated score-floor countermodel.**  For all sufficiently small `τ > 0` the
Gaussian–Hermite density is a probability density, at least `(9/10)ρ_0`, strongly log-concave
with `-(log ρ_τ)'' ≥ 30`, has score defect at least `1 + 177x²`; at the literal actual raw
mass it reproduces the complete fixed first-atom polynomial floor with the uniform strict surplus
`111104/110843`, while its normalized prime–archimedean determinant is negative. -/
theorem exists_gaussianHermite_calibrated_countermodel :
    ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∀ τ : ℝ, 0 < τ → τ ≤ τ₀ →
      (∫ x, gaussianHermiteDensity τ x = 1) ∧
      (∀ x, 0 < gaussianHermiteDensity τ x) ∧
      (∀ x, 9 / 10 * gaussianHermiteDensity 0 x ≤ gaussianHermiteDensity τ x) ∧
      (∀ x, 30 ≤ -deriv (deriv fun x => Real.log (gaussianHermiteDensity τ x)) x) ∧
      (∀ x, 0 ≤ x → (1 + 177 * x ^ 2) * gaussianHermiteDensity τ x ≤
        gaussianHermiteDefectDensity τ x) ∧
      gaussianHermiteRawMoment τ 0 = thetaCuspRawEvenMoment 0 ∧
      (∀ P : ℝ[X], (111104 / 110843 : ℝ) * (2 * Real.pi * ∫ x : ℝ in Ioi 0,
        P.eval (x ^ 2) ^ 2 * (x - 1) ^ 2 * thetaCuspBornWittenAmplitude 1 x ^ 2) ≤
          gaussianHermitePolynomialScoreGap τ P) ∧
      (∀ P : ℝ[X], P ≠ 0 → 2 * Real.pi * (∫ x : ℝ in Ioi 0,
        P.eval (x ^ 2) ^ 2 * (x - 1) ^ 2 * thetaCuspBornWittenAmplitude 1 x ^ 2) <
          gaussianHermitePolynomialScoreGap τ P) ∧
      primeArchHankelDetOfEvenMoments (gaussianHermiteNormalizedMoment τ) =
        (1 / 6) ^ 18 * (τ ^ 2 * (-196 + 324 * τ + 16 * τ ^ 2)) ∧
      primeArchHankelDetOfEvenMoments (gaussianHermiteNormalizedMoment τ) < 0 := by
  obtain ⟨L, hL, hP⟩ := exists_hermiteBoundaryPoly_lower
  have hT := gaussianHermiteThreshold_pos hL
  have hThalf : gaussianHermiteThreshold L < 1 / 2 := by
    unfold gaussianHermiteThreshold
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [mul_nonneg (by norm_num : (0 : ℝ) ≤ 10) hL]
  refine ⟨gaussianHermiteThreshold L, hT, fun τ hτ hτ₀ => ?_⟩
  exact ⟨integral_gaussianHermiteDensity τ,
    gaussianHermiteDensity_pos hL hP hτ.le hτ₀,
    nine_tenths_mul_le_gaussianHermiteDensity hL hP hτ.le hτ₀,
    thirty_le_neg_deriv_deriv_log_gaussianHermiteDensity hL hP hτ.le hτ₀,
    fun x hx => one_add_mul_le_gaussianHermiteDefectDensity hL hP hτ.le hτ₀ hx,
    gaussianHermiteRawMoment_zero τ,
    gaussianHermitePolynomialScoreGap_ge_firstAtomSquare hL hP hτ.le hτ₀,
    fun P hP0 => firstAtomSquare_lt_gaussianHermitePolynomialScoreGap hL hP hτ.le hτ₀ hP0,
    primeArchHankelDetOfEvenMoments_gaussianHermite τ,
    primeArchHankelDetOfEvenMoments_gaussianHermite_neg hτ (hτ₀.trans_lt hThalf)⟩

end RHTower
