import GaloisForLFunctions.OrderSixMetaplecticTheory.TheConstantTermOfTheCompositeRemainderIsFiveBesselSeries
import GaloisForLFunctions.OrderSixMetaplecticTheory.TheDilateCorrelationAtAPrimaryPrimeCarriesTheDoublePole

/-!
# The composite dilate combination carries the double pole

With `ρ = |p|`, `σ = |q|`, `χ = (p/q)₃`, the Mellin transform of the constant term of `G'_m`
(`cuspConstantTerm_remainder`) gives (`integral_remainder_mul_eisenstein`)

`∫ G'_mE(s) = N(m)|P|·(M(s)K_m(s) − (2 + 2χ)M(s)D(s))`,

`K_m = 2ρ^{−s}σ^{−s}D_A + 2χρ^{−s}σ^{−s}D_B + 2ρ^{−s}σ^{s−1}D_{UL} + 2σ^{−s}ρ^{s−1}D_{LU} + ρ^{s−1}σ^{s−1}D_m`
(`combination`). Since `G'_m` has at most a simple pole at `4/3`, `M(s)K_m(s)` carries the double pole of
`(2 + 2χ)M(s)D(s)` (`combination_double_pole`): `(s − 4/3)²M(s)K_m(s) → (2 + 2χ)·108π³r³`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped BigOperators Classical MatrixGroups

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicJacobi
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicKubota SpectralTheoryOfTheCubicCover

/-- Products of two theta coefficients at dilated frequencies are absolutely summable against `|ξ_h|^{−σ}`,
`σ > 4`: by `xy ≤ (x² + y²)/2` and the square series. -/
theorem summable_coeff_of_le (F : O → ℂ) (g₁ g₂ : O → O) {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hg₁ : Function.Injective g₁) (hg₂ : Function.Injective g₂)
    (hn₁ : ∀ h, ‖cuspFrequency (g₁ h)‖ = c₁ * ‖cuspFrequency h‖)
    (hn₂ : ∀ h, ‖cuspFrequency (g₂ h)‖ = c₂ * ‖cuspFrequency h‖)
    (hF : ∀ h, ‖F h‖ ≤ ‖rationalSourceResidualFourierCoefficient (g₁ h)‖ *
      ‖rationalSourceResidualFourierCoefficient (g₂ h)‖) {σ : ℝ} (hσ : 4 < σ) :
    Summable (fun h : O => if h = 0 then 0 else ‖F h‖ * ‖cuspFrequency h‖ ^ (-σ)) := by
  set A : O → ℝ := fun h => if h = 0 then 0 else
    ‖rationalSourceResidualFourierCoefficient h‖ ^ 2 * ‖cuspFrequency h‖ ^ (-σ) with hAdef
  have hA : Summable A := summable_sourceCoefficient_sq_rpow hσ
  have hA0 : ∀ h, 0 ≤ A h := fun h => by
    simp only [hAdef]
    split_ifs <;> positivity
  have hne : ∀ (g : O → O) (c : ℝ), 0 < c → (∀ h, ‖cuspFrequency (g h)‖ = c * ‖cuspFrequency h‖) →
      ∀ h, h ≠ 0 → g h ≠ 0 := fun g c hc hn h hh h0 => by
    have h1 := hn h
    have hξ : 0 < ‖cuspFrequency h‖ := norm_pos_iff.mpr (cuspFrequency_ne_zero h hh)
    have h2 : ‖cuspFrequency (0 : O)‖ = 0 := by simp [cuspFrequency]
    rw [h0, h2] at h1
    nlinarith [mul_pos hc hξ]
  refine Summable.of_nonneg_of_le (fun h => ?_) (fun h => ?_)
    ((((hA.comp_injective hg₁).mul_left (c₁ ^ σ)).add ((hA.comp_injective hg₂).mul_left (c₂ ^ σ))).mul_left (1 / 2))
  · split_ifs <;> positivity
  · simp only [Function.comp_apply]
    split_ifs with hh
    · exact mul_nonneg (by norm_num) (add_nonneg (mul_nonneg (Real.rpow_nonneg hc₁.le σ) (hA0 _))
        (mul_nonneg (Real.rpow_nonneg hc₂.le σ) (hA0 _)))
    · have hξ : 0 < ‖cuspFrequency h‖ := norm_pos_iff.mpr (cuspFrequency_ne_zero h hh)
      have e : ∀ (g : O → O) (c : ℝ), 0 < c → (∀ h, ‖cuspFrequency (g h)‖ = c * ‖cuspFrequency h‖) → g h ≠ 0 →
          c ^ σ * A (g h) = ‖rationalSourceResidualFourierCoefficient (g h)‖ ^ 2 * ‖cuspFrequency h‖ ^ (-σ) := by
        intro g c hc hn hgh
        have hcs := (Real.rpow_pos_of_pos hc σ).ne'
        simp only [hAdef, if_neg hgh, hn, Real.mul_rpow hc.le hξ.le, Real.rpow_neg hc.le]
        field_simp
      rw [e g₁ c₁ hc₁ hn₁ (hne g₁ c₁ hc₁ hn₁ h hh), e g₂ c₂ hc₂ hn₂ (hne g₂ c₂ hc₂ hn₂ h hh)]
      have hw : 0 ≤ ‖cuspFrequency h‖ ^ (-σ) := Real.rpow_nonneg hξ.le _
      have hx := norm_nonneg (rationalSourceResidualFourierCoefficient (g₁ h))
      have hy := norm_nonneg (rationalSourceResidualFourierCoefficient (g₂ h))
      calc ‖F h‖ * ‖cuspFrequency h‖ ^ (-σ) ≤ ‖rationalSourceResidualFourierCoefficient (g₁ h)‖ *
            ‖rationalSourceResidualFourierCoefficient (g₂ h)‖ * ‖cuspFrequency h‖ ^ (-σ) :=
          mul_le_mul_of_nonneg_right (hF h) hw
        _ ≤ 1 / 2 * (‖rationalSourceResidualFourierCoefficient (g₁ h)‖ ^ 2 * ‖cuspFrequency h‖ ^ (-σ) +
            ‖rationalSourceResidualFourierCoefficient (g₂ h)‖ ^ 2 * ‖cuspFrequency h‖ ^ (-σ)) := by
          nlinarith [mul_nonneg (sq_nonneg (‖rationalSourceResidualFourierCoefficient (g₁ h)‖ -
            ‖rationalSourceResidualFourierCoefficient (g₂ h)‖)) hw]

theorem injective_mul_const {c : O} (hc : c ≠ 0) : Function.Injective (fun h : O => h * c) :=
  fun _ _ h => mul_right_cancel₀ hc h

theorem injective_neg_mul_const {c : O} (hc : c ≠ 0) : Function.Injective (fun h : O => -(h * c)) :=
  fun _ _ h => mul_right_cancel₀ hc (neg_injective h)

namespace PrimaryPair

variable (R : PrimaryPair)

/-! ### Summability of the five series -/

theorem summable_shiftCoeff {σ : ℝ} (hσ : 4 < σ) :
    Summable (fun h : O => if h = 0 then 0 else ‖R.shiftCoeff h‖ * ‖cuspFrequency h‖ ^ (-σ)) := by
  have hc : R.P.p * R.Q.p * R.Q.p * R.P.p ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero R.P.ne_zero R.Q.ne_zero) R.Q.ne_zero) R.P.ne_zero
  refine summable_coeff_of_le _ id (fun h => -(h * (R.P.p * R.Q.p)) * R.Q.p * R.P.p) one_pos
    (mul_pos (pow_pos R.P.norm_pos 2) (pow_pos R.Q.norm_pos 2)) Function.injective_id
    (fun a b hab => mul_right_cancel₀ hc (by linear_combination -hab)) (fun h => (one_mul _).symm)
    (fun h => ?_) (fun h => (by rw [shiftCoeff, norm_mul]; rfl : _ = _).le) hσ
  simp only [cuspFrequency_mul_right, cuspFrequency_neg, norm_mul, norm_neg, map_mul]
  ring

theorem summable_crossCoeff {σ : ℝ} (hσ : 4 < σ) :
    Summable (fun h : O => if h = 0 then 0 else ‖R.crossCoeff h‖ * ‖cuspFrequency h‖ ^ (-σ)) := by
  refine summable_coeff_of_le _ (fun l => l * R.Q.p * R.Q.p) (fun l => -(l * R.P.p) * R.P.p)
    (pow_pos R.Q.norm_pos 2) (pow_pos R.P.norm_pos 2)
    (fun a b hab => mul_right_cancel₀ R.QQ_ne_zero (by linear_combination hab))
    (fun a b hab => mul_right_cancel₀ R.PP_ne_zero (by linear_combination -hab))
    (fun h => ?_) (fun h => ?_) (fun h => (by rw [crossCoeff, norm_mul] : _ = _).le) hσ
  · simp only [cuspFrequency_mul_right, norm_mul]
    ring
  · simp only [cuspFrequency_mul_right, cuspFrequency_neg, norm_mul, norm_neg]
    ring

theorem summable_ulCoeff {σ : ℝ} (hσ : 4 < σ) :
    Summable (fun h : O => if h = 0 then 0 else ‖R.ulCoeff h‖ * ‖cuspFrequency h‖ ^ (-σ)) := by
  refine summable_coeff_of_le _ (fun k => k * R.Q.p) (fun k => -(k * (R.P.p * R.P.p)))
    R.Q.norm_pos (pow_pos R.P.norm_pos 2) (injective_mul_const R.Q.ne_zero) (injective_neg_mul_const R.PP_ne_zero)
    (fun h => ?_) (fun h => ?_) (fun h => ?_) hσ
  · simp only [cuspFrequency_mul_right, norm_mul]
    ring
  · simp only [cuspFrequency_mul_right, cuspFrequency_neg, norm_mul, norm_neg, map_mul]
    ring
  · rw [ulCoeff]
    split_ifs
    · rw [norm_zero]
      positivity
    · rw [norm_mul]

theorem summable_luCoeff {σ : ℝ} (hσ : 4 < σ) :
    Summable (fun h : O => if h = 0 then 0 else ‖R.luCoeff h‖ * ‖cuspFrequency h‖ ^ (-σ)) := by
  refine summable_coeff_of_le _ (fun k => k * R.P.p) (fun k => -(k * (R.Q.p * R.Q.p)))
    R.P.norm_pos (pow_pos R.Q.norm_pos 2) (injective_mul_const R.P.ne_zero) (injective_neg_mul_const R.QQ_ne_zero)
    (fun h => ?_) (fun h => ?_) (fun h => ?_) hσ
  · simp only [cuspFrequency_mul_right, norm_mul]
    ring
  · simp only [cuspFrequency_mul_right, cuspFrequency_neg, norm_mul, norm_neg, map_mul]
    ring
  · rw [luCoeff]
    split_ifs
    · rw [norm_zero]
      positivity
    · rw [norm_mul]

theorem summable_mDilateCoeff {σ : ℝ} (hσ : 4 < σ) :
    Summable (fun h : O => if h = 0 then 0 else ‖R.mDilateCoeff h‖ * ‖cuspFrequency h‖ ^ (-σ)) := by
  refine summable_coeff_of_le _ id (fun k => k * (R.P.p * R.Q.p)) one_pos (mul_pos R.P.norm_pos R.Q.norm_pos)
    Function.injective_id (injective_mul_const (mul_ne_zero R.P.ne_zero R.Q.ne_zero)) (fun h => (one_mul _).symm)
    (fun h => ?_) (fun h => ?_) hσ
  · simp only [cuspFrequency_mul_right, norm_mul, map_mul]
    ring
  · rw [mDilateCoeff]
    split_ifs
    · rw [norm_zero]
      positivity
    · rw [norm_mul]
      rfl

/-! ### The Mellin identity -/

/-- `K_m(s)`: the five Dirichlet series of the constant term with their Mellin factors. -/
def combination (s : ℂ) : ℂ :=
  2 * (((‖ringComplex R.P.p‖ : ℝ) : ℂ) ^ (-s) * ((‖ringComplex R.Q.p‖ : ℝ) : ℂ) ^ (-s)) *
      besselDirichlet R.shiftCoeff s +
    2 * ringComplex (symbol R.P.p R.Q.p) *
      (((‖ringComplex R.P.p‖ : ℝ) : ℂ) ^ (-s) * ((‖ringComplex R.Q.p‖ : ℝ) : ℂ) ^ (-s)) *
        besselDirichlet R.crossCoeff s +
    2 * (((‖ringComplex R.P.p‖ : ℝ) : ℂ) ^ (-s) * ((‖ringComplex R.Q.p‖ : ℝ) : ℂ) ^ (s - 1)) *
      besselDirichlet R.ulCoeff s +
    2 * (((‖ringComplex R.Q.p‖ : ℝ) : ℂ) ^ (-s) * ((‖ringComplex R.P.p‖ : ℝ) : ℂ) ^ (s - 1)) *
      besselDirichlet R.luCoeff s +
    ((‖ringComplex R.P.p‖ : ℝ) : ℂ) ^ (s - 1) * ((‖ringComplex R.Q.p‖ : ℝ) : ℂ) ^ (s - 1) *
      besselDirichlet R.mDilateCoeff s

theorem cpow_identities (s : ℂ) :
    ((‖ringComplex R.P.p‖ : ℂ) ^ 2 * (‖ringComplex R.Q.p‖ : ℂ) ^ 2)⁻¹ *
        ((‖ringComplex R.P.p‖ * ‖ringComplex R.Q.p‖ : ℝ) : ℂ) ^ (2 - s) =
      ((‖ringComplex R.P.p‖ : ℝ) : ℂ) ^ (-s) * ((‖ringComplex R.Q.p‖ : ℝ) : ℂ) ^ (-s) ∧
    ((‖ringComplex R.P.p‖ : ℂ) ^ 2)⁻¹ * (‖ringComplex R.Q.p‖ : ℂ) *
        ((‖ringComplex R.P.p‖ / ‖ringComplex R.Q.p‖ : ℝ) : ℂ) ^ (2 - s) =
      ((‖ringComplex R.P.p‖ : ℝ) : ℂ) ^ (-s) * ((‖ringComplex R.Q.p‖ : ℝ) : ℂ) ^ (s - 1) ∧
    ((‖ringComplex R.Q.p‖ : ℂ) ^ 2)⁻¹ * (‖ringComplex R.P.p‖ : ℂ) *
        ((‖ringComplex R.Q.p‖ / ‖ringComplex R.P.p‖ : ℝ) : ℂ) ^ (2 - s) =
      ((‖ringComplex R.Q.p‖ : ℝ) : ℂ) ^ (-s) * ((‖ringComplex R.P.p‖ : ℝ) : ℂ) ^ (s - 1) ∧
    (‖ringComplex R.P.p‖ : ℂ) * (‖ringComplex R.Q.p‖ : ℂ) *
        ((1 / (‖ringComplex R.P.p‖ * ‖ringComplex R.Q.p‖) : ℝ) : ℂ) ^ (2 - s) =
      ((‖ringComplex R.P.p‖ : ℝ) : ℂ) ^ (s - 1) * ((‖ringComplex R.Q.p‖ : ℝ) : ℂ) ^ (s - 1) := by
  have hp := R.P.norm_pos
  have hq := R.Q.norm_pos
  obtain ⟨p1, p2⟩ := PrimaryPrime.real_cpow_identities _ hp s
  obtain ⟨q1, q2⟩ := PrimaryPrime.real_cpow_identities _ hq s
  have hpi : (0 : ℝ) ≤ 1 / ‖ringComplex R.P.p‖ := (one_div_pos.mpr hp).le
  have hqi : (0 : ℝ) ≤ 1 / ‖ringComplex R.Q.p‖ := (one_div_pos.mpr hq).le
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hp.le hq.le, ← p1, ← q1, mul_inv]
    ring
  · rw [div_eq_mul_one_div, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hp.le hqi, ← p1, ← q2]
    ring
  · rw [div_eq_mul_one_div, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hq.le hpi, ← q1, ← p2]
    ring
  · rw [← one_div_mul_one_div, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hpi hqi, ← p2, ← q2]
    ring

/-- **The Mellin identity at `m`.** For `4 < Re s < 13/3`:
`∫ G'_mE(s) = N(m)|P|(M(s)K_m(s) − (2 + 2(p/q)₃)M(s)D(s))`. -/
theorem integral_remainder_mul_eisenstein (s : ℂ) (hs4 : 4 < s.re) (hs : s.re < 13 / 3) :
    ∫ w in levelSet, R.remainder w * hyperbolicEisenstein s w ∂hyperbolicVolume =
      R.normM * periodArea * (besselSqMellin s * R.combination s -
        (2 + 2 * ringComplex (symbol R.P.p R.Q.p)) * (besselSqMellin s * thetaSqDirichlet s)) := by
  have hG := R.remainder_remainderData
  have hp := R.P.norm_pos
  have hq := R.Q.norm_pos
  have hs23 : 2 / 3 < s.re := by linarith
  rw [hG.integral_mul_eisenstein s (by linarith) hs]
  have hpt : ∀ v ∈ Set.Ioi (0 : ℝ),
      (v : ℂ) ^ s * (∫ z in periodDomain, R.remainder (cuspCoordinateLift (v, z))) / (v : ℂ) ^ 3 =
        R.normM * periodArea *
          (2 * ((‖ringComplex R.P.p‖ : ℂ) ^ 2 * (‖ringComplex R.Q.p‖ : ℂ) ^ 2)⁻¹ *
              ((v : ℂ) ^ s * besselRemainder R.shiftCoeff ((‖ringComplex R.P.p‖ * ‖ringComplex R.Q.p‖) * v) /
                (v : ℂ) ^ 3) +
            2 * ringComplex (symbol R.P.p R.Q.p) *
              ((‖ringComplex R.P.p‖ : ℂ) ^ 2 * (‖ringComplex R.Q.p‖ : ℂ) ^ 2)⁻¹ *
              ((v : ℂ) ^ s * besselRemainder R.crossCoeff ((‖ringComplex R.P.p‖ * ‖ringComplex R.Q.p‖) * v) /
                (v : ℂ) ^ 3) +
            2 * (((‖ringComplex R.P.p‖ : ℂ) ^ 2)⁻¹ * (‖ringComplex R.Q.p‖ : ℂ)) *
              ((v : ℂ) ^ s * besselRemainder R.ulCoeff ((‖ringComplex R.P.p‖ / ‖ringComplex R.Q.p‖) * v) /
                (v : ℂ) ^ 3) +
            2 * (((‖ringComplex R.Q.p‖ : ℂ) ^ 2)⁻¹ * (‖ringComplex R.P.p‖ : ℂ)) *
              ((v : ℂ) ^ s * besselRemainder R.luCoeff ((‖ringComplex R.Q.p‖ / ‖ringComplex R.P.p‖) * v) /
                (v : ℂ) ^ 3) +
            (‖ringComplex R.P.p‖ : ℂ) * (‖ringComplex R.Q.p‖ : ℂ) *
              ((v : ℂ) ^ s * besselRemainder R.mDilateCoeff ((1 / (‖ringComplex R.P.p‖ * ‖ringComplex R.Q.p‖)) * v) /
                (v : ℂ) ^ 3) -
            (2 + 2 * ringComplex (symbol R.P.p R.Q.p)) *
              ((v : ℂ) ^ s * besselRemainder (fun h => rationalSourceResidualFourierCoefficient h ^ 2) v /
                (v : ℂ) ^ 3)) := by
    intro v (hv : 0 < v)
    have hc := R.cuspConstantTerm_remainder v hv
    rw [cuspConstantTerm] at hc
    rw [hc, show ‖ringComplex R.P.p‖ * (‖ringComplex R.Q.p‖ * v) = (‖ringComplex R.P.p‖ * ‖ringComplex R.Q.p‖) * v
        by ring, show ‖ringComplex R.P.p‖ * v / ‖ringComplex R.Q.p‖ = (‖ringComplex R.P.p‖ / ‖ringComplex R.Q.p‖) * v
        by ring, show ‖ringComplex R.Q.p‖ * v / ‖ringComplex R.P.p‖ = (‖ringComplex R.Q.p‖ / ‖ringComplex R.P.p‖) * v
        by ring, show v / ‖ringComplex R.Q.p‖ / ‖ringComplex R.P.p‖ =
          (1 / (‖ringComplex R.P.p‖ * ‖ringComplex R.Q.p‖)) * v by field_simp]
    ring
  have hA := integrableOn_mellin_comp_mul (besselRemainder R.shiftCoeff) s (mul_pos hp hq)
    (integrableOn_besselRemainder R.shiftCoeff s hs23 (R.summable_shiftCoeff hs4))
  have hB := integrableOn_mellin_comp_mul (besselRemainder R.crossCoeff) s (mul_pos hp hq)
    (integrableOn_besselRemainder R.crossCoeff s hs23 (R.summable_crossCoeff hs4))
  have hU := integrableOn_mellin_comp_mul (besselRemainder R.ulCoeff) s (div_pos hp hq)
    (integrableOn_besselRemainder R.ulCoeff s hs23 (R.summable_ulCoeff hs4))
  have hL := integrableOn_mellin_comp_mul (besselRemainder R.luCoeff) s (div_pos hq hp)
    (integrableOn_besselRemainder R.luCoeff s hs23 (R.summable_luCoeff hs4))
  have hD := integrableOn_mellin_comp_mul (besselRemainder R.mDilateCoeff) s (one_div_pos.mpr (mul_pos hp hq))
    (integrableOn_besselRemainder R.mDilateCoeff s hs23 (R.summable_mDilateCoeff hs4))
  have h0 := integrableOn_besselRemainder (fun h => rationalSourceResidualFourierCoefficient h ^ 2) s hs23
    (summable_sq_coeff hs4)
  have J1 := hA.const_mul (2 * ((‖ringComplex R.P.p‖ : ℂ) ^ 2 * (‖ringComplex R.Q.p‖ : ℂ) ^ 2)⁻¹)
  have J2 := hB.const_mul (2 * ringComplex (symbol R.P.p R.Q.p) *
    ((‖ringComplex R.P.p‖ : ℂ) ^ 2 * (‖ringComplex R.Q.p‖ : ℂ) ^ 2)⁻¹)
  have J3 := hU.const_mul (2 * (((‖ringComplex R.P.p‖ : ℂ) ^ 2)⁻¹ * (‖ringComplex R.Q.p‖ : ℂ)))
  have J4 := hL.const_mul (2 * (((‖ringComplex R.Q.p‖ : ℂ) ^ 2)⁻¹ * (‖ringComplex R.P.p‖ : ℂ)))
  have J5 := hD.const_mul ((‖ringComplex R.P.p‖ : ℂ) * (‖ringComplex R.Q.p‖ : ℂ))
  have J0 := h0.const_mul (2 + 2 * ringComplex (symbol R.P.p R.Q.p))
  have j2 : IntegrableOn (fun v : ℝ =>
        2 * ((‖ringComplex R.P.p‖ : ℂ) ^ 2 * (‖ringComplex R.Q.p‖ : ℂ) ^ 2)⁻¹ * ((v : ℂ) ^ s * besselRemainder R.shiftCoeff ((‖ringComplex R.P.p‖ * ‖ringComplex R.Q.p‖) * v) / (v : ℂ) ^ 3) +
        2 * ringComplex (symbol R.P.p R.Q.p) * ((‖ringComplex R.P.p‖ : ℂ) ^ 2 * (‖ringComplex R.Q.p‖ : ℂ) ^ 2)⁻¹ * ((v : ℂ) ^ s * besselRemainder R.crossCoeff ((‖ringComplex R.P.p‖ * ‖ringComplex R.Q.p‖) * v) / (v : ℂ) ^ 3)) (Set.Ioi 0) :=
    J1.add J2
  have j3 : IntegrableOn (fun v : ℝ =>
        2 * ((‖ringComplex R.P.p‖ : ℂ) ^ 2 * (‖ringComplex R.Q.p‖ : ℂ) ^ 2)⁻¹ * ((v : ℂ) ^ s * besselRemainder R.shiftCoeff ((‖ringComplex R.P.p‖ * ‖ringComplex R.Q.p‖) * v) / (v : ℂ) ^ 3) +
        2 * ringComplex (symbol R.P.p R.Q.p) * ((‖ringComplex R.P.p‖ : ℂ) ^ 2 * (‖ringComplex R.Q.p‖ : ℂ) ^ 2)⁻¹ * ((v : ℂ) ^ s * besselRemainder R.crossCoeff ((‖ringComplex R.P.p‖ * ‖ringComplex R.Q.p‖) * v) / (v : ℂ) ^ 3) +
        2 * (((‖ringComplex R.P.p‖ : ℂ) ^ 2)⁻¹ * (‖ringComplex R.Q.p‖ : ℂ)) * ((v : ℂ) ^ s * besselRemainder R.ulCoeff ((‖ringComplex R.P.p‖ / ‖ringComplex R.Q.p‖) * v) / (v : ℂ) ^ 3)) (Set.Ioi 0) :=
    j2.add J3
  have j4 : IntegrableOn (fun v : ℝ =>
        2 * ((‖ringComplex R.P.p‖ : ℂ) ^ 2 * (‖ringComplex R.Q.p‖ : ℂ) ^ 2)⁻¹ * ((v : ℂ) ^ s * besselRemainder R.shiftCoeff ((‖ringComplex R.P.p‖ * ‖ringComplex R.Q.p‖) * v) / (v : ℂ) ^ 3) +
        2 * ringComplex (symbol R.P.p R.Q.p) * ((‖ringComplex R.P.p‖ : ℂ) ^ 2 * (‖ringComplex R.Q.p‖ : ℂ) ^ 2)⁻¹ * ((v : ℂ) ^ s * besselRemainder R.crossCoeff ((‖ringComplex R.P.p‖ * ‖ringComplex R.Q.p‖) * v) / (v : ℂ) ^ 3) +
        2 * (((‖ringComplex R.P.p‖ : ℂ) ^ 2)⁻¹ * (‖ringComplex R.Q.p‖ : ℂ)) * ((v : ℂ) ^ s * besselRemainder R.ulCoeff ((‖ringComplex R.P.p‖ / ‖ringComplex R.Q.p‖) * v) / (v : ℂ) ^ 3) +
        2 * (((‖ringComplex R.Q.p‖ : ℂ) ^ 2)⁻¹ * (‖ringComplex R.P.p‖ : ℂ)) * ((v : ℂ) ^ s * besselRemainder R.luCoeff ((‖ringComplex R.Q.p‖ / ‖ringComplex R.P.p‖) * v) / (v : ℂ) ^ 3)) (Set.Ioi 0) :=
    j3.add J4
  have j5 : IntegrableOn (fun v : ℝ =>
        2 * ((‖ringComplex R.P.p‖ : ℂ) ^ 2 * (‖ringComplex R.Q.p‖ : ℂ) ^ 2)⁻¹ * ((v : ℂ) ^ s * besselRemainder R.shiftCoeff ((‖ringComplex R.P.p‖ * ‖ringComplex R.Q.p‖) * v) / (v : ℂ) ^ 3) +
        2 * ringComplex (symbol R.P.p R.Q.p) * ((‖ringComplex R.P.p‖ : ℂ) ^ 2 * (‖ringComplex R.Q.p‖ : ℂ) ^ 2)⁻¹ * ((v : ℂ) ^ s * besselRemainder R.crossCoeff ((‖ringComplex R.P.p‖ * ‖ringComplex R.Q.p‖) * v) / (v : ℂ) ^ 3) +
        2 * (((‖ringComplex R.P.p‖ : ℂ) ^ 2)⁻¹ * (‖ringComplex R.Q.p‖ : ℂ)) * ((v : ℂ) ^ s * besselRemainder R.ulCoeff ((‖ringComplex R.P.p‖ / ‖ringComplex R.Q.p‖) * v) / (v : ℂ) ^ 3) +
        2 * (((‖ringComplex R.Q.p‖ : ℂ) ^ 2)⁻¹ * (‖ringComplex R.P.p‖ : ℂ)) * ((v : ℂ) ^ s * besselRemainder R.luCoeff ((‖ringComplex R.Q.p‖ / ‖ringComplex R.P.p‖) * v) / (v : ℂ) ^ 3) +
        (‖ringComplex R.P.p‖ : ℂ) * (‖ringComplex R.Q.p‖ : ℂ) * ((v : ℂ) ^ s * besselRemainder R.mDilateCoeff ((1 / (‖ringComplex R.P.p‖ * ‖ringComplex R.Q.p‖)) * v) / (v : ℂ) ^ 3)) (Set.Ioi 0) :=
    j4.add J5
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul, integral_sub j5 J0, integral_add j4 J5,
    integral_add j3 J4, integral_add j2 J3, integral_add J1 J2, integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_mellin_comp_mul _ s (mul_pos hp hq), integral_mellin_comp_mul _ s (mul_pos hp hq),
    integral_mellin_comp_mul _ s (div_pos hp hq), integral_mellin_comp_mul _ s (div_pos hq hp),
    integral_mellin_comp_mul _ s (one_div_pos.mpr (mul_pos hp hq)),
    integral_besselRemainder _ s hs23 (R.summable_shiftCoeff hs4), integral_besselRemainder _ s hs23 (R.summable_crossCoeff hs4),
    integral_besselRemainder _ s hs23 (R.summable_ulCoeff hs4), integral_besselRemainder _ s hs23 (R.summable_luCoeff hs4),
    integral_besselRemainder _ s hs23 (R.summable_mDilateCoeff hs4), integral_besselRemainder _ s hs23 (summable_sq_coeff hs4)]
  obtain ⟨i1, i2, i3, i4⟩ := R.cpow_identities s
  have hD0 : besselDirichlet (fun h => rationalSourceResidualFourierCoefficient h ^ 2) s = thetaSqDirichlet s := rfl
  rw [hD0, combination]
  linear_combination R.normM * periodArea * besselSqMellin s *
    ((2 * besselDirichlet R.shiftCoeff s + 2 * ringComplex (symbol R.P.p R.Q.p) * besselDirichlet R.crossCoeff s) * i1 +
      2 * besselDirichlet R.ulCoeff s * i2 + 2 * besselDirichlet R.luCoeff s * i3 + besselDirichlet R.mDilateCoeff s * i4)

theorem normM_periodArea_ne_zero : R.normM * periodArea ≠ 0 :=
  mul_ne_zero (mul_ne_zero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) (Nat.cast_ne_zero.mpr Fintype.card_ne_zero))
    (Complex.ofReal_ne_zero.mpr periodAreaReal_pos.ne')

/-- **The composite combination carries the double pole of `(2 + 2(p/q)₃)M(s)D(s)`.** -/
theorem combination_double_pole :
    ∃ Λ : ℂ → ℂ,
      (∀ s : ℂ, 4 < s.re → s.re < 13 / 3 → 0 < s.im → Λ s = besselSqMellin s * R.combination s) ∧
      (∀ s : ℂ, 1 < s.re → s.re < 13 / 3 → 0 < s.im → DifferentiableAt ℂ Λ s) ∧
      (∀ᶠ s in 𝓝[≠] (4 / 3 : ℂ), DifferentiableAt ℂ Λ s) ∧
      Tendsto (fun s => (s - 4 / 3) ^ 2 * Λ s) (𝓝[≠] (4 / 3 : ℂ))
        (𝓝 ((2 + 2 * ringComplex (symbol R.P.p R.Q.p)) *
          (108 * (Real.pi : ℂ) ^ 3 * constantArithmeticResidue ^ 3))) := by
  obtain ⟨Λ, hΛ, hΛd, hΛn, hΛl, -⟩ := thetaSqDirichlet_double_pole
  have hG := R.remainder_remainderData
  have hq := R.normM_periodArea_ne_zero
  set χ := ringComplex (symbol R.P.p R.Q.p)
  refine ⟨fun s => (2 + 2 * χ) * Λ s + (R.normM * periodArea)⁻¹ * hG.pairing s, fun s hs4 hs hi => ?_,
    fun s hs1 hs hi => ?_, ?_, ?_⟩
  · show (2 + 2 * χ) * Λ s + (R.normM * periodArea)⁻¹ * hG.pairing s = _
    rw [hΛ s hs4 hs hi, ← hG.pairing_eq s hs4 hs hi, R.integral_remainder_mul_eisenstein s hs4 hs,
      inv_mul_cancel_left₀ hq]
    ring
  · exact ((hΛd s hs1 hs hi).const_mul _).add ((hG.pairing_differentiableAt s hs1 hs hi).const_mul _)
  · filter_upwards [hΛn, hG.pairing_near_four_thirds.1] with s h1 h2
    exact (h1.const_mul _).add (h2.const_mul _)
  · have h2 := hG.pairing_near_four_thirds.2
    have hsum := (hΛl.const_mul (2 + 2 * χ)).add (h2.const_mul (R.normM * periodArea)⁻¹)
    rw [mul_zero, add_zero] at hsum
    refine hsum.congr' (Eventually.of_forall fun s => ?_)
    ring

end PrimaryPair

end GaloisForLFunctions.OrderSixMetaplecticTheory
