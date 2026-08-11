import GaloisForLFunctions.RHTower.TwoEdgeWindowAutocorrelation

/-!
# Zero-extended Fourier correlations in the CCM aperture

This is the literal analytic input of Lemma 2.3 in Connes--Consani--Moscovici,
*Zeta Spectral Triples* (2025).  Their periodic Fourier modes on `[0,L]` are extended by zero to
the real line.  We compute the convolution correlation from those source functions, rather than
postulating the sine divided-difference and tent--cosine formulas used by the published restricted
Weil matrix.

Positive apertures and legal lags are bundled as subtypes.  Thus the public source theorem is a
closed universal statement: it has no analytic, spectral, simplicity, parity, or RH premise.
-/

open MeasureTheory Set Complex
open scoped ComplexConjugate

noncomputable section

namespace RHTower

/-- A positive logarithmic aperture length. -/
abbrev CCMPositiveAperture := {L : ℝ // 0 < L}

/-- A nonnegative lag lying inside a positive aperture. -/
abbrev CCMApertureLag (L : CCMPositiveAperture) := Set.Icc (0 : ℝ) (L : ℝ)

/-- The normalized periodic Fourier mode on `[0,L]`, extended by zero to `ℝ`. -/
def ccmZeroExtendedFourierMode (L : CCMPositiveAperture) (n : ℤ) (x : ℝ) : ℂ :=
  (Icc (0 : ℝ) (L : ℝ)).indicator
    (fun t => ((Real.sqrt (L : ℝ))⁻¹ : ℂ) *
      Complex.exp
        (2 * (Real.pi : ℂ) * I * (n : ℂ) * (t : ℂ) / (L : ℂ))) x

/-- The source convolution `(U_m^* * U_n)(y)` of the zero-extended modes. -/
def ccmZeroExtendedModeCorrelation
    (L : CCMPositiveAperture) (m n : ℤ) (y : ℝ) : ℂ :=
  ∫ x : ℝ,
    conj (ccmZeroExtendedFourierMode L m (x - y)) *
      ccmZeroExtendedFourierMode L n x

/-- Paper equation (2.5): the even Hermitian correlation, expressed at positive lag. -/
def ccmZeroExtendedEvenCorrelation
    (L : CCMPositiveAperture) (m n : ℤ) (y : ℝ) : ℂ :=
  ccmZeroExtendedModeCorrelation L m n y +
    conj (ccmZeroExtendedModeCorrelation L n m y)

private theorem inverse_sqrt_mul_self (L : CCMPositiveAperture) :
    (Real.sqrt (L : ℝ))⁻¹ * (Real.sqrt (L : ℝ))⁻¹ = (L : ℝ)⁻¹ := by
  rw [← mul_inv, Real.mul_self_sqrt L.property.le]

private theorem correlation_integrand_eq_indicator
    (L : CCMPositiveAperture) (y : CCMApertureLag L) (m n : ℤ) :
    (fun x : ℝ =>
      conj (ccmZeroExtendedFourierMode L m (x - (y : ℝ))) *
        ccmZeroExtendedFourierMode L n x) =
      (Icc (y : ℝ) (L : ℝ)).indicator
        (fun x => (1 / (L : ℂ)) *
          Complex.exp
            (2 * (Real.pi : ℂ) * I *
              ((m : ℂ) * (y : ℂ) + ((n : ℂ) - (m : ℂ)) * (x : ℂ)) /
                (L : ℂ))) := by
  funext x
  by_cases hx : x ∈ Icc (y : ℝ) (L : ℝ)
  · have hxn : x ∈ Icc (0 : ℝ) (L : ℝ) := ⟨y.property.1.trans hx.1, hx.2⟩
    have hxm : x - (y : ℝ) ∈ Icc (0 : ℝ) (L : ℝ) := by
      constructor <;> linarith [hx.1, hx.2, y.property.1]
    rw [Set.indicator_of_mem hx]
    simp only [ccmZeroExtendedFourierMode, Set.indicator_of_mem hxn,
      Set.indicator_of_mem hxm, map_mul, Complex.conj_ofReal, map_inv₀]
    rw [← Complex.exp_conj]
    rw [show
        ((Real.sqrt (L : ℝ))⁻¹ : ℂ) *
              Complex.exp
                (conj
                  (2 * (Real.pi : ℂ) * I * (m : ℂ) * ((x - (y : ℝ) : ℝ) : ℂ) /
                    (L : ℂ))) *
            (((Real.sqrt (L : ℝ))⁻¹ : ℂ) *
              Complex.exp
                (2 * (Real.pi : ℂ) * I * (n : ℂ) * (x : ℂ) / (L : ℂ))) =
          (((Real.sqrt (L : ℝ))⁻¹ : ℂ) *
              ((Real.sqrt (L : ℝ))⁻¹ : ℂ)) *
            (Complex.exp
                (conj
                  (2 * (Real.pi : ℂ) * I * (m : ℂ) * ((x - (y : ℝ) : ℝ) : ℂ) /
                    (L : ℂ))) *
              Complex.exp
                (2 * (Real.pi : ℂ) * I * (n : ℂ) * (x : ℂ) / (L : ℂ))) by
        ring]
    rw [← Complex.exp_add]
    have hsR := inverse_sqrt_mul_self L
    have hsC :
        ((Real.sqrt (L : ℝ) : ℂ)⁻¹) * ((Real.sqrt (L : ℝ) : ℂ)⁻¹) =
          ((L : ℂ)⁻¹) := by
      exact_mod_cast hsR
    rw [hsC]
    congr 2
    field_simp [ne_of_gt L.property]
    ring
  · rw [Set.indicator_of_notMem hx]
    by_cases hxn : x ∈ Icc (0 : ℝ) (L : ℝ)
    · have hxy : x < (y : ℝ) := by
        by_contra hnot
        exact hx ⟨le_of_not_gt hnot, hxn.2⟩
      have hxm : x - (y : ℝ) ∉ Icc (0 : ℝ) (L : ℝ) := by
        intro h
        linarith [h.1]
      simp [ccmZeroExtendedFourierMode, Set.indicator_of_mem hxn,
        Set.indicator_of_notMem hxm]
    · simp [ccmZeroExtendedFourierMode, Set.indicator_of_notMem hxn]

private theorem correlation_integral_normal_form
    (L : CCMPositiveAperture) (y : CCMApertureLag L) (m n : ℤ) :
    ccmZeroExtendedModeCorrelation L m n (y : ℝ) =
      (1 / (L : ℂ)) *
        Complex.exp
          (2 * (Real.pi : ℂ) * I * (m : ℂ) * (y : ℂ) / (L : ℂ)) *
        ∫ x : ℝ,
          (Icc (y : ℝ) (L : ℝ)).indicator (fun _ => (1 : ℂ)) x *
            Complex.exp
              ((2 * (Real.pi : ℂ) * I * ((n : ℂ) - (m : ℂ)) / (L : ℂ)) *
                (x : ℂ)) := by
  rw [ccmZeroExtendedModeCorrelation, correlation_integrand_eq_indicator L y m n]
  let c : ℂ :=
    (1 / (L : ℂ)) *
      Complex.exp
        (2 * (Real.pi : ℂ) * I * (m : ℂ) * (y : ℂ) / (L : ℂ))
  let w : ℂ := 2 * (Real.pi : ℂ) * I * ((n : ℂ) - (m : ℂ)) / (L : ℂ)
  have hpoint :
      (Icc (y : ℝ) (L : ℝ)).indicator
          (fun x => (1 / (L : ℂ)) *
            Complex.exp
              (2 * (Real.pi : ℂ) * I *
                ((m : ℂ) * (y : ℂ) + ((n : ℂ) - (m : ℂ)) * (x : ℂ)) /
                  (L : ℂ))) =
        fun x => c *
          ((Icc (y : ℝ) (L : ℝ)).indicator (fun _ => (1 : ℂ)) x *
            Complex.exp (w * (x : ℂ))) := by
    funext x
    by_cases hx : x ∈ Icc (y : ℝ) (L : ℝ)
    · simp only [Set.indicator_of_mem hx, one_mul, c, w]
      rw [show
          (1 / (L : ℂ)) *
                Complex.exp
                  (2 * (Real.pi : ℂ) * I * (m : ℂ) * (y : ℂ) / (L : ℂ)) *
              Complex.exp
                ((2 * (Real.pi : ℂ) * I * ((n : ℂ) - (m : ℂ)) / (L : ℂ)) *
                  (x : ℂ)) =
            (1 / (L : ℂ)) *
              (Complex.exp
                  (2 * (Real.pi : ℂ) * I * (m : ℂ) * (y : ℂ) / (L : ℂ)) *
                Complex.exp
                  ((2 * (Real.pi : ℂ) * I * ((n : ℂ) - (m : ℂ)) / (L : ℂ)) *
                    (x : ℂ))) by
          ring]
      rw [← Complex.exp_add]
      congr 2
      field_simp [ne_of_gt L.property]
    · simp [Set.indicator_of_notMem hx]
  rw [hpoint, integral_const_mul]

private theorem nonzero_mode_frequency
    (L : CCMPositiveAperture) {m n : ℤ} (hmn : m ≠ n) :
    2 * (Real.pi : ℂ) * I * ((n : ℂ) - (m : ℂ)) / (L : ℂ) ≠ 0 := by
  have hnm : n - m ≠ 0 := sub_ne_zero.mpr (Ne.symm hmn)
  exact div_ne_zero
    (mul_ne_zero
      (mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) I_ne_zero)
      (by exact_mod_cast hnm))
    (by exact_mod_cast ne_of_gt L.property)

private theorem exp_mode_period (k : ℤ) :
    Complex.exp (2 * (Real.pi : ℂ) * I * (k : ℂ)) = 1 := by
  convert Complex.exp_int_mul_two_pi_mul_I k using 1 <;> ring

/-- CCM equation (2.7), derived from the literal zero-extended modes. -/
theorem ccmZeroExtendedModeCorrelation_eq_of_ne
    (L : CCMPositiveAperture) (y : CCMApertureLag L) {m n : ℤ} (hmn : m ≠ n) :
    ccmZeroExtendedModeCorrelation L m n (y : ℝ) =
      (Complex.exp
          (2 * (Real.pi : ℂ) * I * (m : ℂ) * (y : ℂ) / (L : ℂ)) -
        Complex.exp
          (2 * (Real.pi : ℂ) * I * (n : ℂ) * (y : ℂ) / (L : ℂ))) /
        (2 * (Real.pi : ℂ) * I * ((n : ℂ) - (m : ℂ))) := by
  rw [correlation_integral_normal_form]
  let w : ℂ := 2 * (Real.pi : ℂ) * I * ((n : ℂ) - (m : ℂ)) / (L : ℂ)
  have hw : w ≠ 0 := nonzero_mode_frequency L hmn
  rw [integral_indicator_Icc_mul_exp y.property.2 hw]
  have hperiod : Complex.exp (w * (L : ℂ)) = 1 := by
    rw [show w * (L : ℂ) = 2 * (Real.pi : ℂ) * I * ((n - m : ℤ) : ℂ) by
      dsimp [w]
      field_simp [ne_of_gt L.property]
      push_cast
      ring]
    exact exp_mode_period (n - m)
  have hsplit :
      Complex.exp
          (2 * (Real.pi : ℂ) * I * (m : ℂ) * (y : ℂ) / (L : ℂ)) *
        Complex.exp (w * (y : ℂ)) =
      Complex.exp
          (2 * (Real.pi : ℂ) * I * (n : ℂ) * (y : ℂ) / (L : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    dsimp [w]
    field_simp [ne_of_gt L.property]
    ring
  rw [hperiod]
  have hD : 2 * (Real.pi : ℂ) * I * ((n : ℂ) - (m : ℂ)) ≠ 0 := by
    have hnm : (n : ℂ) - (m : ℂ) ≠ 0 := by
      exact_mod_cast sub_ne_zero.mpr (Ne.symm hmn)
    exact mul_ne_zero
      (mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) I_ne_zero)
      hnm
  calc
    (1 / (L : ℂ)) *
          Complex.exp
            (2 * (Real.pi : ℂ) * I * (m : ℂ) * (y : ℂ) / (L : ℂ)) *
          ((1 - Complex.exp (w * (y : ℂ))) / w) =
        (Complex.exp
              (2 * (Real.pi : ℂ) * I * (m : ℂ) * (y : ℂ) / (L : ℂ)) *
            (1 - Complex.exp (w * (y : ℂ)))) /
          (2 * (Real.pi : ℂ) * I * ((n : ℂ) - (m : ℂ))) := by
      dsimp [w]
      field_simp [ne_of_gt L.property, hD]
    _ = _ := by
      rw [mul_sub, mul_one, hsplit]

/-- CCM equation (2.10) before taking the even part, including exact aperture normalization. -/
theorem ccmZeroExtendedModeCorrelation_eq_self
    (L : CCMPositiveAperture) (y : CCMApertureLag L) (n : ℤ) :
    ccmZeroExtendedModeCorrelation L n n (y : ℝ) =
      (1 - (y : ℂ) / (L : ℂ)) *
        Complex.exp
          (2 * (Real.pi : ℂ) * I * (n : ℂ) * (y : ℂ) / (L : ℂ)) := by
  rw [correlation_integral_normal_form]
  simp only [sub_self, Complex.ofReal_zero, mul_zero, zero_div, zero_mul,
    Complex.exp_zero, mul_one]
  rw [integral_indicator_const (1 : ℂ) measurableSet_Icc, Complex.real_smul, mul_one,
    MeasureTheory.measureReal_def, Real.volume_Icc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr y.property.2)]
  push_cast
  field_simp [ne_of_gt L.property]

/-- Literal source formula of CCM Lemma 2.3, covering diagonal and off-diagonal modes in one
closed theorem. -/
theorem ccmZeroExtendedEvenCorrelation_eq_published
    (L : CCMPositiveAperture) (y : CCMApertureLag L) (m n : ℤ) :
    ccmZeroExtendedEvenCorrelation L m n (y : ℝ) =
      if m = n then
        2 * (1 - (y : ℂ) / (L : ℂ)) *
          Real.cos (2 * Real.pi * (n : ℝ) * (y : ℝ) / (L : ℝ))
      else
        ((Real.sin (2 * Real.pi * (m : ℝ) * (y : ℝ) / (L : ℝ)) -
            Real.sin (2 * Real.pi * (n : ℝ) * (y : ℝ) / (L : ℝ))) : ℂ) /
          (Real.pi * ((n : ℝ) - (m : ℝ))) := by
  by_cases hmn : m = n
  · subst m
    rw [if_pos rfl, ccmZeroExtendedEvenCorrelation,
      ccmZeroExtendedModeCorrelation_eq_self]
    simp only [map_mul, map_sub, map_one, map_div₀, Complex.conj_ofReal]
    have harg :
        2 * (Real.pi : ℂ) * I * (n : ℂ) * (y : ℂ) / (L : ℂ) =
          ((2 * Real.pi * (n : ℝ) * (y : ℝ) / (L : ℝ) : ℝ) : ℂ) * I := by
      push_cast
      field_simp [ne_of_gt L.property]
    rw [harg]
    rw [Complex.exp_ofReal_mul_I]
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  · rw [if_neg hmn, ccmZeroExtendedEvenCorrelation,
      ccmZeroExtendedModeCorrelation_eq_of_ne L y hmn,
      ccmZeroExtendedModeCorrelation_eq_of_ne L y (Ne.symm hmn)]
    have hmarg :
        2 * (Real.pi : ℂ) * I * (m : ℂ) * (y : ℂ) / (L : ℂ) =
          ((2 * Real.pi * (m : ℝ) * (y : ℝ) / (L : ℝ) : ℝ) : ℂ) * I := by
      push_cast
      field_simp [ne_of_gt L.property]
    have hnarg :
        2 * (Real.pi : ℂ) * I * (n : ℂ) * (y : ℂ) / (L : ℂ) =
          ((2 * Real.pi * (n : ℝ) * (y : ℝ) / (L : ℝ) : ℝ) : ℂ) * I := by
      push_cast
      field_simp [ne_of_gt L.property]
    rw [hmarg, hnarg]
    rw [Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I]
    simp only [map_div₀, map_sub, map_add, map_mul, map_ofNat, Complex.conj_ofReal,
      Complex.conj_I, map_intCast, mul_neg]
    have hden : (Real.pi : ℂ) * (((n : ℝ) - (m : ℝ) : ℝ) : ℂ) ≠ 0 := by
      exact mul_ne_zero (by exact_mod_cast Real.pi_ne_zero)
        (by exact_mod_cast sub_ne_zero.mpr (Ne.symm hmn))
    have hnmC : (n : ℂ) - (m : ℂ) ≠ 0 := by
      exact_mod_cast sub_ne_zero.mpr (Ne.symm hmn)
    have hmnC : (m : ℂ) - (n : ℂ) ≠ 0 := by
      exact_mod_cast sub_ne_zero.mpr hmn
    field_simp [hden, hnmC, hmnC]
    push_cast
    ring

end RHTower
