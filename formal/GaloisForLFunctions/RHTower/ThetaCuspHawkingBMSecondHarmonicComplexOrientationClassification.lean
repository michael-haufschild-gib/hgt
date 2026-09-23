import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSecondHarmonicReflectionPositiveConeNoGo

/-!
# Complex-orientation classification for reflected BM second-harmonic currents

The canonical current on a functional-equation reflection pair has a one-dimensional complex
cancellation space.  Its relative coefficient is forced to be the negative quotient of the two
complementary exponents.  Opposite nonzero exponent imaginary parts and simultaneous positive real
parts force this ratio off the real axis on every Xi fibre.

Thus signed real source incidence is no stronger than positive incidence: it cannot cancel except
at zero.  Complex cancellation exists for one ordered reflection pair, but reversal inverts its
ratio, and no fixed ordered complex incidence cancels both orientations nontrivially.  Any surviving
augmented Peierls source law must therefore carry divisor-dependent, reflection-covariant complex
orientation rather than a Hermitian or fixed real/sign-indefinite weight.

`[NEW] [CLASSIFICATION] [NO-GO] [POSITIVE SURVIVOR] [PAPER-PROVED] [LEAN-PROVED]`
-/

open Complex Real Set

namespace RHTower

noncomputable section

/-- Complementary exponent on the chosen member of a reflected Xi pair. -/
def d4BMXiPlusPlusComplementaryExponent
    (n : ℕ) (q : XiZeroCopy) : ℂ :=
  d4BMPlusPlusComplementaryFrobeniusExponent n
    (d4BMXiMixedHorizonAngularMomentum q)

/-- The unique relative coefficient which cancels the ordered reflected exponent pair. -/
def d4BMXiReflectionComplexCancellationRatio
    (n : ℕ) (q : XiZeroCopy) : ℂ :=
  -d4BMXiPlusPlusComplementaryExponent n q /
    d4BMXiPlusPlusComplementaryExponent n (xiZeroCopyReflectEquiv q)

/-- Arbitrary complex-weighted canonical current on an ordered reflected Xi pair. -/
def d4BMXiReflectionComplexWeightedRegularComplementaryCurrent
    (n : ℕ) (q : XiZeroCopy) (a b : ℂ) : ℂ :=
  a * d4BMSecondHarmonicRegularComplementaryPolarizedCurrentValue n
      (d4BMXiMixedHorizonAngularMomentum q) (1 / 2) +
    b * d4BMSecondHarmonicRegularComplementaryPolarizedCurrentValue n
      (d4BMXiMixedHorizonAngularMomentum (xiZeroCopyReflectEquiv q)) (1 / 2)

/-- The Xi height is exactly the imaginary part of its BM complementary exponent. -/
theorem d4BMXiPlusPlusComplementaryExponent_im
    (n : ℕ) (q : XiZeroCopy) :
    (d4BMXiPlusPlusComplementaryExponent n q).im = (q.1 : ℂ).im := by
  rw [d4BMXiPlusPlusComplementaryExponent,
    d4BMPlusPlusComplementaryFrobeniusExponent_eq]
  simp [Complex.mul_im, d4BMXiMixedHorizonAngularMomentum_re]
  ring

/-- Reflected complementary exponents have opposite nonzero imaginary parts. -/
theorem d4BMXiPlusPlusComplementaryExponent_reflect_im
    (n : ℕ) (q : XiZeroCopy) :
    (d4BMXiPlusPlusComplementaryExponent n (xiZeroCopyReflectEquiv q)).im =
      -(d4BMXiPlusPlusComplementaryExponent n q).im := by
  have h := congrArg Complex.im
    (d4BMXi_reflectionPair_complementaryExponent_add n q)
  rw [← d4BMXiPlusPlusComplementaryExponent,
    ← d4BMXiPlusPlusComplementaryExponent] at h
  norm_num at h
  linarith

/-- Every Xi complementary exponent is nonzero. -/
theorem d4BMXiPlusPlusComplementaryExponent_ne_zero
    (n : ℕ) (q : XiZeroCopy) :
    d4BMXiPlusPlusComplementaryExponent n q ≠ 0 := by
  intro h
  have hp := d4BMXiPlusPlusComplementaryFrobeniusExponent_re_pos n q
  rw [← d4BMXiPlusPlusComplementaryExponent, h] at hp
  norm_num at hp

/-- Exact complex cancellation hyperplane: one freely chosen coefficient, one forced ratio. -/
theorem d4BMXiReflectionComplexWeightedRegularComplementaryCurrent_eq_zero_iff
    (n : ℕ) (q : XiZeroCopy) (a b : ℂ) :
    d4BMXiReflectionComplexWeightedRegularComplementaryCurrent n q a b = 0 ↔
      b = a * d4BMXiReflectionComplexCancellationRatio n q := by
  have hz0 : (0 : ℝ) < 1 / 2 := by norm_num
  have hz1 : (1 / 2 : ℝ) < 1 := by norm_num
  rw [d4BMXiReflectionComplexWeightedRegularComplementaryCurrent,
    d4BMSecondHarmonicRegularComplementaryPolarizedCurrentValue_eq_negExponent n
      (d4BMXiMixedHorizonAngularMomentum q)
      (d4BMXiMixedHorizonAngularMomentum_re_ne_zero q) hz0 hz1,
    d4BMSecondHarmonicRegularComplementaryPolarizedCurrentValue_eq_negExponent n
      (d4BMXiMixedHorizonAngularMomentum (xiZeroCopyReflectEquiv q))
      (d4BMXiMixedHorizonAngularMomentum_re_ne_zero (xiZeroCopyReflectEquiv q)) hz0 hz1]
  change a * -d4BMXiPlusPlusComplementaryExponent n q +
      b * -d4BMXiPlusPlusComplementaryExponent n (xiZeroCopyReflectEquiv q) = 0 ↔ _
  rw [d4BMXiReflectionComplexCancellationRatio]
  have hne := d4BMXiPlusPlusComplementaryExponent_ne_zero n
    (xiZeroCopyReflectEquiv q)
  constructor
  · intro h
    calc
      b = (-a * d4BMXiPlusPlusComplementaryExponent n q) /
          d4BMXiPlusPlusComplementaryExponent n (xiZeroCopyReflectEquiv q) := by
            apply (eq_div_iff hne).2
            linear_combination -h
      _ = a * (-d4BMXiPlusPlusComplementaryExponent n q /
          d4BMXiPlusPlusComplementaryExponent n (xiZeroCopyReflectEquiv q)) := by ring
  · intro h
    rw [h]
    field_simp
    ring

/-- Cancellation ratio is genuinely complex on every Xi fibre. -/
theorem d4BMXiReflectionComplexCancellationRatio_im_ne_zero
    (n : ℕ) (q : XiZeroCopy) :
    (d4BMXiReflectionComplexCancellationRatio n q).im ≠ 0 := by
  let lam := d4BMXiPlusPlusComplementaryExponent n q
  let mu := d4BMXiPlusPlusComplementaryExponent n (xiZeroCopyReflectEquiv q)
  let r := d4BMXiReflectionComplexCancellationRatio n q
  have hmu : mu ≠ 0 := d4BMXiPlusPlusComplementaryExponent_ne_zero n
    (xiZeroCopyReflectEquiv q)
  have hrmul : r * mu = -lam := by
    dsimp [r, d4BMXiReflectionComplexCancellationRatio]
    exact div_mul_cancel₀ (-lam) hmu
  have himmu : mu.im = -lam.im := by
    dsimp [lam, mu]
    exact d4BMXiPlusPlusComplementaryExponent_reflect_im n q
  have himlam : lam.im ≠ 0 := by
    dsimp [lam]
    rw [d4BMXiPlusPlusComplementaryExponent_im]
    exact xi_divisor_support_im_ne_zero q.1
  intro hrim
  have him := congrArg Complex.im hrmul
  simp only [Complex.mul_im, Complex.neg_im] at him
  rw [hrim, zero_mul, add_zero, himmu] at him
  have hrre : r.re = 1 := by
    apply (mul_left_cancel₀ himlam)
    nlinarith
  have hrone : r = 1 := by
    apply Complex.ext
    · simpa using hrre
    · simpa using hrim
  rw [hrone, one_mul] at hrmul
  have hplam := d4BMXiPlusPlusComplementaryFrobeniusExponent_re_pos n q
  have hpmu := d4BMXiPlusPlusComplementaryFrobeniusExponent_re_pos n
    (xiZeroCopyReflectEquiv q)
  rw [← d4BMXiPlusPlusComplementaryExponent] at hplam hpmu
  have hre := congrArg Complex.re hrmul
  simp only [Complex.neg_re] at hre
  linarith

/-- Even arbitrary signed real source weights cancel only trivially. -/
theorem d4BMXiReflectionRealWeightedRegularComplementaryCurrent_eq_zero_iff
    (n : ℕ) (q : XiZeroCopy) (a b : ℝ) :
    d4BMXiReflectionComplexWeightedRegularComplementaryCurrent n q a b = 0 ↔
      a = 0 ∧ b = 0 := by
  rw [d4BMXiReflectionComplexWeightedRegularComplementaryCurrent_eq_zero_iff]
  constructor
  · intro h
    have him := congrArg Complex.im h
    simp only [Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, zero_mul, add_zero] at him
    have ha : a = 0 := by
      by_contra ha
      have hratiozero := (mul_eq_zero.mp him.symm).resolve_left ha
      exact d4BMXiReflectionComplexCancellationRatio_im_ne_zero n q hratiozero
    subst a
    simp at h
    exact ⟨rfl, h⟩
  · rintro ⟨rfl, rfl⟩
    simp

/-- A nontrivial complex orientation does cancel an ordered reflected pair. -/
theorem d4BMXiReflectionComplexCancellationRatio_current_eq_zero
    (n : ℕ) (q : XiZeroCopy) :
    d4BMXiReflectionComplexWeightedRegularComplementaryCurrent n q 1
      (d4BMXiReflectionComplexCancellationRatio n q) = 0 := by
  rw [d4BMXiReflectionComplexWeightedRegularComplementaryCurrent_eq_zero_iff]
  simp

/-- Reversing reflection order inverts the complex cancellation orientation. -/
theorem d4BMXiReflectionComplexCancellationRatio_reflect
    (n : ℕ) (q : XiZeroCopy) :
    d4BMXiReflectionComplexCancellationRatio n (xiZeroCopyReflectEquiv q) =
      (d4BMXiReflectionComplexCancellationRatio n q)⁻¹ := by
  rw [d4BMXiReflectionComplexCancellationRatio,
    d4BMXiReflectionComplexCancellationRatio,
    xiZeroCopyReflectEquiv_apply_apply]
  have hq := d4BMXiPlusPlusComplementaryExponent_ne_zero n q
  have hr := d4BMXiPlusPlusComplementaryExponent_ne_zero n
    (xiZeroCopyReflectEquiv q)
  field_simp

/-- No fixed ordered complex incidence can cancel both orientations of a reflection orbit. -/
theorem d4BMXiReflectionComplexWeightedCurrent_bioriented_eq_zero_iff
    (n : ℕ) (q : XiZeroCopy) (a b : ℂ) :
    (d4BMXiReflectionComplexWeightedRegularComplementaryCurrent n q a b = 0 ∧
      d4BMXiReflectionComplexWeightedRegularComplementaryCurrent n
        (xiZeroCopyReflectEquiv q) a b = 0) ↔
      a = 0 ∧ b = 0 := by
  rw [d4BMXiReflectionComplexWeightedRegularComplementaryCurrent_eq_zero_iff,
    d4BMXiReflectionComplexWeightedRegularComplementaryCurrent_eq_zero_iff]
  rw [d4BMXiReflectionComplexCancellationRatio_reflect]
  constructor
  · rintro ⟨h, href⟩
    by_cases ha : a = 0
    · subst a
      simp at h
      exact ⟨rfl, h⟩
    · have hr : d4BMXiReflectionComplexCancellationRatio n q =
          (d4BMXiReflectionComplexCancellationRatio n q)⁻¹ := by
        apply (mul_left_cancel₀ ha)
        rw [← h, ← href]
      have hsquare : (d4BMXiReflectionComplexCancellationRatio n q) ^ (2 : ℕ) = 1 := by
        have hrne : d4BMXiReflectionComplexCancellationRatio n q ≠ 0 := by
          intro hz
          have := d4BMXiReflectionComplexCancellationRatio_im_ne_zero n q
          rw [hz] at this
          exact this rfl
        rw [pow_two]
        calc
          d4BMXiReflectionComplexCancellationRatio n q *
              d4BMXiReflectionComplexCancellationRatio n q =
            (d4BMXiReflectionComplexCancellationRatio n q)⁻¹ *
              d4BMXiReflectionComplexCancellationRatio n q :=
                congrArg (fun z => z * d4BMXiReflectionComplexCancellationRatio n q) hr
          _ = 1 := inv_mul_cancel₀ hrne
      have hor := (sq_eq_one_iff).mp hsquare
      rcases hor with hrone | hrneg
      · have him := d4BMXiReflectionComplexCancellationRatio_im_ne_zero n q
        norm_num [hrone] at him
      · have him := d4BMXiReflectionComplexCancellationRatio_im_ne_zero n q
        norm_num [hrneg] at him
  · rintro ⟨rfl, rfl⟩
    simp

end

end RHTower
