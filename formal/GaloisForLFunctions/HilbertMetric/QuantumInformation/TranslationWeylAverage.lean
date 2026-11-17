import GaloisForLFunctions.HilbertMetric.QuantumInformation.TranslationWeakAverage
import GaloisForLFunctions.HTGeometry.LpDiagonalMultiplier
import GaloisForLFunctions.RHTower.Sieve.PhaseIntegral
import Mathlib.Analysis.Complex.Circle

/-!
# Fourier filtering of real-coordinate Weyl observables

Translation and modulation on counting-measure square-summable real
coordinates satisfy the exact Weyl cocycle. Weak translation averaging
multiplies each Weyl word by its unit-interval Fourier integral. On integer
frequencies this retains precisely the translation terms of a finite Weyl
polynomial. All coefficient integrability is proved on the actual interval.
-/

noncomputable section
open MeasureTheory
namespace GaloisForLFunctions.HilbertMetric.ShiftAverage

theorem shift_zero (v : Space) : shift 0 v = v := by
  apply lp.ext
  funext y
  change v (0 + y) = v y
  rw [zero_add]

/-- Counting-measure translations form an exact real-parameter group. -/
theorem shift_add (s t : ℝ) (v : Space) : shift s (shift t v) = shift (s + t) v := by
  apply lp.ext
  funext y
  change v (t + (s + y)) = v ((s + t) + y)
  rw [show t + (s + y) = (s + t) + y by ring]

/-- Translation as a bounded operator on the full nonseparable Hilbert space. -/
def translation (t : ℝ) : Space →L[ℂ] Space := (shift t).toContinuousLinearMap

/-- Unit-modulus multiplication by a real Fourier character. -/
def modulation (ω : ℝ) : Space →L[ℂ] Space :=
  lpDiagonalCLM (fun y : ℝ => (Circle.exp (ω * y) : ℂ)) (by norm_num : (0 : ℝ) ≤ 1)
    (fun y => (Circle.norm_coe (Circle.exp (ω * y))).le)

theorem modulation_apply (ω : ℝ) (v : Space) (y : ℝ) :
    modulation ω v y = (Circle.exp (ω * y) : ℂ) * v y := rfl

/-- Fourier modulation preserves the full counting-measure Hilbert norm. -/
theorem norm_modulation (ω : ℝ) (v : Space) : ‖modulation ω v‖ = ‖v‖ := by
  rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
  simp only [modulation_apply, norm_mul, Circle.norm_coe, one_mul]

/-- Ordered Weyl observable on the real counting-measure coordinates. -/
def weylWord (a ω : ℝ) : Space →L[ℂ] Space := modulation ω * translation a

theorem weylWord_apply (a ω : ℝ) (v : Space) (y : ℝ) :
    weylWord a ω v y = (Circle.exp (ω * y) : ℂ) * v (a + y) := rfl

theorem norm_weylWord (a ω : ℝ) (v : Space) : ‖weylWord a ω v‖ = ‖v‖ := by
  change ‖modulation ω (shift a v)‖ = ‖v‖
  rw [norm_modulation, norm_shift]

/-- Weyl multiplication records the exact translation-modulation cocycle. -/
theorem weylWord_mul (a b ω ν : ℝ) :
    weylWord a ω * weylWord b ν =
      (Circle.exp (ν * a) : ℂ) • weylWord (a + b) (ω + ν) := by
  apply ContinuousLinearMap.ext
  intro v
  apply lp.ext
  funext y
  change (Circle.exp (ω * y) : ℂ) *
      ((Circle.exp (ν * (a + y)) : ℂ) * v (b + (a + y))) =
    (Circle.exp (ν * a) : ℂ) *
      ((Circle.exp ((ω + ν) * y) : ℂ) * v ((a + b) + y))
  rw [show b + (a + y) = (a + b) + y by ring]
  simp only [← mul_assoc, ← Circle.coe_mul, ← Circle.exp_add]
  congr 2
  ring

/-- The real-coordinate Weyl commutator is the scalar phase of the signed parameter area. -/
theorem weylWord_commutation (a b ω ν : ℝ) :
    weylWord a ω * weylWord b ν =
      (Circle.exp (ν * a - ω * b) : ℂ) • (weylWord b ν * weylWord a ω) := by
  rw [weylWord_mul, weylWord_mul, smul_smul, ← Circle.coe_mul, ← Circle.exp_add]
  rw [show ν * a - ω * b + ω * b = ν * a by ring, add_comm b a, add_comm ν ω]

/-- Actual unitary conjugation by the counting-measure translations. -/
def translatedObservable (t : ℝ) (A : Space →L[ℂ] Space) : Space →L[ℂ] Space :=
  translation (-t) * A * translation t

/-- The weak coefficients are exactly coefficients of the conjugated observable. -/
theorem translatedObservable_inner (t : ℝ) (A : Space →L[ℂ] Space) (u v : Space) :
    inner ℂ (shift t u) (A (shift t v)) = inner ℂ u (translatedObservable t A v) := by
  have h := (shift (-t)).inner_map_map (shift t u) (A (shift t v))
  rw [shift_add, neg_add_cancel, shift_zero] at h
  exact h.symm

/-- Conjugation of a Weyl observable has a single exact Fourier frequency. -/
theorem translatedObservable_weylWord (t a ω : ℝ) :
    translatedObservable t (weylWord a ω) =
      (Circle.exp (-ω * t) : ℂ) • weylWord a ω := by
  apply ContinuousLinearMap.ext
  intro v
  apply lp.ext
  funext y
  change (Circle.exp (ω * (-t + y)) : ℂ) * v (t + (a + (-t + y))) =
    (Circle.exp (-ω * t) : ℂ) * ((Circle.exp (ω * y) : ℂ) * v (a + y))
  rw [show t + (a + (-t + y)) = a + y by ring,
    show ω * (-t + y) = -ω * t + ω * y by ring,
    Circle.exp_add, Circle.coe_mul, mul_assoc]

/-- Every weak Weyl coefficient reduces to a scalar Fourier character times a fixed pairing. -/
theorem weylWord_shift_coefficient (t a ω : ℝ) (u v : Space) :
    inner ℂ (shift t u) (weylWord a ω (shift t v)) =
      (Circle.exp (-ω * t) : ℂ) * inner ℂ u (weylWord a ω v) := by
  rw [translatedObservable_inner, translatedObservable_weylWord]
  simp only [smul_apply, inner_smul_right]

/-- Zero-frequency Weyl words are exactly translations and survive averaging unchanged. -/
theorem weylWord_zero_frequency (a : ℝ) : weylWord a 0 = translation a := by
  apply ContinuousLinearMap.ext
  intro v
  apply lp.ext
  funext y
  change (Circle.exp (0 * y) : ℂ) * v (a + y) = v (a + y)
  simp only [zero_mul, Circle.exp_zero, Circle.coe_one, one_mul]

/-- The actual unit-interval Fourier average of a modulation frequency. -/
def phaseAverage (ω : ℝ) : ℂ :=
  ∫ t : ℝ in Set.Ioc 0 1, (Circle.exp (-ω * t) : ℂ)

/-- Averaging a Weyl observable returns its exact scalar Fourier attenuation. -/
theorem interval_average_weylWord (a ω : ℝ) (u v : Space) :
    (∫ t : ℝ in Set.Ioc 0 1, inner ℂ (shift t u) (weylWord a ω (shift t v))) =
      phaseAverage ω * inner ℂ u (weylWord a ω v) := by
  simp_rw [weylWord_shift_coefficient]
  rw [integral_mul_const]
  rfl

/-- Unit-interval attenuation never increases a Weyl coefficient's magnitude. -/
theorem norm_phaseAverage_le_one (ω : ℝ) : ‖phaseAverage ω‖ ≤ 1 := by
  unfold phaseAverage
  calc
    _ ≤ ∫ t : ℝ in Set.Ioc 0 1, ‖(Circle.exp (-ω * t) : ℂ)‖ :=
      norm_integral_le_integral_norm _
    _ = 1 := by simp only [Circle.norm_coe]; simp

/-- The retained zero-frequency component has attenuation exactly one. -/
theorem phaseAverage_zero : phaseAverage 0 = 1 := by
  simp [phaseAverage]

/-- Every translation observable survives the normalized weak averaging operation. -/
theorem interval_average_translation (a : ℝ) (u v : Space) :
    (∫ t : ℝ in Set.Ioc 0 1, inner ℂ (shift t u) (translation a (shift t v))) =
      inner ℂ u (translation a v) := by
  have h := interval_average_weylWord a 0 u v
  simpa only [weylWord_zero_frequency, phaseAverage_zero, one_mul] using h

/-- The Fourier attenuation has its exact removable-singularity formula. -/
theorem phaseAverage_formula (ω : ℝ) :
    phaseAverage ω = if ω = 0 then 1 else
      ((Circle.exp (-ω) : ℂ) - 1) / (((-ω : ℝ) : ℂ) * Complex.I) := by
  classical
  by_cases h : ω = 0
  · rw [h, phaseAverage_zero, if_pos rfl]
  · rw [if_neg h]
    have he := _root_.RHTower.Sieve.integral_exp_phase (-ω) (neg_ne_zero.mpr h) 1
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] at he
    change (∫ t : ℝ in Set.Ioc 0 1, Complex.exp (((t * -ω : ℝ) : ℂ) * Complex.I)) = _ at he
    simpa only [phaseAverage, Circle.coe_exp, mul_comm (-ω), one_mul] using he

/-- Weyl coefficients are integrable on the exact interval used by the weak average. -/
theorem weylWord_coefficient_integrableOn (a ω : ℝ) (u v : Space) :
    IntegrableOn (fun t : ℝ => inner ℂ (shift t u) (weylWord a ω (shift t v)))
      (Set.Ioc 0 1) := by
  simp_rw [weylWord_shift_coefficient]
  have h := (_root_.RHTower.Sieve.intervalIntegrable_exp_phase (-ω) 0 1).1
  have hp : IntegrableOn (fun t : ℝ => (Circle.exp (-ω * t) : ℂ)) (Set.Ioc 0 1) := by
    simpa only [Circle.coe_exp, mul_comm (-ω)] using h
  exact hp.mul_const _

/-- The unit interval annihilates exactly the nonzero integer Fourier frequencies. -/
theorem phaseAverage_integer (k : ℤ) :
    phaseAverage (2 * Real.pi * (k : ℝ)) = if k = 0 then 1 else 0 := by
  classical
  by_cases hk : k = 0
  · subst k
    simp only [Int.cast_zero, mul_zero, phaseAverage_zero, if_true]
  · have hω : 2 * Real.pi * (k : ℝ) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) (by exact_mod_cast hk)
    rw [phaseAverage_formula, if_neg hω, if_neg hk]
    have he : (Circle.exp (-(2 * Real.pi * (k : ℝ))) : ℂ) = 1 := by
      rw [Circle.coe_exp]
      have ha : (((-(2 * Real.pi * (k : ℝ)) : ℝ) : ℂ) * Complex.I) =
          ((-k : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by push_cast; ring
      rw [ha, Complex.exp_int_mul_two_pi_mul_I]
    rw [he, sub_self, zero_div]

/-- Integer-frequency averaging retains translations and removes every modulated Weyl word. -/
theorem interval_average_integer_weylWord (a : ℝ) (k : ℤ) (u v : Space) :
    (∫ t : ℝ in Set.Ioc 0 1,
      inner ℂ (shift t u) (weylWord a (2 * Real.pi * (k : ℝ)) (shift t v))) =
        if k = 0 then inner ℂ u (translation a v) else 0 := by
  rw [interval_average_weylWord, phaseAverage_integer]
  by_cases hk : k = 0
  · subst k
    simp only [Int.cast_zero, mul_zero, if_true, one_mul, weylWord_zero_frequency]
  · simp only [if_neg hk, zero_mul]

/-- A finite observable polynomial in actual real translations and integer modulations. -/
def integerWeylPolynomial {m : ℕ} (a : Fin m → ℝ) (k : Fin m → ℤ)
    (c : Fin m → ℂ) : Space →L[ℂ] Space :=
  ∑ i, c i • weylWord (a i) (2 * Real.pi * (k i : ℝ))

/-- The translation part retained after eliminating all nonzero modulation frequencies. -/
def zeroFrequencyPart {m : ℕ} (a : Fin m → ℝ) (k : Fin m → ℤ)
    (c : Fin m → ℂ) : Space →L[ℂ] Space :=
  ∑ i, if k i = 0 then c i • translation (a i) else 0

/-- Weak averaging of a finite Weyl polynomial is the actual zero-frequency observable. -/
theorem interval_average_integerWeylPolynomial {m : ℕ}
    (a : Fin m → ℝ) (k : Fin m → ℤ) (c : Fin m → ℂ) (u v : Space) :
    (∫ t : ℝ in Set.Ioc 0 1,
      inner ℂ (shift t u) (integerWeylPolynomial a k c (shift t v))) =
        inner ℂ u (zeroFrequencyPart a k c v) := by
  simp only [integerWeylPolynomial, _root_.sum_apply, smul_apply,
    inner_sum, inner_smul_right]
  rw [integral_finsetSum _ (fun i _ =>
    (weylWord_coefficient_integrableOn (a i) (2 * Real.pi * (k i : ℝ)) u v).const_mul (c i))]
  simp_rw [integral_const_mul, interval_average_integer_weylWord]
  simp only [zeroFrequencyPart, _root_.sum_apply, inner_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : k i = 0
  · simp only [if_pos hi, smul_apply, inner_smul_right]
  · simp only [if_neg hi, mul_zero, zero_apply, inner_zero_right]

#print axioms shift_add
#print axioms norm_modulation
#print axioms norm_weylWord
#print axioms weylWord_mul
#print axioms weylWord_commutation
#print axioms translatedObservable_inner
#print axioms translatedObservable_weylWord
#print axioms weylWord_shift_coefficient
#print axioms interval_average_weylWord
#print axioms norm_phaseAverage_le_one
#print axioms interval_average_translation
#print axioms phaseAverage_formula
#print axioms weylWord_coefficient_integrableOn
#print axioms phaseAverage_integer
#print axioms interval_average_integer_weylWord
#print axioms interval_average_integerWeylPolynomial
end GaloisForLFunctions.HilbertMetric.ShiftAverage
