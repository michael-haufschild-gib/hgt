import GaloisForLFunctions.HTGeometry.GomesDilatonMassNormalization
import GaloisForLFunctions.HTGeometry.GomesGaussianChargeMeasure
import GaloisForLFunctions.HTGeometry.GomesQuarticChargeGroundState

/-!
# Gaussian and quartic charge laws after mass normalization

The integer tensor charges of arXiv:2509.25276v7 section 5.2 meet the reconstruction
question of arXiv:2607.24901v1 section 4 in two existing density families. Positive
charges give probability laws that retain their effective charge. Nonpositive charges
collapse to zero under total normalization. A Gaussian and a quartic normalized law
can agree only through this invalid-probability collapse, never as probability laws.
-/

noncomputable section
open Polynomial MeasureTheory
open scoped NNReal ENNReal SchwartzMap

namespace GaloisForLFunctions.HTGeometry

/-- The general raw construction is the existing Gaussian integer-charge measure. -/
theorem gomesDilatonMeasure_gaussian (b : ℝ) (n : ℤ) :
    gomesDilatonMeasure (gomesGaussianTensorLogWeight b n) = gomesGaussianChargeMeasure b n := rfl

/-- The general raw construction is also the existing quartic integer-charge measure. -/
theorem gomesDilatonMeasure_quartic (b : ℝ) (n : ℤ) :
    gomesDilatonMeasure (gomesQuarticTensorLogWeight b n) = gomesQuarticChargeMeasure b n := rfl

/-- Total-mass normalized Gaussian charge observation. -/
def gomesGaussianNormalizedCharge (b : ℝ) (n : ℤ) : Measure ℝ :=
  gomesDilatonMassNormalized (gomesGaussianTensorLogWeight b n)

/-- Total-mass normalized quartic charge observation. -/
def gomesQuarticNormalizedCharge (b : ℝ) (n : ℤ) : Measure ℝ :=
  gomesDilatonMassNormalized (gomesQuarticTensorLogWeight b n)

/-- The entire Gaussian positive half-lattice consists of genuine probability laws. -/
theorem gomesGaussianNormalizedCharge_probability_iff (b : ℝ) (n : ℤ) :
    IsProbabilityMeasure (gomesGaussianNormalizedCharge b n) ↔ 0 < (n : ℝ) * b := by
  rw [gomesGaussianNormalizedCharge, gomesDilatonMassNormalized_probability_iff,
    gomesDilatonMeasure_gaussian, gomesGaussianChargeMeasure_finite_iff]

/-- Quartic probability normalization succeeds on exactly the same positive half-lattice. -/
theorem gomesQuarticNormalizedCharge_probability_iff (b : ℝ) (n : ℤ) :
    IsProbabilityMeasure (gomesQuarticNormalizedCharge b n) ↔ 0 < (n : ℝ) * b := by
  rw [gomesQuarticNormalizedCharge, gomesDilatonMassNormalized_probability_iff,
    gomesDilatonMeasure_quartic, gomesQuarticChargeMeasure_finite_iff]

/-- Nonpositive Gaussian effective charge collapses to zero, including the tensor unit. -/
theorem gomesGaussianNormalizedCharge_zero_iff (b : ℝ) (n : ℤ) :
    gomesGaussianNormalizedCharge b n = 0 ↔ (n : ℝ) * b ≤ 0 := by
  rw [gomesGaussianNormalizedCharge, gomesDilatonMassNormalized_zero_iff,
    gomesDilatonMeasure_gaussian, gomesGaussianChargeMeasure_infinite_iff]

/-- Nonpositive quartic effective charge collapses to zero as well. -/
theorem gomesQuarticNormalizedCharge_zero_iff (b : ℝ) (n : ℤ) :
    gomesQuarticNormalizedCharge b n = 0 ↔ (n : ℝ) * b ≤ 0 := by
  rw [gomesQuarticNormalizedCharge, gomesDilatonMassNormalized_zero_iff,
    gomesDilatonMeasure_quartic, gomesQuarticChargeMeasure_infinite_iff]

/-- A constant ambiguity cannot hide any Gaussian effective charge. -/
theorem gomesGaussianLogWeight_constant_iff (a b : ℝ) :
    (∃ c : ℝ, gomesGaussianLogWeight a = gomesGaussianLogWeight b + C c) ↔ a = b := by
  constructor
  · rintro ⟨c, hc⟩
    have hd := congrArg (fun p : ℝ[X] => p.derivative.eval 1) hc
    simp only [derivative_add, derivative_C, add_zero,
      gomesGaussianLogWeight_derivative_eval, mul_one] at hd
    have he : Real.pi * a = Real.pi * b := by linarith
    exact mul_left_cancel₀ Real.pi_ne_zero he
  · rintro rfl
    exact ⟨0, by simp⟩

/-- A constant ambiguity cannot hide any quartic effective charge either. -/
theorem gomesQuarticLogWeight_constant_iff (a b : ℝ) :
    (∃ c : ℝ, gomesQuarticLogWeight a = gomesQuarticLogWeight b + C c) ↔ a = b := by
  constructor
  · rintro ⟨c, hc⟩
    have hd := congrArg (fun p : ℝ[X] => p.derivative.eval 1) hc
    simp only [derivative_add, derivative_C, add_zero,
      gomesQuarticLogWeight_derivative_eval, one_pow, mul_one] at hd
    linarith
  · rintro rfl
    exact ⟨0, by simp⟩

/-- Gaussian and quartic shapes can coincide only when both are the neutral constant shape. -/
theorem gomesGaussianQuarticLogWeight_constant_iff (a b : ℝ) :
    (∃ c : ℝ, gomesGaussianLogWeight a = gomesQuarticLogWeight b + C c) ↔ a = 0 ∧ b = 0 := by
  constructor
  · rintro ⟨c, hc⟩
    have h2 := congrArg (fun p : ℝ[X] => p.derivative.derivative.eval 0) hc
    simp only [derivative_add, derivative_C, add_zero,
      gomesGaussianLogWeight_second_derivative_eval,
      gomesQuarticLogWeight_second_derivative_eval, pow_two, mul_zero] at h2
    have he : Real.pi * a = 0 := by linarith
    have ha : a = 0 := (mul_eq_zero.mp he).resolve_left Real.pi_ne_zero
    have h1 := congrArg (fun p : ℝ[X] => p.derivative.eval 1) hc
    simp only [derivative_add, derivative_C, add_zero,
      gomesGaussianLogWeight_derivative_eval, gomesQuarticLogWeight_derivative_eval,
      ha, mul_zero, one_pow, mul_one] at h1
    exact ⟨ha, by linarith⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨0, by simp [gomesGaussianLogWeight, gomesQuarticLogWeight]⟩

/-- Complete Gaussian law equality, distinguishing effective-charge recovery from joint collapse. -/
theorem gomesGaussianNormalizedCharge_eq_iff (b c : ℝ) (n m : ℤ) :
    gomesGaussianNormalizedCharge b n = gomesGaussianNormalizedCharge c m ↔
      (n : ℝ) * b = (m : ℝ) * c ∨ ((n : ℝ) * b ≤ 0 ∧ (m : ℝ) * c ≤ 0) := by
  rw [gomesGaussianNormalizedCharge, gomesGaussianNormalizedCharge,
    gomesDilatonMassNormalized_eq_iff, gomesDilatonMeasure_gaussian,
    gomesDilatonMeasure_gaussian, gomesGaussianChargeMeasure_infinite_iff,
    gomesGaussianChargeMeasure_infinite_iff]
  exact or_congr (gomesGaussianLogWeight_constant_iff _ _) Iff.rfl

/-- Complete quartic law equality, with the same exact two sources of ambiguity. -/
theorem gomesQuarticNormalizedCharge_eq_iff (b c : ℝ) (n m : ℤ) :
    gomesQuarticNormalizedCharge b n = gomesQuarticNormalizedCharge c m ↔
      (n : ℝ) * b = (m : ℝ) * c ∨ ((n : ℝ) * b ≤ 0 ∧ (m : ℝ) * c ≤ 0) := by
  rw [gomesQuarticNormalizedCharge, gomesQuarticNormalizedCharge,
    gomesDilatonMassNormalized_eq_iff, gomesDilatonMeasure_quartic,
    gomesDilatonMeasure_quartic, gomesQuarticChargeMeasure_infinite_iff,
    gomesQuarticChargeMeasure_infinite_iff]
  exact or_congr (gomesQuarticLogWeight_constant_iff _ _) Iff.rfl

/-- Cross-family normalized observations agree exactly when both are zero, never as probabilities. -/
theorem gomesGaussianQuarticNormalizedCharge_eq_iff (b c : ℝ) (n m : ℤ) :
    gomesGaussianNormalizedCharge b n = gomesQuarticNormalizedCharge c m ↔
      (n : ℝ) * b ≤ 0 ∧ (m : ℝ) * c ≤ 0 := by
  rw [gomesGaussianNormalizedCharge, gomesQuarticNormalizedCharge,
    gomesDilatonMassNormalized_eq_iff, gomesDilatonMeasure_gaussian,
    gomesDilatonMeasure_quartic, gomesGaussianChargeMeasure_infinite_iff,
    gomesQuarticChargeMeasure_infinite_iff]
  change ((∃ d : ℝ, gomesGaussianLogWeight ((n : ℝ) * b) =
      gomesQuarticLogWeight ((m : ℝ) * c) + C d) ∨ _) ↔ _
  rw [gomesGaussianQuarticLogWeight_constant_iff]
  constructor
  · rintro (⟨hh, hk⟩ | h)
    · exact ⟨le_of_eq hh, le_of_eq hk⟩
    · exact h
  · exact Or.inr

/-- Positive Gaussian and quartic charge probability laws are always distinct. -/
theorem gomesGaussianQuarticNormalizedCharge_distinct (b c : ℝ)
    (n : GomesGaussianFiniteCharge b) (m : GomesQuarticFiniteCharge c) :
    gomesGaussianNormalizedCharge b n.val ≠ gomesQuarticNormalizedCharge c m.val := by
  intro h
  have hn := (gomesGaussianQuarticNormalizedCharge_eq_iff b c n.val m.val).mp h
  exact (not_le_of_gt n.property) hn.1

/-- A charge and its dual normalize to the same Gaussian observation only at zero effective charge. -/
theorem gomesGaussianNormalizedCharge_dual_iff (b : ℝ) (n : ℤ) :
    gomesGaussianNormalizedCharge b n = gomesGaussianNormalizedCharge b (-n) ↔
      (n : ℝ) * b = 0 := by
  rw [gomesGaussianNormalizedCharge_eq_iff]
  simp only [Int.cast_neg, neg_mul]
  constructor
  · rintro (h | ⟨h, h'⟩) <;> linarith
  · intro h
    exact Or.inl (by rw [h, neg_zero])

/-- Quartic dual equality has the same exact zero-charge threshold. -/
theorem gomesQuarticNormalizedCharge_dual_iff (b : ℝ) (n : ℤ) :
    gomesQuarticNormalizedCharge b n = gomesQuarticNormalizedCharge b (-n) ↔
      (n : ℝ) * b = 0 := by
  rw [gomesQuarticNormalizedCharge_eq_iff]
  simp only [Int.cast_neg, neg_mul]
  constructor
  · rintro (h | ⟨h, h'⟩) <;> linarith
  · intro h
    exact Or.inl (by rw [h, neg_zero])

end GaloisForLFunctions.HTGeometry
