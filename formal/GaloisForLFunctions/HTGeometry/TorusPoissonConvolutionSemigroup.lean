import GaloisForLFunctions.HTGeometry.PrimePoissonProductState
import GaloisForLFunctions.HTGeometry.SummableSpectrumScrewHull

/-!
# Convolution semigroup of product Poisson laws on a countable torus

Circle Poisson laws multiply their disk parameters under convolution, `P_a ∗ P_b = P_{ab}`, and
the reflection `x ↦ -x` conjugates the parameter, `(-)_* P_a = P_{ā}`.  Both laws hold on an
arbitrary countable product torus.  The proof compares finite-support Fourier characters: a
character is a homomorphism of the torus, so its integral against a convolution factors, and
finite-support characters determine probability measures.
-/

open MeasureTheory Complex
open scoped ComplexConjugate

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Product of two open-disk parameters. -/
def circlePoissonParameterMul (a b : CirclePoissonParameter) : CirclePoissonParameter :=
  ⟨(a : ℂ) * b, by
    have ha : ‖(a : ℂ)‖ < 1 := mem_ball_zero_iff.mp a.2
    have hb : ‖(b : ℂ)‖ < 1 := mem_ball_zero_iff.mp b.2
    rw [mem_ball_zero_iff, norm_mul]
    nlinarith [norm_nonneg (a : ℂ), norm_nonneg (b : ℂ)]⟩

@[simp]
theorem coe_circlePoissonParameterMul (a b : CirclePoissonParameter) :
    ((circlePoissonParameterMul a b : CirclePoissonParameter) : ℂ) = (a : ℂ) * b := rfl

/-- Complex conjugate of an open-disk parameter. -/
def circlePoissonParameterConj (a : CirclePoissonParameter) : CirclePoissonParameter :=
  ⟨conj (a : ℂ), by
    rw [mem_ball_zero_iff, Complex.norm_conj]
    exact mem_ball_zero_iff.mp a.2⟩

@[simp]
theorem coe_circlePoissonParameterConj (a : CirclePoissonParameter) :
    ((circlePoissonParameterConj a : CirclePoissonParameter) : ℂ) = conj (a : ℂ) := rfl

/-- Poisson Fourier moments are multiplicative in the disk parameter. -/
theorem circlePoissonFourierMoment_mul (a b : CirclePoissonParameter) (q : ℤ) :
    circlePoissonFourierMoment (circlePoissonParameterMul a b) q =
      circlePoissonFourierMoment a q * circlePoissonFourierMoment b q := by
  rcases q with n | n
  · simp [circlePoissonFourierMoment, mul_pow]
  · simp [circlePoissonFourierMoment, mul_pow]

/-- Conjugating the disk parameter reverses the Fourier index. -/
theorem circlePoissonFourierMoment_conj (a : CirclePoissonParameter) (q : ℤ) :
    circlePoissonFourierMoment (circlePoissonParameterConj a) q =
      circlePoissonFourierMoment a (-q) := by
  rcases q with n | n
  · rcases n with _ | k
    · simp [circlePoissonFourierMoment]
    · change conj (a : ℂ) ^ (k + 1) = circlePoissonFourierMoment a (Int.negSucc k)
      simp [circlePoissonFourierMoment]
  · change conj (conj (a : ℂ)) ^ (n + 1) = circlePoissonFourierMoment a (Int.ofNat (n + 1))
    simp [circlePoissonFourierMoment]

variable {I : Type*}

/-- A finite-support character at the reflected point is the conjugate character. -/
theorem infiniteTorusFourier_neg_point (n : I →₀ ℤ) (x : I → UnitAddCircle) :
    infiniteTorusFourier n (-x) = infiniteTorusFourier (-n) x := by
  classical
  rw [infiniteTorusFourier_neg]
  simp only [infiniteTorusFourier, ContinuousMap.coe_mk, Pi.neg_apply]
  rw [map_finsuppProd]
  refine Finsupp.prod_congr fun i _ => ?_
  rw [fourier_apply, smul_neg, fourier_neg']

theorem integrable_infiniteTorusFourier [Countable I] (μ : Measure (I → UnitAddCircle)) [IsFiniteMeasure μ]
    (n : I →₀ ℤ) : Integrable (fun x => infiniteTorusFourier n x) μ :=
  (infiniteTorusFourier n).continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Finite-support characters turn convolution of finite measures into multiplication. -/
theorem integral_infiniteTorusFourier_conv [Countable I] (μ ν : Measure (I → UnitAddCircle))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (n : I →₀ ℤ) :
    ∫ x, infiniteTorusFourier n x ∂(μ ∗ ν) =
      (∫ x, infiniteTorusFourier n x ∂μ) * ∫ x, infiniteTorusFourier n x ∂ν := by
  haveI : IsFiniteMeasure (μ ∗ ν) := Measure.finite_of_finite_conv μ ν
  rw [integral_conv (integrable_infiniteTorusFourier (μ ∗ ν) n)]
  simp_rw [infiniteTorusFourier_add_point, integral_const_mul]
  rw [integral_mul_const]

/-- Integral of a finite-support character against a reflected finite measure. -/
theorem integral_infiniteTorusFourier_map_neg [Countable I] (μ : Measure (I → UnitAddCircle))
    (n : I →₀ ℤ) :
    ∫ x, infiniteTorusFourier n x ∂(μ.map Neg.neg) =
      ∫ x, infiniteTorusFourier (-n) x ∂μ := by
  rw [integral_map measurable_neg.aemeasurable
    (infiniteTorusFourier n).continuous.aestronglyMeasurable]
  simp_rw [infiniteTorusFourier_neg_point]

/-- **Poisson convolution semigroup.**  Product Poisson laws convolve by multiplying their disk
parameters coordinatewise. -/
theorem torusPoissonMeasure_conv [Countable I] (a b : I → CirclePoissonParameter) :
    torusPoissonMeasure a ∗ torusPoissonMeasure b =
      torusPoissonMeasure (fun i => circlePoissonParameterMul (a i) (b i)) := by
  have h := probabilityMeasure_ext_of_infiniteTorusFourier_integral_eq
    ⟨torusPoissonMeasure a ∗ torusPoissonMeasure b, inferInstance⟩
    (torusPoissonProbabilityMeasure fun i => circlePoissonParameterMul (a i) (b i))
    (fun n => by
      change ∫ x, infiniteTorusFourier n x ∂(torusPoissonMeasure a ∗ torusPoissonMeasure b) =
        ∫ x, infiniteTorusFourier n x
          ∂(torusPoissonMeasure fun i => circlePoissonParameterMul (a i) (b i))
      rw [integral_infiniteTorusFourier_conv, integral_infiniteTorusFourier_torusPoissonMeasure,
        integral_infiniteTorusFourier_torusPoissonMeasure,
        integral_infiniteTorusFourier_torusPoissonMeasure, ← Finsupp.prod_mul]
      simp_rw [circlePoissonFourierMoment_mul])
  exact congrArg ProbabilityMeasure.toMeasure h

/-- **Poisson reflection law.**  Reflecting a product Poisson law conjugates every disk
parameter. -/
theorem map_neg_torusPoissonMeasure [Countable I] (a : I → CirclePoissonParameter) :
    (torusPoissonMeasure a).map Neg.neg =
      torusPoissonMeasure (fun i => circlePoissonParameterConj (a i)) := by
  haveI : IsProbabilityMeasure ((torusPoissonMeasure a).map Neg.neg) :=
    Measure.isProbabilityMeasure_map measurable_neg.aemeasurable
  have h := probabilityMeasure_ext_of_infiniteTorusFourier_integral_eq
    ⟨(torusPoissonMeasure a).map Neg.neg, inferInstance⟩
    (torusPoissonProbabilityMeasure fun i => circlePoissonParameterConj (a i))
    (fun n => by
      change ∫ x, infiniteTorusFourier n x ∂((torusPoissonMeasure a).map Neg.neg) =
        ∫ x, infiniteTorusFourier n x
          ∂(torusPoissonMeasure fun i => circlePoissonParameterConj (a i))
      rw [integral_infiniteTorusFourier_map_neg,
        integral_infiniteTorusFourier_torusPoissonMeasure,
        integral_infiniteTorusFourier_torusPoissonMeasure,
        Finsupp.prod_neg_index (fun i => by simp [circlePoissonFourierMoment])]
      simp_rw [circlePoissonFourierMoment_conj])
  exact congrArg ProbabilityMeasure.toMeasure h

end

end GaloisForLFunctions.HTGeometry
