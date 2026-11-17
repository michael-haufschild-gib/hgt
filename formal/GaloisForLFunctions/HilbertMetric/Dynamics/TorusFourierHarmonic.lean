import GaloisForLFunctions.HTGeometry.ActivePhaseLattice
import GaloisForLFunctions.HTGeometry.FiniteSpectralHaarRecurrenceLaw
import GaloisForLFunctions.RHTower.Deninger.DeningerTorusFlow
import GaloisForLFunctions.RHTower.PrimeIrrationalRotationKZeroRH

/-!
# The Fourier harmonic equation of a prime irrational torus foliation

The harmonic-measure mechanism in arXiv:2610.34557 applies to the actual
linear torus flows. Twice differentiating each character along a leaf
multiplies it by minus its squared angular frequency. The weak equation
on all characters therefore retains exactly resonant Fourier modes.
For the prime irrational slope, this character-test equation has precisely
one probability solution: normalized Haar measure.
-/

open MeasureTheory Filter Topology UnitAddTorus
open scoped BigOperators
namespace GaloisForLFunctions.HilbertMetric.Dynamics.TorusHarmonic
open HTGeometry _root_.RHTower
noncomputable section
variable {d : Type*} [Fintype d]

/-- A character restricted to the actual flow leaf through the point `x`. -/
def characterPath (lam : d → ℝ) (n : d → ℤ) (x : UnitAddTorus d) (t : ℝ) : ℂ :=
  mFourier n (x + deningerTorusFlow lam t)

private def frequencyFactor (lam : d → ℝ) (n : d → ℤ) : ℂ :=
  ((2 * Real.pi * deningerFrequency n lam : ℝ) : ℂ) * Complex.I

private theorem characterPath_exp (lam : d → ℝ) (n : d → ℤ) (x : UnitAddTorus d) :
    characterPath lam n x =
      fun t : ℝ => mFourier n x * Complex.exp (frequencyFactor lam n * (t : ℂ)) := by
  funext t
  rw [characterPath, mFourier_add_point, deningerMFourier_flow]
  congr 2
  unfold frequencyFactor
  push_cast
  ring

/-- The genuine first derivative along a leaf is its character frequency multiplier. -/
theorem characterPath_hasDerivAt (lam : d → ℝ) (n : d → ℤ) (x : UnitAddTorus d) (t : ℝ) :
    HasDerivAt (characterPath lam n x)
      (frequencyFactor lam n * characterPath lam n x t) t := by
  rw [characterPath_exp]
  have h0 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
  have h := ((h0.const_mul (frequencyFactor lam n)).cexp).const_mul (mFourier n x)
  convert h using 1 <;> ring

/-- The leaf Laplacian is the actual iterated real derivative, evaluated at the point. -/
def characterLaplacian (lam : d → ℝ) (n : d → ℤ) (x : UnitAddTorus d) : ℂ :=
  deriv (deriv (characterPath lam n x)) 0

/-- Fourier characters diagonalize the literal second derivative along the foliation. -/
theorem characterLaplacian_eq (lam : d → ℝ) (n : d → ℤ) (x : UnitAddTorus d) :
    characterLaplacian lam n x =
      -(((2 * Real.pi * deningerFrequency n lam : ℝ) : ℂ) ^ 2) * mFourier n x := by
  have hd : deriv (characterPath lam n x) =
      fun t => frequencyFactor lam n * characterPath lam n x t :=
    funext fun t => (characterPath_hasDerivAt lam n x t).deriv
  rw [characterLaplacian, hd, ((characterPath_hasDerivAt lam n x 0).const_mul
    (frequencyFactor lam n)).deriv]
  have hz : deningerTorusFlow lam 0 = 0 := by
    funext i
    simp only [deningerTorusFlow, zero_mul, AddCircle.coe_zero, Pi.zero_apply]
  rw [characterPath, hz, add_zero]
  unfold frequencyFactor
  calc
    _ = (((2 * Real.pi * deningerFrequency n lam : ℝ) : ℂ) ^ 2 * Complex.I ^ 2) *
        mFourier n x := by ring
    _ = _ := by rw [Complex.I_sq]; ring

/-- The weak harmonic equation tested on every finite torus character. -/
def FourierHarmonic (lam : d → ℝ) (μ : ProbabilityMeasure (UnitAddTorus d)) : Prop :=
  ∀ n : d → ℤ, (∫ x, characterLaplacian lam n x ∂(μ : Measure (UnitAddTorus d))) = 0

/-- Exactly the nonresonant Fourier coefficients must vanish. -/
theorem fourierHarmonic_iff (lam : d → ℝ) (μ : ProbabilityMeasure (UnitAddTorus d)) :
    FourierHarmonic lam μ ↔ ∀ n : d → ℤ, deningerFrequency n lam ≠ 0 →
      (∫ x, mFourier n x ∂(μ : Measure (UnitAddTorus d))) = 0 := by
  have he (n : d → ℤ) :
      (∫ x, characterLaplacian lam n x ∂(μ : Measure (UnitAddTorus d))) =
        -(((2 * Real.pi * deningerFrequency n lam : ℝ) : ℂ) ^ 2) *
          ∫ x, mFourier n x ∂(μ : Measure (UnitAddTorus d)) := by
    simp only [characterLaplacian_eq, integral_const_mul]
  constructor
  · intro h n hn
    have hc : -(((2 * Real.pi * deningerFrequency n lam : ℝ) : ℂ) ^ 2) ≠ 0 :=
      neg_ne_zero.mpr (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr
        (mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hn)))
    exact (mul_eq_zero.mp ((he n).symm.trans (h n))).resolve_left hc
  · intro h n
    rw [he]
    by_cases hn : deningerFrequency n lam = 0
    · simp only [hn, mul_zero, Complex.ofReal_zero, zero_pow (by decide : (2 : ℕ) ≠ 0),
        neg_zero, zero_mul]
    · rw [h n hn, mul_zero]

/-- Concrete prime irrational slope, with its nonzero time denominator fixed to one. -/
def primeVelocity (p : Nat.Primes) : Fin 2 → ℝ := ![1, primeRotationParameter p 1]

private theorem primeFrequency_eq (p : Nat.Primes) (n : Fin 2 → ℤ) :
    deningerFrequency n (primeVelocity p) = (n 0 : ℝ) + primeRotationParameter p 1 * n 1 := by
  simp only [deningerFrequency, Fin.sum_univ_two, primeVelocity, Matrix.cons_val_zero,
    Matrix.cons_val_one, mul_one]
  ring

/-- Prime arithmetic removes every nontrivial resonant character. -/
theorem primeFrequency_zero_iff (p : Nat.Primes) (n : Fin 2 → ℤ) :
    deningerFrequency n (primeVelocity p) = 0 ↔ n = 0 := by
  constructor
  · intro h
    rw [primeFrequency_eq] at h
    have h1 : n 1 = 0 := chern_eq_zero_of_irrationalRotationKZeroTrace_eq_integer
      (primeRotationParameter_irrational p (by norm_num : (1 : ℕ) ≠ 0)) (index := 0)
      (by simpa only [irrationalRotationKZeroTrace, Int.cast_zero] using h)
    have h0 : n 0 = 0 := by
      rw [h1, Int.cast_zero, mul_zero, add_zero] at h
      exact_mod_cast h
    funext i
    fin_cases i
    · change n 0 = 0
      exact h0
    · change n 1 = 0
      exact h1
  · rintro rfl
    exact deningerFrequency_zero _

/-- The character-test harmonic equation has exactly Haar probability as its solution. -/
theorem prime_fourierHarmonic_iff_haar (p : Nat.Primes)
    (μ : ProbabilityMeasure (UnitAddTorus (Fin 2))) :
    FourierHarmonic (primeVelocity p) μ ↔ μ = finiteTorusHaarProbabilityMeasure (Fin 2) := by
  rw [fourierHarmonic_iff]
  constructor
  · intro h
    apply probabilityMeasure_ext_of_mFourier_integral_eq
    intro n
    rw [finiteTorusHaarProbabilityMeasure_mFourier_integral]
    by_cases hn : n = 0
    · subst n
      simp [mFourier_zero]
    · rw [if_neg hn]
      exact h n (fun hz => hn ((primeFrequency_zero_iff p n).mp hz))
  · rintro rfl n hn
    rw [finiteTorusHaarProbabilityMeasure_mFourier_integral, if_neg]
    exact fun hz => hn ((primeFrequency_zero_iff p n).mpr hz)

/-- Pushforward of a probability law by the actual leaf flow. -/
def flowTranslate (lam : d → ℝ) (μ : ProbabilityMeasure (UnitAddTorus d)) (t : ℝ) :
    ProbabilityMeasure (UnitAddTorus d) :=
  μ.map (f := fun x => x + deningerTorusFlow lam t)
    (continuous_id.add continuous_const).aemeasurable

private theorem flowTranslate_fourier (lam : d → ℝ)
    (μ : ProbabilityMeasure (UnitAddTorus d)) (t : ℝ) (n : d → ℤ) :
    (∫ x, mFourier n x ∂(flowTranslate lam μ t : Measure (UnitAddTorus d))) =
      (∫ x, mFourier n x ∂(μ : Measure (UnitAddTorus d))) *
        mFourier n (deningerTorusFlow lam t) := by
  rw [flowTranslate, ProbabilityMeasure.toMeasure_map,
    integral_map (continuous_id.add continuous_const).aemeasurable
      (mFourier n).continuous.aestronglyMeasurable]
  simp only [mFourier_add_point, integral_mul_const]

/-- The character harmonic equation is exactly invariance of the full probability law. -/
theorem fourierHarmonic_iff_flow_invariant (lam : d → ℝ)
    (μ : ProbabilityMeasure (UnitAddTorus d)) :
    FourierHarmonic lam μ ↔ ∀ t : ℝ, flowTranslate lam μ t = μ := by
  rw [fourierHarmonic_iff]
  constructor
  · intro h t
    apply probabilityMeasure_ext_of_mFourier_integral_eq
    intro n
    rw [flowTranslate_fourier]
    by_cases hn : deningerFrequency n lam = 0
    · rw [deningerMFourier_flow, hn]
      simp only [mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one]
    · rw [h n hn, zero_mul]
  · intro h n hn
    have he := congrArg
      (fun ν : ProbabilityMeasure (UnitAddTorus d) =>
        ∫ x, mFourier n x ∂(ν : Measure (UnitAddTorus d)))
      (h (1 / (2 * deningerFrequency n lam)))
    rw [flowTranslate_fourier, deningerMFourier_flow] at he
    have ht : 2 * Real.pi * deningerFrequency n lam *
        (1 / (2 * deningerFrequency n lam)) = Real.pi := by
      field_simp [hn]
    rw [ht, Complex.exp_pi_mul_I, mul_neg_one] at he
    linear_combination -(1 / 2 : ℂ) * he

/-- Prime irrational slope has exactly one invariant probability law. -/
theorem prime_flow_invariant_iff_haar (p : Nat.Primes)
    (μ : ProbabilityMeasure (UnitAddTorus (Fin 2))) :
    (∀ t : ℝ, flowTranslate (primeVelocity p) μ t = μ) ↔
      μ = finiteTorusHaarProbabilityMeasure (Fin 2) := by
  rw [← fourierHarmonic_iff_flow_invariant, prime_fourierHarmonic_iff_haar]

#print axioms characterLaplacian_eq
#print axioms fourierHarmonic_iff
#print axioms primeFrequency_zero_iff
#print axioms prime_fourierHarmonic_iff_haar
#print axioms fourierHarmonic_iff_flow_invariant
#print axioms prime_flow_invariant_iff_haar
end
end GaloisForLFunctions.HilbertMetric.Dynamics.TorusHarmonic
