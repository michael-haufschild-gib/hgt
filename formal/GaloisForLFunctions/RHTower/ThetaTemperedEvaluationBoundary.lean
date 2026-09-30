import GaloisForLFunctions.HTGeometry.PositiveEvenSchwartzLaplaceEscape
import Mathlib.Analysis.Distribution.TemperedDistribution

/-!
# Exact tempered boundary of Fourier–Laplace evaluation

Remote positive even Schwartz packets exclude every off-real evaluator,
even on the sources where all exponential integrals converge. Every real
evaluator is the actual Fourier transform of a Dirac distribution and
agrees with the literal integral on all complex Schwartz functions.
-/

noncomputable section
open MeasureTheory Filter Topology Set
open scoped SchwartzMap FourierTransform
namespace RHTower
open GaloisForLFunctions.HTGeometry.PositiveEvenLaplaceEscape

/-- The continuous real-linear embedding of real into complex Schwartz functions. -/
def thetaRealSchwartzComplexification : 𝓢(ℝ, ℝ) →L[ℝ] 𝓢(ℝ, ℂ) :=
  SchwartzMap.postcompCLM Complex.ofRealCLM

theorem thetaRealSchwartzComplexification_apply (f : 𝓢(ℝ, ℝ)) (x : ℝ) :
    thetaRealSchwartzComplexification f x = (f x : ℂ) := rfl

/-- The literal physical-frequency exponential evaluator. -/
def thetaSchwartzFourierLaplaceEvaluation (z : ℂ) (f : 𝓢(ℝ, ℂ)) : ℂ :=
  ∫ x : ℝ, Complex.exp ((Complex.I * z) * (x : ℂ)) * f x

/-- The complex Schwartz sources on which every exponential integral converges. -/
def thetaSchwartzExponentialDomain (f : 𝓢(ℝ, ℂ)) : Prop :=
  ∀ z : ℂ, Integrable (fun x : ℝ => Complex.exp ((Complex.I * z) * (x : ℂ)) * f x)

theorem thetaRealSchwartzComplexification_mem_exponentialDomain
    (f : 𝓢(ℝ, ℝ)) (hf : HasEntireLaplace f) :
    thetaSchwartzExponentialDomain (thetaRealSchwartzComplexification f) := by
  intro z
  exact hf (Complex.I * z)

theorem thetaSchwartzFourierLaplaceEvaluation_real (z : ℂ) (f : 𝓢(ℝ, ℝ)) :
    thetaSchwartzFourierLaplaceEvaluation z (thetaRealSchwartzComplexification f) =
      bilateralLaplace f (Complex.I * z) := rfl

/-- Even the real sources with entire Laplace transform exclude a tempered extension. -/
theorem thetaOffRealEvaluation_not_tempered_real (z : ℂ) (hz : z.im ≠ 0) :
    ¬ ∃ T : 𝓢'(ℝ, ℂ), ∀ f : 𝓢(ℝ, ℝ), HasEntireLaplace f →
      T (thetaRealSchwartzComplexification f) =
        thetaSchwartzFourierLaplaceEvaluation z (thetaRealSchwartzComplexification f) := by
  rintro ⟨T, hT⟩
  have hIz : (Complex.I * z).re ≠ 0 := by
    simpa using hz
  apply not_exists_continuous_extension hIz
  refine ⟨fun f => T (thetaRealSchwartzComplexification f),
    (T.continuous.comp thetaRealSchwartzComplexification.continuous).continuousAt, ?_⟩
  intro f hf
  exact (hT f hf).trans (thetaSchwartzFourierLaplaceEvaluation_real z f)

/-- Every off-real exponential evaluation fails to extend to the actual tempered dual. -/
theorem thetaOffRealEvaluation_not_tempered (z : ℂ) (hz : z.im ≠ 0) :
    ¬ ∃ T : 𝓢'(ℝ, ℂ), ∀ f : 𝓢(ℝ, ℂ), thetaSchwartzExponentialDomain f →
      T f = thetaSchwartzFourierLaplaceEvaluation z f := by
  rintro ⟨T, hT⟩
  apply thetaOffRealEvaluation_not_tempered_real z hz
  refine ⟨T, fun f hf => ?_⟩
  exact hT _ (thetaRealSchwartzComplexification_mem_exponentialDomain f hf)

/-- The actual real-frequency tempered evaluator, with the exact physical normalization. -/
def thetaRealTemperedFourierEvaluation (t : ℝ) : 𝓢'(ℝ, ℂ) :=
  𝓕 (TemperedDistribution.delta (-t / (2 * Real.pi)))

/-- Every real evaluator equals its literal integral on all complex Schwartz functions. -/
theorem thetaRealTemperedFourierEvaluation_apply (t : ℝ) (f : 𝓢(ℝ, ℂ)) :
    thetaRealTemperedFourierEvaluation t f = thetaSchwartzFourierLaplaceEvaluation (t : ℂ) f := by
  rw [thetaRealTemperedFourierEvaluation, TemperedDistribution.fourier_apply,
    TemperedDistribution.delta_apply]
  change FourierTransform.fourier (f : ℝ → ℂ) (-t / (2 * Real.pi)) = _
  rw [Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards with x
  change Complex.exp (((-2 * Real.pi * x * (-t / (2 * Real.pi)) : ℝ) : ℂ) * Complex.I) * f x =
    Complex.exp ((Complex.I * (t : ℂ)) * (x : ℂ)) * f x
  congr 1
  congr 1
  push_cast
  field_simp [Real.pi_ne_zero]

/-- Exact positive boundary: a tempered extension exists precisely at real frequencies. -/
theorem exists_thetaTemperedFourierLaplaceEvaluation_iff (z : ℂ) :
    (∃ T : 𝓢'(ℝ, ℂ), ∀ f : 𝓢(ℝ, ℂ), thetaSchwartzExponentialDomain f →
      T f = thetaSchwartzFourierLaplaceEvaluation z f) ↔ z.im = 0 := by
  constructor
  · intro h
    by_contra hz
    exact thetaOffRealEvaluation_not_tempered z hz h
  · intro hz
    have hz' : z = (z.re : ℂ) := by
      apply Complex.ext <;> simp [hz]
    rw [hz']
    exact ⟨thetaRealTemperedFourierEvaluation z.re,
      fun f _ => thetaRealTemperedFourierEvaluation_apply z.re f⟩

end RHTower
