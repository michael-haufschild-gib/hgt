import GaloisForLFunctions.HTGeometry.HermiteOrthogonality
import GaloisForLFunctions.HTGeometry.SchwartzPolynomialDifferentialFrame
import GaloisForLFunctions.HTGeometry.TwoChannelRobertson

/-!
# Canonical commutation and Robertson mechanics on Schwartz space

The pointwise commutators already used by the Hermite corpus are promoted to unconditional
operator equalities. Physical position and momentum satisfy `[X,P]=iI`; creation and annihilation
satisfy their exact oscillator CCR. The three-vector Robertson determinant is then applied to the
state, position channel, and momentum channel in `L²(ℝ)`.
-/

open scoped Real FourierTransform SchwartzMap InnerProductSpace
open Complex MeasureTheory

noncomputable section

namespace GaloisForLFunctions

/-- Differentiation and coordinate multiplication satisfy `[D,X]=I` on Schwartz space. -/
theorem schwartz_derivative_position_operatorCCR :
    derivSCLM * mulXCLM - mulXCLM * derivSCLM =
      (1 : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ)) := by
  apply ContinuousLinearMap.ext
  intro f
  change derivSCLM (mulXCLM f) - mulXCLM (derivSCLM f) = f
  rw [derivSCLM_mulXCLM]
  module

/-- Physical position and momentum `P=-iD` satisfy `[X,P]=iI` on Schwartz space. -/
theorem schwartz_position_momentum_operatorCCR :
    mulXCLM * SchwartzMap.momentumCLM - SchwartzMap.momentumCLM * mulXCLM =
      Complex.I • (1 : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ)) := by
  apply ContinuousLinearMap.ext
  intro f
  change mulXCLM ((-Complex.I) • derivSCLM f) -
      (-Complex.I) • derivSCLM (mulXCLM f) = Complex.I • f
  rw [map_smul, derivSCLM_mulXCLM]
  module

/-- Creation and annihilation satisfy the exact operator CCR `[B,A]=4πI`. -/
theorem schwartz_oscillator_operatorCCR :
    annihilationCLM * creationCLM - creationCLM * annihilationCLM =
      (4 * (Real.pi : ℂ)) • (1 : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ)) := by
  apply ContinuousLinearMap.ext
  intro f
  change annihilationCLM (creationCLM f) - creationCLM (annihilationCLM f) =
    (4 * (Real.pi : ℂ)) • f
  exact annihilationCLM_creationCLM_sub f

/-- Two-channel Robertson determinant for a Schwartz state and its position/momentum responses. -/
theorem schwartz_position_momentum_twoChannelRobertson (f : 𝓢(ℝ, ℂ)) :
    inner ℝ (f.toLp 2 (volume : Measure ℝ)) ((mulXCLM f).toLp 2 volume) ^ (2 : ℕ) *
          inner ℝ ((SchwartzMap.momentumCLM f).toLp 2 volume)
            ((SchwartzMap.momentumCLM f).toLp 2 volume) -
        2 * inner ℝ (f.toLp 2 volume) ((mulXCLM f).toLp 2 volume) *
          inner ℝ (f.toLp 2 volume) ((SchwartzMap.momentumCLM f).toLp 2 volume) *
          inner ℝ ((mulXCLM f).toLp 2 volume)
            ((SchwartzMap.momentumCLM f).toLp 2 volume) +
        inner ℝ (f.toLp 2 volume) ((SchwartzMap.momentumCLM f).toLp 2 volume) ^ (2 : ℕ) *
          inner ℝ ((mulXCLM f).toLp 2 volume) ((mulXCLM f).toLp 2 volume) ≤
      inner ℝ (f.toLp 2 volume) (f.toLp 2 volume) *
        (inner ℝ ((mulXCLM f).toLp 2 volume) ((mulXCLM f).toLp 2 volume) *
            inner ℝ ((SchwartzMap.momentumCLM f).toLp 2 volume)
              ((SchwartzMap.momentumCLM f).toLp 2 volume) -
          inner ℝ ((mulXCLM f).toLp 2 volume)
              ((SchwartzMap.momentumCLM f).toLp 2 volume) ^ (2 : ℕ)) :=
  HTGeometry.twoChannelRobertsonGram
    (f.toLp 2 (volume : Measure ℝ))
    ((mulXCLM f).toLp 2 volume)
    ((SchwartzMap.momentumCLM f).toLp 2 volume)

end GaloisForLFunctions
