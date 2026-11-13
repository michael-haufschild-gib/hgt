import GaloisForLFunctions.HTGeometry.GammaReflectionRatioClock
import GaloisForLFunctions.RHTower.UnitModulusL2Multiplier

/-!
# The signed-Beta Gamma factor as a reflection clock

The one-variable factor in Li--Liu's signed-Beta factorization is
`X₁(s) = Γ((3/2-s)/2) / Γ((3/2+s)/2)`.
After `s=2t`, it is the existing Gamma reflection clock at center `3/4`.
Its imaginary-axis modulus is one, although its meromorphic differential
class is hypertranscendental. Multiplication by the axis factor preserves
every pointwise spectral magnitude.
-/

open Set Complex
open scoped Differential

namespace GaloisForLFunctions.Goldbach

open Bottcher
open scoped UnivMeroFieldInstances

noncomputable section

/-- The literal Gamma quotient in the signed-Beta factorization. -/
def signedBetaGammaFactor (s : ℂ) : ℂ :=
  Complex.Gamma ((3 / 2 - s) / 2) / Complex.Gamma ((3 / 2 + s) / 2)

/-- Rescaling the argument exposes the reflected Gamma pair. -/
theorem signedBetaGammaFactor_twice (t : ℂ) :
    signedBetaGammaFactor (2 * t) =
      Complex.Gamma (-t + 3 / 4) / Complex.Gamma (t + 3 / 4) := by
  unfold signedBetaGammaFactor
  congr 2 <;> ring

/-- Reflection in the argument inverts the scalar quotient, including its totalized values. -/
theorem signedBetaGammaFactor_neg (s : ℂ) :
    signedBetaGammaFactor (-s) = (signedBetaGammaFactor s)⁻¹ := by
  simp only [signedBetaGammaFactor, sub_neg_eq_add, ← sub_eq_add_neg, inv_div]

/-- The Gamma quotient is unimodular on the entire imaginary axis. -/
theorem norm_signedBetaGammaFactor_axis (t : ℝ) :
    ‖signedBetaGammaFactor ((t : ℂ) * I)‖ = 1 := by
  have hc : (3 / 2 - (t : ℂ) * I) / 2 =
      (starRingEnd ℂ) ((3 / 2 + (t : ℂ) * I) / 2) := by
    simp only [map_div₀, map_add, map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
    ring
  have hn : Complex.Gamma ((3 / 2 + (t : ℂ) * I) / 2) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by norm_num)
  rw [signedBetaGammaFactor, hc, Complex.Gamma_conj, norm_div, RCLike.norm_conj,
    div_self (norm_ne_zero_iff.mpr hn)]

/-- The factor changes spectral phase while preserving arbitrary spectral magnitudes. -/
theorem signedBetaGammaFactor_axis_mul_norm (t : ℝ) (z : ℂ) :
    ‖signedBetaGammaFactor ((t : ℂ) * I) * z‖ = ‖z‖ := by
  rw [norm_mul, norm_signedBetaGammaFactor_axis, one_mul]

/-- The Gamma phase is measurable on the whole imaginary axis. -/
theorem measurable_signedBetaGammaFactor_axis :
    Measurable (fun t : ℝ => signedBetaGammaFactor ((t : ℂ) * I)) := by
  have hg : Measurable Complex.Gamma := by
    have he : (fun z : ℂ => (reciprocalGammaEntire z)⁻¹) = Complex.Gamma := by
      funext z
      simp only [reciprocalGammaEntire, inv_inv]
    rw [← he]
    exact contDiff_reciprocalGammaEntire.continuous.measurable.inv
  exact (hg.comp (by fun_prop)).div (hg.comp (by fun_prop))

/-- The literal signed-Beta factor gives a phase for every measure on the real axis. -/
def signedBetaGammaPhase (ν : MeasureTheory.Measure ℝ) :
    RHTower.UnitModulusL2Phase ℝ ν where
  toFun t := signedBetaGammaFactor ((t : ℂ) * I)
  aestronglyMeasurable := measurable_signedBetaGammaFactor_axis.aestronglyMeasurable
  norm_eq_one := Filter.Eventually.of_forall norm_signedBetaGammaFactor_axis

/-- Multiplication by the signed-Beta factor is an onto isometry of the spectral `L²` space. -/
def signedBetaGammaUnitary (ν : MeasureTheory.Measure ℝ) :
    MeasureTheory.Lp ℂ 2 ν ≃ₗᵢ[ℂ] MeasureTheory.Lp ℂ 2 ν :=
  (signedBetaGammaPhase ν).mulUnitary

/-- The unitary acts by the literal Gamma quotient almost everywhere. -/
theorem signedBetaGammaUnitary_ae (ν : MeasureTheory.Measure ℝ)
    (f : MeasureTheory.Lp ℂ 2 ν) :
    signedBetaGammaUnitary ν f =ᵐ[ν]
      fun t => signedBetaGammaFactor ((t : ℂ) * I) * f t :=
  (signedBetaGammaPhase ν).mulUnitary_ae f

/-- Every spectral `L²` norm is preserved by the Gamma factor. -/
theorem norm_signedBetaGammaUnitary (ν : MeasureTheory.Measure ℝ)
    (f : MeasureTheory.Lp ℂ 2 ν) : ‖signedBetaGammaUnitary ν f‖ = ‖f‖ :=
  (signedBetaGammaUnitary ν).norm_map f

/-- The global meromorphic element representing `X₁(2t)`. -/
def signedBetaGammaFactorMero : meroField Set.univ := gammaReflectionRatioMero (3 / 4)

/-- The rescaled Gamma factor has no algebraic differential equation over `ℂ(t)`. -/
theorem hypertranscendentalOver_signedBetaGammaFactorMero :
    HypertranscendentalOver (RatFunc ℂ) signedBetaGammaFactorMero :=
  hypertranscendentalOver_gammaReflectionRatioMero (3 / 4)

/-- Euler reflection exhibits two reciprocal Gamma factors and a sine gauge. -/
theorem signedBetaGammaFactorMero_reflection :
    signedBetaGammaFactorMero = gammaReflectionGaugeMero (3 / 4) /
      (gammaShiftMero (1 / 4) * gammaShiftMero (3 / 4)) := by
  rw [signedBetaGammaFactorMero, gammaReflectionRatioMero, gammaNegativeShiftMero_reflection]
  norm_num only [show (1 : ℂ) - 3 / 4 = 1 / 4 by norm_num]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

end

end GaloisForLFunctions.Goldbach

-- Temporary dependency audit.
#print axioms GaloisForLFunctions.Goldbach.signedBetaGammaFactor
#print axioms GaloisForLFunctions.Goldbach.signedBetaGammaFactor_twice
#print axioms GaloisForLFunctions.Goldbach.signedBetaGammaFactor_neg
#print axioms GaloisForLFunctions.Goldbach.norm_signedBetaGammaFactor_axis
#print axioms GaloisForLFunctions.Goldbach.signedBetaGammaFactor_axis_mul_norm
#print axioms GaloisForLFunctions.Goldbach.measurable_signedBetaGammaFactor_axis
#print axioms GaloisForLFunctions.Goldbach.signedBetaGammaPhase
#print axioms GaloisForLFunctions.Goldbach.signedBetaGammaUnitary
#print axioms GaloisForLFunctions.Goldbach.signedBetaGammaUnitary_ae
#print axioms GaloisForLFunctions.Goldbach.norm_signedBetaGammaUnitary
#print axioms GaloisForLFunctions.Goldbach.signedBetaGammaFactorMero
#print axioms GaloisForLFunctions.Goldbach.hypertranscendentalOver_signedBetaGammaFactorMero
#print axioms GaloisForLFunctions.Goldbach.signedBetaGammaFactorMero_reflection
