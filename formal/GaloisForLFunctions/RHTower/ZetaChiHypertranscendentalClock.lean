import GaloisForLFunctions.HTGeometry.GammaReflectionRatioClock
import GaloisForLFunctions.HTGeometry.FiniteAlgebraicStateBoundary
import GaloisForLFunctions.HTGeometry.FiniteGeneratorDifferentialEscape
import GaloisForLFunctions.HTGeometry.MeromorphicExponentialGaugeDA
import GaloisForLFunctions.HTGeometry.ExponentialObservationHypertranscendence
import GaloisForLFunctions.RHTower.ZetaCarrier
import GaloisForLFunctions.HTGeometry.UnivMeroFieldInstances

/-!
# The centered zeta archimedean factor is a hypertranscendental clock

In the centered coordinate `s = 1/2 + 2*w`, the completed zeta reflection factor satisfies

`zetaChi(s) = pi^(2*w) * Gamma(1/4-w) / Gamma(1/4+w)`.

The Gamma quotient is the reflected clock at center `1/4`.  Its two Euler-reflected translation
orbits differ by `1/2`, so the separated-center theorem makes its genuine global meromorphic
realization hypertranscendental.  Consequently this known archimedean clock cannot lie in any
derivation-closed finite-transcendence state field.

This result concerns the source-defined functional-equation factor only.  It neither constrains
the zeros of zeta nor supplies the positivity, contractivity, or prime-source estimate needed by
an RH criterion.
-/

open Filter Set Topology Function Complex
open scoped Differential

namespace RHTower

open GaloisForLFunctions Bottcher Polynomial

noncomputable section

open scoped UnivMeroFieldInstances

/-- Genuine meromorphic realization of the Gamma quotient in zeta's centered reflection clock. -/
def centeredZetaGammaReflectionMero : meroField Set.univ :=
  GaloisForLFunctions.gammaReflectionRatioMero (1 / 4 : ℂ)

/-- The centered zeta Gamma reflection clock is hypertranscendental because its two reflected
centers differ by the nonintegral amount `1/2`. -/
theorem hypertranscendentalOver_centeredZetaGammaReflectionMero :
    HypertranscendentalOver (RatFunc ℂ) centeredZetaGammaReflectionMero := by
  exact GaloisForLFunctions.hypertranscendentalOver_gammaReflectionRatioMero (1 / 4 : ℂ)

/-- **Positive state-complexity consequence.**  No derivation-closed finite-transcendence state
field can contain the centered archimedean Gamma reflection clock. -/
theorem not_finiteAlgebraicStateObservable_centeredZetaGammaReflectionMero :
    ¬ GaloisForLFunctions.HTGeometry.FiniteAlgebraicStateObservable
        (RatFunc ℂ) centeredZetaGammaReflectionMero :=
  GaloisForLFunctions.HTGeometry.not_finiteAlgebraicStateObservable_of_hypertranscendentalOver
    hypertranscendentalOver_centeredZetaGammaReflectionMero

/-- The complete centered archimedean zeta clock: the reflected Gamma quotient together with
the elementary `pi^(2*w)` exponential gauge. -/
def centeredZetaChiMero : meroField Set.univ :=
  centeredZetaGammaReflectionMero *
    GaloisForLFunctions.physicalExponentialMero
      (2 * Complex.log (Real.pi : ℂ))

/-- **Complete archimedean-clock classification.**  Restoring the `pi^(2*w)` gauge does not
remove the hypertranscendental source carried by the reflected Gamma quotient. -/
theorem hypertranscendentalOver_centeredZetaChiMero :
    HypertranscendentalOver (RatFunc ℂ) centeredZetaChiMero := by
  rw [centeredZetaChiMero,
    GaloisForLFunctions.HTGeometry.hypertranscendentalOver_mul_differentialAlgebraic_iff
      (GaloisForLFunctions.differentialAlgebraicOver_physicalExponentialMero
        (2 * Complex.log (Real.pi : ℂ)))
      (GaloisForLFunctions.physicalExponentialMero_ne_zero
        (2 * Complex.log (Real.pi : ℂ)))]
  exact hypertranscendentalOver_centeredZetaGammaReflectionMero

/-- The reciprocal completed archimedean clock is HT as well.  This is the meromorphic
observability form needed on the reflected side of the functional equation. -/
theorem hypertranscendentalOver_inv_centeredZetaChiMero :
    HypertranscendentalOver (RatFunc ℂ) (centeredZetaChiMero)⁻¹ :=
  GaloisForLFunctions.HTGeometry.hypertranscendentalOver_inv_iff.mpr
    hypertranscendentalOver_centeredZetaChiMero

/-- No derivation-closed finite-transcendence state field contains the reflected reciprocal
archimedean clock either. -/
theorem not_finiteAlgebraicStateObservable_inv_centeredZetaChiMero :
    ¬ GaloisForLFunctions.HTGeometry.FiniteAlgebraicStateObservable
        (RatFunc ℂ) (centeredZetaChiMero)⁻¹ :=
  GaloisForLFunctions.HTGeometry.not_finiteAlgebraicStateObservable_of_hypertranscendentalOver
    hypertranscendentalOver_inv_centeredZetaChiMero

/-- No derivation-closed finite-transcendence state field contains the complete centered zeta
archimedean clock. -/
theorem not_finiteAlgebraicStateObservable_centeredZetaChiMero :
    ¬ GaloisForLFunctions.HTGeometry.FiniteAlgebraicStateObservable
        (RatFunc ℂ) centeredZetaChiMero :=
  GaloisForLFunctions.HTGeometry.not_finiteAlgebraicStateObservable_of_hypertranscendentalOver
    hypertranscendentalOver_centeredZetaChiMero

/-- **Positive finite-generator escape for the reflected Gamma clock.**  Every finite rational
state packet containing the centered reflected clock loses closure under differentiation at one
of its chosen generators. -/
theorem exists_generator_deriv_escape_of_centeredZetaGammaReflectionMero
    {ι : Type*} [Fintype ι] (s : ι → meroField Set.univ)
    (hmem : centeredZetaGammaReflectionMero ∈
      IntermediateField.adjoin (RatFunc ℂ) (Set.range s)) :
    ∃ i, (s i)′ ∉ IntermediateField.adjoin (RatFunc ℂ) (Set.range s) :=
  GaloisForLFunctions.HTGeometry.exists_generator_deriv_escape_of_hypertranscendentalOver
    s hypertranscendentalOver_centeredZetaGammaReflectionMero hmem

/-- **Positive finite-generator escape for the complete archimedean clock.**  Any finite rational
state packet containing the exponential-dressed centered zeta clock has a generator derivative
outside that packet. -/
theorem exists_generator_deriv_escape_of_centeredZetaChiMero
    {ι : Type*} [Fintype ι] (s : ι → meroField Set.univ)
    (hmem : centeredZetaChiMero ∈
      IntermediateField.adjoin (RatFunc ℂ) (Set.range s)) :
    ∃ i, (s i)′ ∉ IntermediateField.adjoin (RatFunc ℂ) (Set.range s) :=
  GaloisForLFunctions.HTGeometry.exists_generator_deriv_escape_of_hypertranscendentalOver
    s hypertranscendentalOver_centeredZetaChiMero hmem

/-- The reciprocal complete archimedean clock forces the same finite-generator derivative escape
on the reflected side of the functional equation. -/
theorem exists_generator_deriv_escape_of_inv_centeredZetaChiMero
    {ι : Type*} [Fintype ι] (s : ι → meroField Set.univ)
    (hmem : (centeredZetaChiMero)⁻¹ ∈
      IntermediateField.adjoin (RatFunc ℂ) (Set.range s)) :
    ∃ i, (s i)′ ∉ IntermediateField.adjoin (RatFunc ℂ) (Set.range s) :=
  GaloisForLFunctions.HTGeometry.exists_generator_deriv_escape_of_hypertranscendentalOver
    s hypertranscendentalOver_inv_centeredZetaChiMero hmem

/-- Actual-function Gamma quotient in the centered zeta reflection coordinate. -/
def centeredZetaGammaReflectionValue (w : ℂ) : ℂ :=
  Complex.Gamma (1 / 4 - w) / Complex.Gamma (1 / 4 + w)

/-- Actual-function value of the complete centered archimedean clock. -/
def centeredZetaChiValue (w : ℂ) : ℂ :=
  centeredZetaGammaReflectionValue w *
    Complex.exp ((2 * Complex.log (Real.pi : ℂ)) * w)

/-- The power gauge in the completed zeta factor is exactly the pointwise exponential used by
the genuine meromorphic clock. -/
theorem pi_cpow_two_mul_eq_physicalExponentialValue (w : ℂ) :
    (Real.pi : ℂ) ^ (2 * w) =
      Complex.exp ((2 * Complex.log (Real.pi : ℂ)) * w) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [Complex.cpow_def_of_ne_zero hpi]
  congr 1
  ring

/-- **Exact centered value relation.**  Zeta's completed reflection factor is an elementary
exponential gauge times the hypertranscendental reflected Gamma clock. -/
theorem zetaChi_centered_eq (w : ℂ) :
    zetaChi (1 / 2 + 2 * w) =
      (Real.pi : ℂ) ^ (2 * w) * centeredZetaGammaReflectionValue w := by
  rw [zetaChi, Complex.Gammaℝ_def, Complex.Gammaℝ_def]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hfactor (A B G H : ℂ) :
      (A * G) / (B * H) = (A / B) * (G / H) := by
    simp [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [hfactor]
  have hpow :
      (Real.pi : ℂ) ^ (-(1 - (1 / 2 + 2 * w)) / 2) /
        (Real.pi : ℂ) ^ (-(1 / 2 + 2 * w) / 2) =
          (Real.pi : ℂ) ^ (2 * w) := by
    rw [← Complex.cpow_sub _ _ hpi]
    congr 1
    ring
  rw [hpow]
  simp only [centeredZetaGammaReflectionValue]
  congr 2 <;> ring

/-- The previously proved completed-factor identity is precisely evaluation of the complete
meromorphic exponential-dressed clock. -/
theorem zetaChi_centered_eq_centeredZetaChiValue (w : ℂ) :
    zetaChi (1 / 2 + 2 * w) = centeredZetaChiValue w := by
  rw [zetaChi_centered_eq, pi_cpow_two_mul_eq_physicalExponentialValue]
  simp [centeredZetaChiValue, mul_comm]

end

end RHTower
