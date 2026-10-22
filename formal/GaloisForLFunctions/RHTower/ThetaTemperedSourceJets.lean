import GaloisForLFunctions.RHTower.ThetaTemperedMultiplicityJets
import GaloisForLFunctions.RHTower.ThetaTemperedEvaluationBoundary
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaDerivativeHistoryFourier

/-!
# Actual tempered multiplicity jets for the unscaled theta source

The physical Fourier map is the invertible Schwartz map
`φ ↦ (t ↦ F_mathlib φ (-t/(2π)))`. Its continuous tempered pullback
transports every actual real Dirac derivative. All lower Xi-multiplicity
jets annihilate every ordinary derivative of the original unscaled source;
the first excluded jet survives on that source itself. The full supported-
distribution converse is a separate obligation.
-/

open MeasureTheory Set Filter Topology
open scoped SchwartzMap FourierTransform

noncomputable section

namespace RHTower

/-- Exact real frequency change for the physical positive-phase Fourier transform. -/
def thetaPhysicalFrequencyChange : ℝ ≃L[ℝ] ℝ :=
  ContinuousLinearEquiv.equivOfInverse
    (-(2 * Real.pi)⁻¹ • ContinuousLinearMap.id ℝ ℝ)
    (-(2 * Real.pi) • ContinuousLinearMap.id ℝ ℝ)
    (by
      intro x
      change -(2 * Real.pi) * (-(2 * Real.pi)⁻¹ * x) = x
      field_simp [Real.pi_ne_zero])
    (by
      intro x
      change -(2 * Real.pi)⁻¹ * (-(2 * Real.pi) * x) = x
      field_simp [Real.pi_ne_zero])

theorem thetaPhysicalFrequencyChange_apply (t : ℝ) :
    thetaPhysicalFrequencyChange t = -t / (2 * Real.pi) := by
  change -(2 * Real.pi)⁻¹ * t = -t / (2 * Real.pi)
  ring

theorem thetaPhysicalFrequencyChange_symm_apply (t : ℝ) :
    thetaPhysicalFrequencyChange.symm t = -(2 * Real.pi) * t := rfl

/-- Frequency composition, including its actual continuous inverse. -/
def thetaPhysicalFrequencyCompositionCLE : 𝓢(ℝ, ℂ) ≃L[ℂ] 𝓢(ℝ, ℂ) :=
  ContinuousLinearEquiv.equivOfInverse
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ thetaPhysicalFrequencyChange)
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ thetaPhysicalFrequencyChange.symm)
    (by
      intro φ
      ext t
      change φ (thetaPhysicalFrequencyChange (thetaPhysicalFrequencyChange.symm t)) = φ t
      rw [thetaPhysicalFrequencyChange.apply_symm_apply])
    (by
      intro φ
      ext t
      change φ (thetaPhysicalFrequencyChange.symm (thetaPhysicalFrequencyChange t)) = φ t
      rw [thetaPhysicalFrequencyChange.symm_apply_apply])

theorem thetaPhysicalFrequencyCompositionCLE_apply (φ : 𝓢(ℝ, ℂ)) (t : ℝ) :
    thetaPhysicalFrequencyCompositionCLE φ t = φ (-t / (2 * Real.pi)) := by
  change φ (thetaPhysicalFrequencyChange t) = _
  rw [thetaPhysicalFrequencyChange_apply]

/-- The literal unscaled physical Fourier map on the actual Schwartz space. -/
def thetaPhysicalFourierCLE : 𝓢(ℝ, ℂ) ≃L[ℂ] 𝓢(ℝ, ℂ) :=
  (FourierTransform.fourierCLE ℂ 𝓢(ℝ, ℂ)).trans thetaPhysicalFrequencyCompositionCLE

theorem thetaPhysicalFourierCLE_apply (φ : 𝓢(ℝ, ℂ)) (t : ℝ) :
    thetaPhysicalFourierCLE φ t = (𝓕 φ) (-t / (2 * Real.pi)) := by
  change thetaPhysicalFrequencyCompositionCLE (𝓕 φ) t = _
  exact thetaPhysicalFrequencyCompositionCLE_apply (𝓕 φ) t

theorem thetaPhysicalFourierCLE_apply_eq_integral (φ : 𝓢(ℝ, ℂ)) (t : ℝ) :
    thetaPhysicalFourierCLE φ t = thetaSchwartzFourierLaplaceEvaluation (t : ℂ) φ := by
  rw [thetaPhysicalFourierCLE_apply]
  exact thetaRealTemperedFourierEvaluation_apply t φ

/-- Continuous pullback of actual tempered distributions through the physical Fourier map. -/
def thetaPhysicalTemperedPullback : 𝓢'(ℝ, ℂ) →L[ℂ] 𝓢'(ℝ, ℂ) :=
  PointwiseConvergenceCLM.precomp ℂ thetaPhysicalFourierCLE.toContinuousLinearMap

theorem thetaPhysicalTemperedPullback_apply (T : 𝓢'(ℝ, ℂ)) (φ : 𝓢(ℝ, ℂ)) :
    thetaPhysicalTemperedPullback T φ = T (thetaPhysicalFourierCLE φ) := rfl

theorem thetaPhysicalTemperedPullback_injective :
    Function.Injective thetaPhysicalTemperedPullback := by
  intro T Q h
  ext φ
  have hh := congrArg (fun R : 𝓢'(ℝ, ℂ) => R (thetaPhysicalFourierCLE.symm φ)) h
  simpa only [thetaPhysicalTemperedPullback_apply,
    thetaPhysicalFourierCLE.apply_symm_apply] using hh

private theorem thetaRealSchwartzIteratedDerivative_apply
    (n : ℕ) (φ : 𝓢(ℝ, ℝ)) (x : ℝ) :
    ((SchwartzMap.derivCLM ℝ ℝ)^[n] φ) x = iteratedDeriv n (φ : ℝ → ℝ) x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', SchwartzMap.derivCLM_apply, iteratedDeriv_succ]
    have he : (((SchwartzMap.derivCLM ℝ ℝ)^[n] φ) : ℝ → ℝ) =
        iteratedDeriv n (φ : ℝ → ℝ) := funext ih
    rw [he]

/-- Every ordinary derivative of the original unscaled source, as an actual Schwartz function. -/
def thetaUnscaledSchwartzDerivative (n : ℕ) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.postcompCLM Complex.ofRealCLM
    ((SchwartzMap.derivCLM ℝ ℝ)^[n] thetaCuspSchwartzReal)

theorem thetaUnscaledSchwartzDerivative_apply (n : ℕ) (x : ℝ) :
    thetaUnscaledSchwartzDerivative n x = ((iteratedDeriv n thetaCuspFullSource x : ℝ) : ℂ) := by
  rw [thetaUnscaledSchwartzDerivative, SchwartzMap.postcompCLM_apply,
    thetaRealSchwartzIteratedDerivative_apply]
  rfl

theorem thetaUnscaledSchwartzDerivative_zero :
    thetaUnscaledSchwartzDerivative 0 = thetaCuspSchwartz := rfl

/-- Exact physical transform of every literal ordinary source derivative. -/
theorem thetaPhysicalFourierCLE_sourceDerivative (n : ℕ) (t : ℝ) :
    thetaPhysicalFourierCLE (thetaUnscaledSchwartzDerivative n) t =
      (-Complex.I * (t : ℂ)) ^ n * XiC (t : ℂ) := by
  rw [thetaPhysicalFourierCLE_apply_eq_integral]
  change (∫ x : ℝ, Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) *
    thetaUnscaledSchwartzDerivative n x) = _
  calc
    _ = ∫ x : ℝ, ((iteratedDeriv n thetaCuspFullSource x : ℝ) : ℂ) *
        Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) := by
      apply integral_congr_ae
      filter_upwards with x
      rw [thetaUnscaledSchwartzDerivative_apply, mul_comm]
    _ = _ := HedenmalmThetaSource.thetaSourceDerivativeFourierIntegral (t : ℂ) n

theorem thetaPhysicalFourierCLE_source :
    (thetaPhysicalFourierCLE thetaCuspSchwartz : ℝ → ℂ) = thetaXiRealSymbol := by
  funext t
  simpa only [thetaUnscaledSchwartzDerivative_zero, pow_zero, one_mul,
    thetaXiRealSymbol] using thetaPhysicalFourierCLE_sourceDerivative 0 t

/-- The literal physical pullback of an actual real spectral Dirac derivative. -/
def thetaPhysicalTemperedDiracJet (t : ℝ) (r : ℕ) : 𝓢'(ℝ, ℂ) :=
  thetaPhysicalTemperedPullback (thetaRealDiracJet t r)

theorem thetaPhysicalTemperedDiracJet_apply (t : ℝ) (r : ℕ) (φ : 𝓢(ℝ, ℂ)) :
    thetaPhysicalTemperedDiracJet t r φ =
      (-1 : ℂ) ^ r * iteratedDeriv r (thetaPhysicalFourierCLE φ : ℝ → ℂ) t := by
  rw [thetaPhysicalTemperedDiracJet, thetaPhysicalTemperedPullback_apply,
    thetaRealDiracJet_apply]

theorem thetaPhysicalTemperedDiracJet_zero (t : ℝ) :
    thetaPhysicalTemperedDiracJet t 0 = thetaRealTemperedFourierEvaluation t := by
  ext φ
  rw [thetaPhysicalTemperedDiracJet_apply]
  simp only [pow_zero, iteratedDeriv_zero, one_mul]
  exact (thetaPhysicalFourierCLE_apply_eq_integral φ t).trans
    (thetaRealTemperedFourierEvaluation_apply t φ).symm

theorem thetaPhysicalTemperedDiracJet_ne_zero (t : ℝ) (r : ℕ) :
    thetaPhysicalTemperedDiracJet t r ≠ 0 := by
  intro h
  have hh : thetaRealDiracJet t r = 0 :=
    thetaPhysicalTemperedPullback_injective
      (h.trans (thetaPhysicalTemperedPullback.map_zero).symm)
  exact thetaRealDiracJet_ne_zero t r hh

theorem thetaPhysicalTemperedDiracJet_fin_linearIndependent (t : ℝ) (N : ℕ) :
    LinearIndependent ℂ (fun r : Fin N => thetaPhysicalTemperedDiracJet t r) := by
  exact (thetaRealDiracJet_fin_linearIndependent t N).map'
    thetaPhysicalTemperedPullback.toLinearMap
    (LinearMap.ker_eq_bot.mpr thetaPhysicalTemperedPullback_injective)

/-- Annihilator of every actual ordinary derivative of the original unscaled theta source. -/
def thetaUnscaledTemperedDerivativeAnnihilator : Submodule ℂ 𝓢'(ℝ, ℂ) where
  carrier := {T | ∀ n : ℕ, T (thetaUnscaledSchwartzDerivative n) = 0}
  zero_mem' := by intro n; rfl
  add_mem' := by
    intro T Q hT hQ n
    change T (thetaUnscaledSchwartzDerivative n) + Q (thetaUnscaledSchwartzDerivative n) = 0
    rw [hT n, hQ n, add_zero]
  smul_mem' := by
    intro c T hT n
    change c * T (thetaUnscaledSchwartzDerivative n) = 0
    rw [hT n, mul_zero]

theorem thetaUnscaledTemperedDerivativeAnnihilator_mem (T : 𝓢'(ℝ, ℂ)) :
    T ∈ thetaUnscaledTemperedDerivativeAnnihilator ↔
      ∀ n : ℕ, T (thetaUnscaledSchwartzDerivative n) = 0 := Iff.rfl

/-- All lower actual multiplicity jets annihilate every literal source derivative. -/
theorem thetaPhysicalTemperedDiracJet_sourceDerivative_eq_zero
    (t : ℝ) {r : ℕ} (hr : r < thetaRealXiMultiplicity t) (n : ℕ) :
    thetaPhysicalTemperedDiracJet t r (thetaUnscaledSchwartzDerivative n) = 0 := by
  rw [thetaPhysicalTemperedDiracJet_apply]
  have he : (thetaPhysicalFourierCLE (thetaUnscaledSchwartzDerivative n) : ℝ → ℂ) =
      (fun x : ℝ => (-Complex.I * (x : ℂ)) ^ n * thetaXiRealSymbol x) := by
    funext x
    exact thetaPhysicalFourierCLE_sourceDerivative n x
  rw [he]
  have hp : ContDiff ℝ r (fun x : ℝ => (-Complex.I * (x : ℂ)) ^ n) :=
    (contDiff_const.mul Complex.ofRealCLM.contDiff).pow n
  have hXi : ContDiff ℝ r thetaXiRealSymbol := by
    rw [thetaXiRealSymbol_eq_coeSchwartz]
    exact thetaXiSchwartzSymbol.smooth r
  have hz : iteratedDeriv r
      (fun x : ℝ => (-Complex.I * (x : ℂ)) ^ n * thetaXiRealSymbol x) t = 0 := by
    change iteratedDeriv r
      ((fun x : ℝ => (-Complex.I * (x : ℂ)) ^ n) * thetaXiRealSymbol) t = 0
    rw [iteratedDeriv_mul hp.contDiffAt hXi.contDiffAt]
    apply Finset.sum_eq_zero
    intro j hj
    have horder : r - j < thetaRealXiMultiplicity t := by omega
    rw [thetaXiRealSymbol_iteratedDeriv,
      thetaXiComplexJet_vanish_below_multiplicity t horder, mul_zero]
  rw [hz, mul_zero]

theorem thetaPhysicalTemperedDiracJet_mem_annihilator
    (t : ℝ) {r : ℕ} (hr : r < thetaRealXiMultiplicity t) :
    thetaPhysicalTemperedDiracJet t r ∈ thetaUnscaledTemperedDerivativeAnnihilator :=
  thetaPhysicalTemperedDiracJet_sourceDerivative_eq_zero t hr

/-- The first excluded physical jet survives on the original unscaled source itself. -/
theorem thetaPhysicalTemperedDiracJet_at_multiplicity_source_ne_zero (t : ℝ) :
    thetaPhysicalTemperedDiracJet t (thetaRealXiMultiplicity t) thetaCuspSchwartz ≠ 0 := by
  rw [thetaPhysicalTemperedDiracJet_apply, thetaPhysicalFourierCLE_source,
    thetaXiRealSymbol_iteratedDeriv]
  exact mul_ne_zero (pow_ne_zero _ (by norm_num))
    (thetaXiComplexJet_ne_zero_at_multiplicity t)

/-- The actual physical source annihilator jets below the actual real Xi multiplicity. -/
def thetaPhysicalTemperedLowerJetSpan (t : ℝ) : Submodule ℂ 𝓢'(ℝ, ℂ) :=
  Submodule.span ℂ (Set.range (fun r : Fin (thetaRealXiMultiplicity t) =>
    thetaPhysicalTemperedDiracJet t r))

theorem thetaPhysicalTemperedLowerJetSpan_le_annihilator (t : ℝ) :
    thetaPhysicalTemperedLowerJetSpan t ≤ thetaUnscaledTemperedDerivativeAnnihilator := by
  apply Submodule.span_le.mpr
  rintro T ⟨r, rfl⟩
  exact thetaPhysicalTemperedDiracJet_mem_annihilator t r.isLt

theorem thetaPhysicalTemperedLowerJetSpan_finrank (t : ℝ) :
    Module.finrank ℂ (thetaPhysicalTemperedLowerJetSpan t) = thetaRealXiMultiplicity t := by
  change Module.finrank ℂ (Submodule.span ℂ (Set.range
    (fun r : Fin (thetaRealXiMultiplicity t) => thetaPhysicalTemperedDiracJet t r))) = _
  rw [finrank_span_eq_card (thetaPhysicalTemperedDiracJet_fin_linearIndependent t _)]
  exact Fintype.card_fin _

end RHTower
