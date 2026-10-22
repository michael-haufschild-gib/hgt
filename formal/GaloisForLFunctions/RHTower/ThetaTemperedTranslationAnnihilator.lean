import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspSchwartzTranslationCurve
import GaloisForLFunctions.RHTower.ThetaTemperedSourceJets
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Uniqueness

/-!
# Exact unscaled theta source jets and tempered translation annihilation

Every scalar orbit jet is the genuine spatial Schwartz jet. At zero it
is precisely the ordinary derivative of the original real theta source,
followed by complex postcomposition. Scalar analytic uniqueness on the
literal strip identifies its derivative annihilator with annihilation of
every literal real or complex-strip translate. Fourier-correlation and
the full supported-distribution classification remain separate results.
-/

open Filter Topology Set
open scoped SchwartzMap

noncomputable section

namespace RHTower

private theorem thetaRealParameter_mem_strip (a : ℝ) : (a : ℂ) ∈ thetaCuspStrip := by
  change |(a : ℂ).im| < Real.pi / 4
  simp only [Complex.ofReal_im, abs_zero]
  positivity

/-- Complex postcomposition commutes with the actual spatial Schwartz derivative. -/
theorem thetaSchwartzSpatialDeriv_ofReal (φ : 𝓢(ℝ, ℝ)) :
    SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.postcompCLM Complex.ofRealCLM φ) =
      SchwartzMap.postcompCLM Complex.ofRealCLM (SchwartzMap.derivCLM ℝ ℝ φ) := by
  ext x
  change deriv (fun y : ℝ => (φ y : ℂ)) x = ((deriv (φ : ℝ → ℝ) x : ℝ) : ℂ)
  exact (φ.hasDerivAt x).ofReal_comp.deriv

/-- Every actual complex-valued spatial jet retains the original real derivative. -/
theorem thetaSchwartzSpatialJetCLM_ofReal (n : ℕ) (φ : 𝓢(ℝ, ℝ)) :
    thetaSchwartzSpatialJetCLM n (SchwartzMap.postcompCLM Complex.ofRealCLM φ) =
      SchwartzMap.postcompCLM Complex.ofRealCLM ((SchwartzMap.derivCLM ℝ ℝ)^[n] φ) := by
  induction n generalizing φ with
  | zero => rfl
  | succ n ih =>
    change thetaSchwartzSpatialJetCLM n
      (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.postcompCLM Complex.ofRealCLM φ)) = _
    rw [thetaSchwartzSpatialDeriv_ofReal, ih, Function.iterate_succ_apply]

theorem thetaSchwartzSpatialJetCLM_thetaCuspSchwartz (n : ℕ) :
    thetaSchwartzSpatialJetCLM n thetaCuspSchwartz = thetaUnscaledSchwartzDerivative n :=
  thetaSchwartzSpatialJetCLM_ofReal n thetaCuspSchwartzReal

/-- The literal curve's source jets at zero are exactly the original ordinary derivatives. -/
theorem thetaSchwartzSpatialJetCLM_translationCurve_zero (n : ℕ) :
    thetaSchwartzSpatialJetCLM n (thetaCuspSchwartzTranslationCurve 0) =
      thetaUnscaledSchwartzDerivative n := by
  rw [thetaCuspSchwartzTranslationCurve_zero, thetaSchwartzSpatialJetCLM_thetaCuspSchwartz]

theorem thetaCuspSchwartzTranslationCurve_real_eq_schwartzTranslate (a : ℝ) :
    thetaCuspSchwartzTranslationCurve (a : ℂ) = MellinL2.schwartzTranslate a thetaCuspSchwartz := by
  ext x
  exact thetaCuspSchwartzTranslationCurve_real_apply a x

/-- Every scalar complex orbit derivative is its observer applied to the actual spatial jet. -/
theorem thetaCuspSchwartzTranslationCurve_observer_iteratedDeriv
    (T : 𝓢(ℝ, ℂ) →L[ℂ] ℂ) (n : ℕ) (a : ℂ) (ha : a ∈ thetaCuspStrip) :
    iteratedDeriv n (fun z => T (thetaCuspSchwartzTranslationCurve z)) a =
      T (thetaSchwartzSpatialJetCLM n (thetaCuspSchwartzTranslationCurve a)) := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv n (fun z => T (thetaCuspSchwartzTranslationCurve z)) =ᶠ[𝓝 a]
        (fun z => T (thetaSchwartzSpatialJetCLM n (thetaCuspSchwartzTranslationCurve z))) := by
      filter_upwards [isOpen_thetaCuspStrip.mem_nhds ha] with z hz
      exact ih z hz
    rw [he.deriv_eq]
    exact (thetaCuspSchwartzTranslationCurve_clm_hasDerivAt
      (T.comp (thetaSchwartzSpatialJetCLM n)) a ha).deriv

/-- The same exact source jets are derivatives of the literal real scalar restriction. -/
theorem thetaCuspSchwartzTranslationCurve_observer_real_iteratedDeriv
    (T : 𝓢(ℝ, ℂ) →L[ℂ] ℂ) (n : ℕ) (a : ℝ) :
    iteratedDeriv n (fun r : ℝ => T (thetaCuspSchwartzTranslationCurve (r : ℂ))) a =
      T (thetaSchwartzSpatialJetCLM n (thetaCuspSchwartzTranslationCurve (a : ℂ))) := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv n (fun r : ℝ => T (thetaCuspSchwartzTranslationCurve (r : ℂ))) =
        (fun r : ℝ => T (thetaSchwartzSpatialJetCLM n
          (thetaCuspSchwartzTranslationCurve (r : ℂ)))) := funext ih
    rw [he]
    exact (thetaCuspSchwartzTranslationCurve_clm_hasDerivAt
      (T.comp (thetaSchwartzSpatialJetCLM n)) (a : ℂ)
      (thetaRealParameter_mem_strip a)).comp_ofReal.deriv

theorem thetaCuspSchwartzTranslationCurve_observer_iteratedDeriv_zero
    (T : 𝓢(ℝ, ℂ) →L[ℂ] ℂ) (n : ℕ) :
    iteratedDeriv n (fun z => T (thetaCuspSchwartzTranslationCurve z)) 0 =
      T (thetaUnscaledSchwartzDerivative n) := by
  rw [thetaCuspSchwartzTranslationCurve_observer_iteratedDeriv T n 0
    (by simpa using thetaRealParameter_mem_strip 0),
    thetaSchwartzSpatialJetCLM_translationCurve_zero]

theorem thetaCuspSchwartzTranslationCurve_observer_real_iteratedDeriv_zero
    (T : 𝓢(ℝ, ℂ) →L[ℂ] ℂ) (n : ℕ) :
    iteratedDeriv n (fun r : ℝ => T (thetaCuspSchwartzTranslationCurve (r : ℂ))) 0 =
      T (thetaUnscaledSchwartzDerivative n) := by
  simpa only [Complex.ofReal_zero, thetaSchwartzSpatialJetCLM_translationCurve_zero] using
    thetaCuspSchwartzTranslationCurve_observer_real_iteratedDeriv T n 0

/-- Real translation vanishing already kills every ordinary unscaled source derivative. -/
theorem thetaUnscaledTemperedDerivativeAnnihilator_mem_of_realTranslates
    (T : 𝓢'(ℝ, ℂ))
    (hT : ∀ a : ℝ, T (thetaCuspSchwartzTranslationCurve (a : ℂ)) = 0) :
    T ∈ thetaUnscaledTemperedDerivativeAnnihilator := by
  apply (thetaUnscaledTemperedDerivativeAnnihilator_mem T).2
  intro n
  have hzero : (fun r : ℝ => (T : 𝓢(ℝ, ℂ) →L[ℂ] ℂ)
      (thetaCuspSchwartzTranslationCurve (r : ℂ))) =
      (fun _ : ℝ => (0 : ℂ)) := funext hT
  have hd := thetaCuspSchwartzTranslationCurve_observer_real_iteratedDeriv_zero T n
  exact hd.symm.trans ((congrArg (fun f : ℝ → ℂ => iteratedDeriv n f 0) hzero).trans
    iteratedDeriv_fun_const_zero)

/-- Exact ordinary-source annihilation is equivalent to vanishing on the entire literal strip. -/
theorem thetaUnscaledTemperedDerivativeAnnihilator_mem_iff_stripTranslates (T : 𝓢'(ℝ, ℂ)) :
    T ∈ thetaUnscaledTemperedDerivativeAnnihilator ↔
      ∀ a : ℂ, a ∈ thetaCuspStrip → T (thetaCuspSchwartzTranslationCurve a) = 0 := by
  constructor
  · intro hT
    have hjets : ∀ n : ℕ,
        iteratedDeriv n (fun z => T (thetaCuspSchwartzTranslationCurve z)) 0 = 0 := by
      intro n
      exact (thetaCuspSchwartzTranslationCurve_observer_iteratedDeriv_zero T n).trans
        ((thetaUnscaledTemperedDerivativeAnnihilator_mem T).1 hT n)
    have ha := thetaCuspSchwartzTranslationCurve_observer_analyticOnNhd T
    have h0 : (0 : ℂ) ∈ thetaCuspStrip := by simpa using thetaRealParameter_mem_strip 0
    have hord : analyticOrderAt (fun z => T (thetaCuspSchwartzTranslationCurve z)) 0 = ⊤ := by
      by_contra hn
      have hnat : analyticOrderAt (fun z => T (thetaCuspSchwartzTranslationCurve z)) 0 =
          ↑(analyticOrderAt (fun z => T (thetaCuspSchwartzTranslationCurve z)) 0).toNat :=
        (ENat.coe_toNat hn).symm
      exact ((analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero (ha 0 h0)).1 hnat).2 (hjets _)
    have hnear : (fun z => T (thetaCuspSchwartzTranslationCurve z)) =ᶠ[𝓝 (0 : ℂ)] 0 :=
      analyticOrderAt_eq_top.1 hord
    exact ha.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_thetaCuspStrip h0 hnear
  · intro hT
    exact thetaUnscaledTemperedDerivativeAnnihilator_mem_of_realTranslates T
      (fun a => hT (a : ℂ) (thetaRealParameter_mem_strip a))

theorem thetaUnscaledTemperedDerivativeAnnihilator_mem_iff_realTranslates (T : 𝓢'(ℝ, ℂ)) :
    T ∈ thetaUnscaledTemperedDerivativeAnnihilator ↔
      ∀ a : ℝ, T (thetaCuspSchwartzTranslationCurve (a : ℂ)) = 0 := by
  constructor
  · intro hT a
    exact (thetaUnscaledTemperedDerivativeAnnihilator_mem_iff_stripTranslates T).1 hT
      (a : ℂ) (thetaRealParameter_mem_strip a)
  · exact thetaUnscaledTemperedDerivativeAnnihilator_mem_of_realTranslates T

/-- The original unscaled derivative annihilator is precisely its actual Schwartz translation annihilator. -/
theorem thetaUnscaledTemperedDerivativeAnnihilator_mem_iff_schwartzTranslates (T : 𝓢'(ℝ, ℂ)) :
    T ∈ thetaUnscaledTemperedDerivativeAnnihilator ↔
      ∀ a : ℝ, T (MellinL2.schwartzTranslate a thetaCuspSchwartz) = 0 := by
  simpa only [thetaCuspSchwartzTranslationCurve_real_eq_schwartzTranslate] using
    thetaUnscaledTemperedDerivativeAnnihilator_mem_iff_realTranslates T

end RHTower
