import GaloisForLFunctions.RHTower.CCMThetaSignedLocalizationWitness
import GaloisForLFunctions.RHTower.CCMFarGapPhaseCoercivity

/-!
# Exact finite localization chains

At each smooth angle, the sine channel is retained and the cosine channel
continues to the next split. Physical mass is conserved exactly. The complete
Weil energy telescopes with separate, signed prime and continuous errors.
-/

noncomputable section

open MeasureTheory Set
open scoped SchwartzMap

namespace RHTower

def ccmLocalizationRemainder {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) : List 𝓢(ℝ, ℝ) → CCMComplexSmoothInteriorSource a
  | [] => u
  | theta :: rest => ccmLocalizationRemainder (ccmCosLocalizedSource u theta) rest

def ccmLocalizationPieces {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) : List 𝓢(ℝ, ℝ) → List (CCMComplexSmoothInteriorSource a)
  | [] => []
  | theta :: rest => ccmSinLocalizedSource u theta ::
      ccmLocalizationPieces (ccmCosLocalizedSource u theta) rest

def ccmLocalizationPrimeTotal {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) : List 𝓢(ℝ, ℝ) → ℝ
  | [] => 0
  | theta :: rest => ccmThetaPrimeLocalizationError u theta +
      ccmLocalizationPrimeTotal (ccmCosLocalizedSource u theta) rest

def ccmLocalizationContinuousTotal {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) : List 𝓢(ℝ, ℝ) → ℝ
  | [] => 0
  | theta :: rest => ccmThetaContinuousLocalizationError u theta +
      ccmLocalizationContinuousTotal (ccmCosLocalizedSource u theta) rest

theorem ccmLocalization_mass_conservation {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (angles : List 𝓢(ℝ, ℝ)) :
    ‖ccmArchimedeanFormEmbedding a (ccmLocalizationRemainder u angles).toCCMFormVector‖ ^ 2 +
      ((ccmLocalizationPieces u angles).map
        (fun v => ‖ccmArchimedeanFormEmbedding a v.toCCMFormVector‖ ^ 2)).sum =
      ‖ccmArchimedeanFormEmbedding a u.toCCMFormVector‖ ^ 2 := by
  induction angles generalizing u with
  | nil => simp only [ccmLocalizationRemainder, ccmLocalizationPieces, List.map_nil,
      List.sum_nil, add_zero]
  | cons theta rest ih =>
    have h := ccmPhysicalMass_localization u theta
    change ‖ccmArchimedeanFormEmbedding a (ccmCosLocalizedSource u theta).toCCMFormVector‖ ^ 2 +
      ‖ccmArchimedeanFormEmbedding a (ccmSinLocalizedSource u theta).toCCMFormVector‖ ^ 2 =
      ‖ccmArchimedeanFormEmbedding a u.toCCMFormVector‖ ^ 2 at h
    have hi := ih (ccmCosLocalizedSource u theta)
    simp only [ccmLocalizationRemainder, ccmLocalizationPieces, List.map_cons, List.sum_cons]
    linarith only [h, hi]

theorem ccmLocalization_energy_conservation {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (angles : List 𝓢(ℝ, ℝ)) :
    ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector =
      ccmRestrictedWeilSourceQuadratic a (ccmLocalizationRemainder u angles).toCCMFormVector +
      ((ccmLocalizationPieces u angles).map
        (fun v => ccmRestrictedWeilSourceQuadratic a v.toCCMFormVector)).sum -
      ccmLocalizationPrimeTotal u angles + ccmLocalizationContinuousTotal u angles := by
  induction angles generalizing u with
  | nil => simp only [ccmLocalizationRemainder, ccmLocalizationPieces,
      ccmLocalizationPrimeTotal, ccmLocalizationContinuousTotal, List.map_nil, List.sum_nil,
      add_zero, sub_zero]
  | cons theta rest ih =>
    have h := ccmRestrictedWeilSourceQuadratic_localization u theta
    have hi := ih (ccmCosLocalizedSource u theta)
    simp only [ccmLocalizationRemainder, ccmLocalizationPieces, ccmLocalizationPrimeTotal,
      ccmLocalizationContinuousTotal, List.map_cons, List.sum_cons]
    linarith only [h, hi]

theorem ccmLocalizationRemainder_apply_eq_zero {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (angles : List 𝓢(ℝ, ℝ)) (x : ℝ)
    (hu : u x = 0) : ccmLocalizationRemainder u angles x = 0 := by
  induction angles generalizing u with
  | nil => exact hu
  | cons theta rest ih =>
    exact ih (ccmCosLocalizedSource u theta) (by rw [ccmCosLocalizedSource_apply, hu, mul_zero])

theorem ccmLocalizationRemainder_apply_eq_zero_of_mem {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (angles : List 𝓢(ℝ, ℝ))
    (theta : 𝓢(ℝ, ℝ)) (ht : theta ∈ angles) (x : ℝ) (hx : Real.cos (theta x) = 0) :
    ccmLocalizationRemainder u angles x = 0 := by
  induction angles generalizing u with
  | nil => simp only [List.not_mem_nil] at ht
  | cons eta rest ih =>
    rcases List.mem_cons.mp ht with h | h
    · subst eta
      exact ccmLocalizationRemainder_apply_eq_zero _ rest x
        (by rw [ccmCosLocalizedSource_apply, hx, Complex.ofReal_zero, zero_mul])
    · exact ih (ccmCosLocalizedSource u eta) h

theorem tsupport_ccmSinLocalizedSource_subset_angle {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (theta : 𝓢(ℝ, ℝ)) :
    tsupport (ccmSinLocalizedSource u theta) ⊆ tsupport theta := by
  apply closure_mono
  intro x hx hz
  exact hx (by rw [ccmSinLocalizedSource_apply, hz, Real.sin_zero, Complex.ofReal_zero, zero_mul])

theorem ccmLocalizationPieces_support {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (angles : List 𝓢(ℝ, ℝ)) (delta : ℝ)
    (hs : ∀ theta ∈ angles, ∃ c : ℝ, tsupport theta ⊆ Metric.ball c delta) :
    ∀ v ∈ ccmLocalizationPieces u angles, ∃ c : ℝ, tsupport v ⊆ Metric.ball c delta := by
  induction angles generalizing u with
  | nil => simp only [ccmLocalizationPieces, List.not_mem_nil, false_implies, implies_true]
  | cons theta rest ih =>
    intro v hv
    rcases List.mem_cons.mp hv with hv | hv
    · subst v
      obtain ⟨c, hc⟩ := hs theta (List.mem_cons_self)
      exact ⟨c, (tsupport_ccmSinLocalizedSource_subset_angle u theta).trans hc⟩
    · exact ih (ccmCosLocalizedSource u theta)
        (fun eta he => hs eta (List.mem_cons_of_mem _ he)) v hv

end RHTower
