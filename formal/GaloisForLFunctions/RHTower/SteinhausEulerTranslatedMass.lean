import GaloisForLFunctions.RHTower.SteinhausEulerCriticalMoments
import Mathlib.MeasureTheory.Group.LIntegral

open Complex Filter MeasureTheory Set
open scoped ENNReal Topology

noncomputable section
namespace RHTower
open SteinhausModel

/-- The normalized field is covariant under every real vertical shift. -/
theorem steinhausEulerSpatialDensity_add (N : ℕ) (a t : ℝ) (ω : Omega) :
    steinhausEulerSpatialDensity N (a + t) ω =
      steinhausEulerSpatialDensity N t (steinhausEulerVerticalRotation a ω) := by
  unfold steinhausEulerSpatialDensity
  have hz : (1 / 2 : ℂ) + ((a + t : ℝ) : ℂ) * I =
      ((1 / 2 : ℂ) + (t : ℂ) * I) + (a : ℂ) * I := by push_cast; ring
  rw [hz, steinhausFiniteEulerProduct_vertical_eq_rotated _
    (fun _ hp => (Nat.mem_primesBelow.mp hp).2)]

/-- Exact unit mean at every spatial point. -/
theorem lintegral_steinhausEulerSpatialDensity (N : ℕ) (t : ℝ) :
    (∫⁻ ω, steinhausEulerSpatialDensity N t ω ∂steinhausMeasure) = 1 := by
  have h := setLIntegral_steinhausEulerSpatialFiniteBarrier_density (fun _ => 0) 0 0 N
    (by intro j hj; omega) t
  simpa [steinhausEulerSpatialFiniteBarrier, steinhausEulerTiltFiniteBarrier] using h

/-- Literal normalized energy on an arbitrary translated unit interval. -/
def steinhausEulerTranslatedMass (N : ℕ) (a : ℝ) (ω : Omega) : ℝ≥0∞ :=
  ∫⁻ t in Icc a (a + 1), steinhausEulerSpatialDensity N t ω

/-- A single rotation transports the entire spatial integral, pointwise in the sample. -/
theorem steinhausEulerTranslatedMass_eq_rotated (N : ℕ) (a : ℝ) (ω : Omega) :
    steinhausEulerTranslatedMass N a ω =
      steinhausEulerCriticalMass N (steinhausEulerVerticalRotation a ω) := by
  have h := (measurePreserving_add_left volume a).setLIntegral_comp_emb
    (measurableEmbedding_addLeft a) (fun t => steinhausEulerSpatialDensity N t ω) (Icc 0 1)
  rw [Set.image_const_add_Icc, add_zero] at h
  rw [steinhausEulerTranslatedMass, ← h, steinhausEulerCriticalMass]
  apply lintegral_congr
  intro t
  exact steinhausEulerSpatialDensity_add N a t ω

theorem measurable_steinhausEulerTranslatedMass (N : ℕ) (a : ℝ) :
    Measurable (steinhausEulerTranslatedMass N a) := by
  have h := (measurable_steinhausEulerCriticalMass N).comp
    (measurable_steinhausEulerVerticalRotation a)
  simpa only [Function.comp_def, ← steinhausEulerTranslatedMass_eq_rotated] using h

/-- Exact stationarity for every measurable nonnegative test, with no moment restriction. -/
theorem lintegral_steinhausEulerTranslatedMass_test (N : ℕ) (a : ℝ)
    (Φ : ℝ≥0∞ → ℝ≥0∞) (hΦ : Measurable Φ) :
    (∫⁻ ω, Φ (steinhausEulerTranslatedMass N a ω) ∂steinhausMeasure) =
      ∫⁻ ω, Φ (steinhausEulerCriticalMass N ω) ∂steinhausMeasure := by
  simp_rw [steinhausEulerTranslatedMass_eq_rotated]
  have hmp : MeasurePreserving (steinhausEulerVerticalRotation a) steinhausMeasure steinhausMeasure :=
    ⟨measurable_steinhausEulerVerticalRotation a, map_steinhausEulerVerticalRotation a⟩
  exact hmp.lintegral_comp (hΦ.comp (measurable_steinhausEulerCriticalMass N))

theorem lintegral_steinhausEulerTranslatedMass_rpow (N : ℕ) (a q : ℝ) :
    (∫⁻ ω, steinhausEulerTranslatedMass N a ω ^ q ∂steinhausMeasure) =
      ∫⁻ ω, steinhausEulerCriticalMass N ω ^ q ∂steinhausMeasure :=
  lintegral_steinhausEulerTranslatedMass_test N a _ ENNReal.continuous_rpow_const.measurable

/-- All translated unit intervals have vanishing subunit moments along all cutoffs. -/
theorem tendsto_lintegral_steinhausEulerTranslatedMass_rpow (a : ℝ)
    {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    Tendsto (fun N => ∫⁻ ω, steinhausEulerTranslatedMass N a ω ^ q ∂steinhausMeasure)
      atTop (𝓝 0) := by
  simp_rw [lintegral_steinhausEulerTranslatedMass_rpow]
  exact tendsto_lintegral_steinhausEulerCriticalMass_rpow hq hq1

end RHTower
