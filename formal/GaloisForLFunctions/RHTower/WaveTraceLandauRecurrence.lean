import GaloisForLFunctions.HTGeometry.WaveTracePoleDivergence
import GaloisForLFunctions.RHTower.LandauIntegralTransfer

/-!
# Landau transfer for an eventually one-signed wave trace

An eventually nonnegative wave trace is the density of a positive measure on a time tail. The
complex moment generating function of that measure is the shifted Laplace integral of the wave
trace read backwards from a real base point, so holomorphy of the active-pole transform is
exactly the input Landau's theorem consumes.
-/

open Complex Filter MeasureTheory ProbabilityTheory Set Topology
open GaloisForLFunctions.HTGeometry
open scoped ENNReal NNReal

namespace RHTower

noncomputable section

variable {G : Type*} (S : WaveSpectrum G)

/-- Density of the positive measure carried by an eventually nonnegative wave trace. -/
def traceDensity (P : Polynomial ℝ) (sigma : ℝ) (t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (S.realWaveTrace P t * Real.exp (-sigma * t))

/-- The positive measure carried by an eventually nonnegative wave trace. -/
def traceMeasure (P : Polynomial ℝ) (T sigma : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi T)).withDensity (traceDensity S P sigma)

theorem measurable_traceDensity (P : Polynomial ℝ) (sigma : ℝ) :
    Measurable (traceDensity S P sigma) := by
  unfold traceDensity
  exact ENNReal.measurable_ofReal.comp
    (((S.continuous_realWaveTrace P).mul (by fun_prop)).measurable)

theorem traceDensity_lt_top (P : Polynomial ℝ) (sigma : ℝ) (t : ℝ) :
    traceDensity S P sigma t < ⊤ := by
  unfold traceDensity
  exact ENNReal.ofReal_lt_top

theorem toReal_traceDensity_of_nonneg (P : Polynomial ℝ) {sigma t : ℝ}
    (ht : 0 ≤ S.realWaveTrace P t) :
    (traceDensity S P sigma t).toReal = S.realWaveTrace P t * Real.exp (-sigma * t) := by
  unfold traceDensity
  rw [ENNReal.toReal_ofReal]
  positivity

/-- Integrability of an exponential against the trace measure is integrability of the shifted
Laplace integrand on the tail. -/
theorem integrable_exp_traceMeasure_iff (P : Polynomial ℝ) {T sigma : ℝ}
    (hpos : ∀ t, T < t → 0 ≤ S.realWaveTrace P t) (rho : ℝ) :
    Integrable (fun t : ℝ => Real.exp (rho * t)) (traceMeasure S P T sigma) ↔
      IntegrableOn (fun t : ℝ => S.realWaveTrace P t * Real.exp ((rho - sigma) * t))
        (Ioi T) := by
  rw [traceMeasure, integrable_withDensity_iff (measurable_traceDensity S P sigma)
    (Filter.Eventually.of_forall fun t => traceDensity_lt_top S P sigma t)]
  refine integrable_congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [toReal_traceDensity_of_nonneg S P (hpos t ht),
    show (rho - sigma) * t = rho * t + -sigma * t by ring, Real.exp_add]
  ring

/-- The complex moment generating function of the trace measure is the shifted Laplace
integral of the wave trace. -/
theorem complexMGF_traceMeasure (P : Polynomial ℝ) {T sigma : ℝ}
    (hpos : ∀ t, T < t → 0 ≤ S.realWaveTrace P t) (z : ℂ) :
    complexMGF (fun t : ℝ => t) (traceMeasure S P T sigma) z =
      ∫ t in Ioi T, S.waveTrace P t * Complex.exp (-((sigma : ℂ) - z) * t) := by
  rw [complexMGF, traceMeasure,
    integral_withDensity_eq_integral_toReal_smul (measurable_traceDensity S P sigma)
      (Filter.Eventually.of_forall fun t => traceDensity_lt_top S P sigma t)]
  refine setIntegral_congr_ae measurableSet_Ioi ?_
  filter_upwards with t ht
  rw [toReal_traceDensity_of_nonneg S P (hpos t ht), real_smul, ← S.ofReal_realWaveTrace P t]
  rw [show -((sigma : ℂ) - z) * (t : ℂ) = z * (t : ℂ) + (-(sigma : ℂ) * (t : ℂ)) by ring,
    Complex.exp_add]
  push_cast
  ring

end

end RHTower
