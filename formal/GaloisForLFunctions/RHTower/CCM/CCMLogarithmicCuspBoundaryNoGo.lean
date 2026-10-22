import GaloisForLFunctions.HTGeometry.PeriodicCuspBoundaryGap
import GaloisForLFunctions.RHTower.CCM.CCMFiniteRamifiedBoundaryNoGo

/-!
# CCM logarithmic-cusp boundary exclusion

This file closes the bounded holomorphic logarithmic-cover escape left by finite ramification.
Positive first-order thermal density quantizes the full logarithmic period to `4π` times a positive
integral cusp order. Consequently the ordinary one-loop period `2π` cannot descend any such CCM
boundary branch, in arbitrary complete complex normed targets.
-/

open Complex Filter Asymptotics Function Set
open scoped Real Topology

noncomputable section

namespace RHTower

local notation "I∞" => comap Complex.im atTop

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

omit [NormedSpace ℂ E] [CompleteSpace E] in
/-- The logarithmic central-ray density is exactly the analytic ramification density of the
normed cusp function, at rate `2π/h`. -/
theorem logarithmicCuspBoundaryDensity_eq_analyticRamifiedBoundaryDensity
    {h : ℝ} (hh : h ≠ 0) {f : ℂ → E} (hf : Periodic f (h : ℂ)) :
    HTGeometry.logarithmicCuspBoundaryDensity f =
      analyticRamifiedBoundaryDensity (2 * Real.pi / h)
        (HTGeometry.normedPeriodicCuspFunction h f) := by
  funext t
  rw [HTGeometry.logarithmicCuspBoundaryDensity,
    analyticRamifiedBoundaryDensity,
    normedAnalyticShiftMultiplier,
    ← HTGeometry.qParam_vertical_eq_real_exp hh t,
    HTGeometry.normedPeriodicCuspFunction_qParam_eq hh hf]

/-- **Periodic-cusp charge law.** Positive finite first-order thermal density quantizes the period
of every bounded holomorphic logarithmic cover by
`h = 4π * ord₀(cuspFunction)`. -/
theorem period_eq_four_pi_mul_analyticOrderNatAt_of_logarithmicCuspBoundaryDensity_pos
    {h : ℝ} (hh : 0 < h) {f : ℂ → E} (hf : Periodic f (h : ℂ))
    (hhol : ∀ᶠ z in I∞, DifferentiableAt ℂ f z)
    (hbd : BoundedAtFilter I∞ f) {ell : ℝ} (hell : 0 < ell)
    (hdensity : Tendsto (HTGeometry.logarithmicCuspBoundaryDensity f) atTop (nhds ell)) :
    h = 4 * Real.pi *
      (analyticOrderNatAt (HTGeometry.normedPeriodicCuspFunction h f) 0 : ℝ) := by
  have hq : 0 < 2 * Real.pi / h :=
    div_pos (mul_pos (by norm_num) Real.pi_pos) hh
  have hana := HTGeometry.analyticAt_normedPeriodicCuspFunction_zero hh hf hhol hbd
  have hquant :=
    two_mul_rate_mul_analyticOrderNatAt_eq_one_of_boundaryDensity_pos
      hq hana hell
        (hdensity.congr' (Eventually.of_forall fun t =>
          logarithmicCuspBoundaryDensity_eq_analyticRamifiedBoundaryDensity
            hh.ne' hf ▸ rfl))
  field_simp [hh.ne'] at hquant
  nlinarith

/-- **One-loop logarithmic exclusion.** Period `2π` is incompatible with every positive finite
first-order thermal density. This is the single-valued logarithmic-cover no-go. -/
theorem not_tendsto_logarithmicCuspBoundaryDensity_pos_of_two_pi_periodic
    {f : ℂ → E} (hf : Periodic f ((2 * Real.pi : ℝ) : ℂ))
    (hhol : ∀ᶠ z in I∞, DifferentiableAt ℂ f z)
    (hbd : BoundedAtFilter I∞ f) {ell : ℝ} (hell : 0 < ell) :
    ¬ Tendsto (HTGeometry.logarithmicCuspBoundaryDensity f) atTop (nhds ell) := by
  intro hdensity
  have hperiod :=
    period_eq_four_pi_mul_analyticOrderNatAt_of_logarithmicCuspBoundaryDensity_pos
      (by positivity : (0 : ℝ) < 2 * Real.pi) hf hhol hbd hell hdensity
  have : (1 : ℝ) = 2 * (analyticOrderNatAt
      (HTGeometry.normedPeriodicCuspFunction (2 * Real.pi) f) 0 : ℝ) := by
    nlinarith [Real.pi_pos]
  have hcast : (1 : ℕ) = 2 * analyticOrderNatAt
      (HTGeometry.normedPeriodicCuspFunction (2 * Real.pi) f) 0 := by
    exact_mod_cast this
  omega

/-- Direct CCM connector: the four-unit density forces the same exact period quantization. -/
theorem ccmFourUnit_logarithmicCusp_period_eq_four_pi_mul_order
    {h : ℝ} (hh : 0 < h) {f : ℂ → E} (hf : Periodic f (h : ℂ))
    (hhol : ∀ᶠ z in I∞, DifferentiableAt ℂ f z)
    (hbd : BoundedAtFilter I∞ f)
    (hfour : Tendsto (HTGeometry.logarithmicCuspBoundaryDensity f) atTop (nhds 4)) :
    h = 4 * Real.pi *
      (analyticOrderNatAt (HTGeometry.normedPeriodicCuspFunction h f) 0 : ℝ) := by
  exact period_eq_four_pi_mul_analyticOrderNatAt_of_logarithmicCuspBoundaryDensity_pos
    hh hf hhol hbd (by norm_num) hfour

/-- Direct CCM no-go: a bounded holomorphic one-loop logarithmic descent cannot realize the
four-unit boundary normalization. -/
theorem ccmFourUnit_not_two_pi_periodic_logarithmicCuspBoundary
    {f : ℂ → E} (hf : Periodic f ((2 * Real.pi : ℝ) : ℂ))
    (hhol : ∀ᶠ z in I∞, DifferentiableAt ℂ f z)
    (hbd : BoundedAtFilter I∞ f) :
    ¬ Tendsto (HTGeometry.logarithmicCuspBoundaryDensity f) atTop (nhds 4) := by
  exact not_tendsto_logarithmicCuspBoundaryDensity_pos_of_two_pi_periodic
    hf hhol hbd (by norm_num)

end RHTower
