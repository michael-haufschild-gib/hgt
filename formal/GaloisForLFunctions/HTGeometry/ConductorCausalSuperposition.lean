import GaloisForLFunctions.HTGeometry.ConductorSymbolAnalytic
import GaloisForLFunctions.HTGeometry.CausalFourierBridge

/-!
# The conductor symbol is a superposition of causal resolvents

In the Fourier normalization used by the causal bridge, the transform of the one-sided exponential
of rate `a` is the right-half-plane resolvent `(a + 2iξ)⁻¹`.  The resolvent representation of the
conductor symbol therefore exhibits it as a superposition, over the rate `λ + 2`, of the
transforms of causal exponentials — the analytic half-plane structure that makes one of the two
Hankel pieces of the conductor commutator vanish.

The symbol in this normalization is `Log(2 + 2iξ)`, which is the earlier `Log(2 + iξ)` read at the
doubled frequency; it still differs from `log(2 + |ξ|)` by a bounded amount.
-/

open Complex Real Set Filter Topology MeasureTheory FourierTransform

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- The conductor symbol in the causal Fourier normalization. -/
def conductorAnalyticTwo (ξ : ℝ) : ℂ := Complex.log (2 + 2 * Complex.I * ξ)

theorem conductorAnalyticTwo_eq (ξ : ℝ) : conductorAnalyticTwo ξ = conductorAnalytic (2 * ξ) := by
  rw [conductorAnalyticTwo, conductorAnalytic]
  congr 1
  push_cast
  ring

/-- **The symbol is a superposition of causal resolvents.** -/
theorem conductorAnalyticTwo_eq_resolvent (ξ : ℝ) :
    conductorAnalyticTwo ξ - (Real.log 2 : ℂ)
      = ∫ lam in Ioi (0:ℝ),
          (1 / ((lam : ℂ) + 2) - ((lam : ℂ) + 2 + 2 * Complex.I * ξ)⁻¹) := by
  rw [conductorAnalyticTwo_eq, conductorAnalytic_eq_resolvent (2 * ξ)]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun lam _ => ?_)
  congr 2
  push_cast
  ring

/-- **The bridge to the causal exponentials.**  Each resolvent in the superposition is the Fourier
transform of a one-sided exponential. -/
theorem conductorAnalyticTwo_eq_fourier_superposition (ξ : ℝ) :
    conductorAnalyticTwo ξ - (Real.log 2 : ℂ)
      = ∫ lam in Ioi (0:ℝ),
          (1 / ((lam : ℂ) + 2)
            - 𝓕 (RHTower.causalFourierExponential (lam + 2)) ξ) := by
  rw [conductorAnalyticTwo_eq_resolvent]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun lam hlam => ?_)
  have hlam0 : (0 : ℝ) < lam := hlam
  have ha : (0 : ℝ) < lam + 2 := by linarith
  rw [RHTower.fourier_causalFourierExponential ha]
  congr 2
  push_cast
  ring

/-! ## The bounded difference in this normalization -/

theorem sq_bounds_two (ξ : ℝ) :
    (2 + |ξ|) ^ (2 : ℕ) ≤ 8 * (1 + ξ ^ (2 : ℕ)) ∧ 1 + ξ ^ (2 : ℕ) ≤ (2 + |ξ|) ^ (2 : ℕ) := by
  have habs : |ξ| ^ (2 : ℕ) = ξ ^ (2 : ℕ) := sq_abs ξ
  have hnn : 0 ≤ |ξ| := abs_nonneg ξ
  constructor
  · nlinarith [habs, hnn, sq_nonneg (|ξ| - 2)]
  · nlinarith [habs, hnn]

theorem conductorAnalyticTwo_re (ξ : ℝ) :
    (conductorAnalyticTwo ξ).re = Real.log 2 + Real.log (Real.sqrt (1 + ξ ^ (2 : ℕ))) := by
  have hne : (2 : ℂ) + 2 * Complex.I * ξ = 2 * (1 + Complex.I * ξ) := by ring
  have hnorm : ‖(2 : ℂ) + 2 * Complex.I * ξ‖ = 2 * Real.sqrt (1 + ξ ^ (2 : ℕ)) := by
    rw [hne, norm_mul]
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    have h1 : ‖(1 : ℂ) + Complex.I * ξ‖ = Real.sqrt (1 + ξ ^ (2 : ℕ)) := by
      rw [Complex.norm_def, Complex.normSq_apply]
      congr 1
      simp
      ring
    rw [h2, h1]
  rw [conductorAnalyticTwo, Complex.log_re, hnorm,
    Real.log_mul (by norm_num) (ne_of_gt (Real.sqrt_pos.mpr (by positivity)))]

/-- **The conductor symbol is analytic up to a bounded error, in the causal normalization.** -/
theorem abs_conductorSymbol_sub_analyticTwo_le (ξ : ℝ) :
    |conductorSymbol ξ - (conductorAnalyticTwo ξ).re| ≤ Real.log 2 + Real.log 8 / 2 := by
  have hpos : (0 : ℝ) < 1 + ξ ^ (2 : ℕ) := by positivity
  have hspos : (0 : ℝ) < Real.sqrt (1 + ξ ^ (2 : ℕ)) := Real.sqrt_pos.mpr hpos
  obtain ⟨hup, hlow⟩ := sq_bounds_two ξ
  have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog8 : (0 : ℝ) ≤ Real.log 8 := Real.log_nonneg (by norm_num)
  have hge : Real.log (Real.sqrt (1 + ξ ^ (2 : ℕ))) ≤ Real.log (2 + |ξ|) := by
    refine Real.log_le_log hspos ?_
    rw [show (2 : ℝ) + |ξ| = Real.sqrt ((2 + |ξ|) ^ (2 : ℕ)) by rw [Real.sqrt_sq (by positivity)]]
    exact Real.sqrt_le_sqrt hlow
  have hle : Real.log (2 + |ξ|) ≤ Real.log 8 / 2 + Real.log (Real.sqrt (1 + ξ ^ (2 : ℕ))) := by
    have hsq8 : (2 : ℝ) + |ξ| ≤ Real.sqrt 8 * Real.sqrt (1 + ξ ^ (2 : ℕ)) := by
      rw [← Real.sqrt_mul (by norm_num) (1 + ξ ^ (2 : ℕ)),
        show (2 : ℝ) + |ξ| = Real.sqrt ((2 + |ξ|) ^ (2 : ℕ)) by rw [Real.sqrt_sq (by positivity)]]
      exact Real.sqrt_le_sqrt hup
    have hs8 : (0 : ℝ) < Real.sqrt 8 := Real.sqrt_pos.mpr (by norm_num)
    have h1 : Real.log (2 + |ξ|) ≤ Real.log (Real.sqrt 8 * Real.sqrt (1 + ξ ^ (2 : ℕ))) :=
      Real.log_le_log (by positivity) hsq8
    rw [Real.log_mul (ne_of_gt hs8) (ne_of_gt hspos)] at h1
    have hval : Real.log (Real.sqrt 8) = Real.log 8 / 2 := by
      have h2 : Real.sqrt 8 * Real.sqrt 8 = 8 := Real.mul_self_sqrt (by norm_num)
      have hlog := Real.log_mul (ne_of_gt hs8) (ne_of_gt hs8)
      rw [h2] at hlog
      linarith
    rwa [hval] at h1
  rw [conductorSymbol, conductorAnalyticTwo_re, abs_le]
  constructor <;> linarith

end GaloisForLFunctions.HTGeometry
