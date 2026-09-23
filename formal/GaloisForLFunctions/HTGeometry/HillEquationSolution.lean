import GaloisForLFunctions.HTGeometry.HillOscillatorEnergy
import GaloisForLFunctions.HTGeometry.VolterraLinearIntegralEquation

/-!
# Global solutions of the Hill equation

The oscillator `u'' + ω(t)²u = 0` with a time-dependent frequency is the first-order system
`(u, u')' = A(t)(u, u')`. Written as a Volterra integral equation its kernel is bounded whenever the
frequency is, so the corpus's Picard series — which needs no smallness, because each iteration
integrates one more power of the time variable — produces a solution on the whole line.

Combined with the energy estimate this gives, for every initial datum, a global solution whose energy
obeys a bound depending only on the logarithmic derivative of the frequency, and therefore uniform
over a family of frequencies `ω = c·s`.
-/

namespace GaloisForLFunctions.HTGeometry

open Set MeasureTheory intervalIntegral

/-! ## The first-order system -/

/-- The generator of the Hill system. -/
noncomputable def hillField (ω : ℝ → ℝ) (s : ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).prod (-(ω s ^ (2 : ℕ)) • ContinuousLinearMap.fst ℝ ℝ ℝ)

theorem hillField_apply (ω : ℝ → ℝ) (s : ℝ) (y : ℝ × ℝ) :
    hillField ω s y = (y.2, -(ω s ^ (2 : ℕ)) * y.1) := rfl

theorem norm_hillField_le {ω : ℝ → ℝ} {M : ℝ} (hM1 : 1 ≤ M) (hM : ∀ s, ω s ^ (2 : ℕ) ≤ M) (s : ℝ) :
    ‖hillField ω s‖ ≤ M := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by linarith) fun y => ?_
  rw [hillField_apply, Prod.norm_def, Prod.norm_def]
  refine max_le ?_ ?_
  · refine le_trans (le_max_right ‖y.1‖ ‖y.2‖) ?_
    nlinarith [le_max_left ‖y.1‖ ‖y.2‖, le_max_right ‖y.1‖ ‖y.2‖, norm_nonneg y.1, norm_nonneg y.2]
  · have hy1 : ‖y.1‖ ≤ max ‖y.1‖ ‖y.2‖ := le_max_left _ _
    have hsq : (0 : ℝ) ≤ ω s ^ (2 : ℕ) := sq_nonneg _
    have hnorm : ‖-(ω s ^ (2 : ℕ)) * y.1‖ = ω s ^ (2 : ℕ) * ‖y.1‖ := by
      rw [norm_mul, norm_neg, Real.norm_eq_abs, abs_of_nonneg hsq]
    rw [hnorm]
    have hle := hM s
    nlinarith [norm_nonneg y.1, le_max_left ‖y.1‖ ‖y.2‖, norm_nonneg y.2]

theorem continuous_hillField {ω : ℝ → ℝ} (hω : Continuous ω) :
    Continuous fun p : ℝ × ℝ => hillField ω p.2 := by
  have hsplit : (fun p : ℝ × ℝ => hillField ω p.2)
      = fun p : ℝ × ℝ => (ContinuousLinearMap.snd ℝ ℝ ℝ).prod 0 +
        (-(ω p.2 ^ (2 : ℕ))) • ((0 : (ℝ × ℝ) →L[ℝ] ℝ).prod (ContinuousLinearMap.fst ℝ ℝ ℝ)) := by
    funext p
    refine ContinuousLinearMap.ext fun y => ?_
    simp [hillField_apply]
  rw [hsplit]
  exact continuous_const.add (((hω.comp continuous_snd).pow 2).neg.smul continuous_const)

/-! ## The flow -/

/-- The solution of the Hill system with prescribed initial datum. -/
noncomputable def hillFlow (ω : ℝ → ℝ) (y₀ : ℝ × ℝ) : ℝ → ℝ × ℝ :=
  volterraSolution (fun _ => y₀) fun _ s => hillField ω s

section Flow

variable {ω : ℝ → ℝ} {M : ℝ}

theorem continuous_hillFlow (hω : Continuous ω) (hM1 : 1 ≤ M) (hM : ∀ s, ω s ^ (2 : ℕ) ≤ M)
    (y₀ : ℝ × ℝ) : Continuous (hillFlow ω y₀) :=
  continuous_volterraSolution continuous_const (continuous_hillField hω) (by linarith)
    (norm_nonneg y₀) (fun _ s => norm_hillField_le hM1 hM s) fun _ => le_rfl

theorem hillFlow_eq (hω : Continuous ω) (hM1 : 1 ≤ M) (hM : ∀ s, ω s ^ (2 : ℕ) ≤ M) (y₀ : ℝ × ℝ)
    (t : ℝ) :
    hillFlow ω y₀ t = y₀ + ∫ s in (0 : ℝ)..t, hillField ω s (hillFlow ω y₀ s) :=
  volterraSolution_eq continuous_const (continuous_hillField hω) (by linarith)
    (norm_nonneg y₀) (fun _ s => norm_hillField_le hM1 hM s) (fun _ => le_rfl) t

theorem hillFlow_zero (hω : Continuous ω) (hM1 : 1 ≤ M) (hM : ∀ s, ω s ^ (2 : ℕ) ≤ M) (y₀ : ℝ × ℝ) :
    hillFlow ω y₀ 0 = y₀ := by
  rw [hillFlow_eq hω hM1 hM y₀ 0]
  simp

theorem hasDerivAt_hillFlow (hω : Continuous ω) (hM1 : 1 ≤ M) (hM : ∀ s, ω s ^ (2 : ℕ) ≤ M)
    (y₀ : ℝ × ℝ) (t : ℝ) :
    HasDerivAt (hillFlow ω y₀) (hillField ω t (hillFlow ω y₀ t)) t := by
  have hcont : Continuous fun s => hillField ω s (hillFlow ω y₀ s) := by
    have hpair : Continuous fun s : ℝ => ((s, s) : ℝ × ℝ) := continuous_id.prodMk continuous_id
    exact ((continuous_hillField hω).comp hpair).clm_apply (continuous_hillFlow hω hM1 hM y₀)
  have hint : HasDerivAt (fun u => ∫ s in (0 : ℝ)..u, hillField ω s (hillFlow ω y₀ s))
      (hillField ω t (hillFlow ω y₀ t)) t :=
    integral_hasDerivAt_right (hcont.intervalIntegrable 0 t)
      (hcont.stronglyMeasurableAtFilter _ _) hcont.continuousAt
  have hshift : HasDerivAt (fun u => y₀ + ∫ s in (0 : ℝ)..u, hillField ω s (hillFlow ω y₀ s))
      (hillField ω t (hillFlow ω y₀ t)) t := by
    simpa using hint.const_add y₀
  refine hshift.congr_of_eventuallyEq ?_
  exact Filter.Eventually.of_forall fun u => hillFlow_eq hω hM1 hM y₀ u

end Flow

/-! ## The scalar solution -/

/-- The Hill oscillator with prescribed position and velocity. -/
noncomputable def hillSolution (ω : ℝ → ℝ) (y₀ : ℝ × ℝ) : ℝ → ℝ := fun t => (hillFlow ω y₀ t).1

/-- Its velocity. -/
noncomputable def hillSolutionDeriv (ω : ℝ → ℝ) (y₀ : ℝ × ℝ) : ℝ → ℝ :=
  fun t => (hillFlow ω y₀ t).2

section Solution

variable {ω : ℝ → ℝ} {M : ℝ}

theorem hasDerivAt_hillSolution (hω : Continuous ω) (hM1 : 1 ≤ M) (hM : ∀ s, ω s ^ (2 : ℕ) ≤ M)
    (y₀ : ℝ × ℝ) (t : ℝ) :
    HasDerivAt (hillSolution ω y₀) (hillSolutionDeriv ω y₀ t) t := by
  have h := (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_hillFlow hω hM1 hM y₀ t)
  have h' : HasDerivAt (fun x => (hillFlow ω y₀ x).1) (hillFlow ω y₀ t).2 t := by
    simpa [hillField_apply, Function.comp_def] using h
  exact h'

theorem hasDerivAt_hillSolutionDeriv (hω : Continuous ω) (hM1 : 1 ≤ M) (hM : ∀ s, ω s ^ (2 : ℕ) ≤ M)
    (y₀ : ℝ × ℝ) (t : ℝ) :
    HasDerivAt (hillSolutionDeriv ω y₀) (-(ω t ^ (2 : ℕ)) * hillSolution ω y₀ t) t := by
  have h := (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_hillFlow hω hM1 hM y₀ t)
  have h' : HasDerivAt (fun x => (hillFlow ω y₀ x).2) (-(ω t ^ (2 : ℕ) * (hillFlow ω y₀ t).1)) t := by
    simpa [hillField_apply, Function.comp_def] using h
  have hval : -(ω t ^ (2 : ℕ) * (hillFlow ω y₀ t).1) = -(ω t ^ (2 : ℕ)) * hillSolution ω y₀ t := by
    rw [hillSolution]
    ring
  rw [← hval]
  exact h'

theorem hillEquation (ω : ℝ → ℝ) (y₀ : ℝ × ℝ) (t : ℝ) :
    -(ω t ^ (2 : ℕ)) * hillSolution ω y₀ t + ω t ^ (2 : ℕ) * hillSolution ω y₀ t = 0 := by ring

theorem hillSolution_zero (hω : Continuous ω) (hM1 : 1 ≤ M) (hM : ∀ s, ω s ^ (2 : ℕ) ≤ M)
    (y₀ : ℝ × ℝ) : hillSolution ω y₀ 0 = y₀.1 := by
  rw [hillSolution, hillFlow_zero hω hM1 hM y₀]

theorem hillSolutionDeriv_zero (hω : Continuous ω) (hM1 : 1 ≤ M) (hM : ∀ s, ω s ^ (2 : ℕ) ≤ M)
    (y₀ : ℝ × ℝ) : hillSolutionDeriv ω y₀ 0 = y₀.2 := by
  rw [hillSolutionDeriv, hillFlow_zero hω hM1 hM y₀]

/-- **A global Hill oscillator with the frequency-uniform energy bound.** The solution exists for all
time, takes the prescribed initial data, and its energy obeys a bound governed only by the
logarithmic derivative of the frequency. -/
theorem hillEnergy_hillSolution_le {dω : ℝ → ℝ} {K a b : ℝ} (hω : Continuous ω)
    (hM1 : 1 ≤ M) (hM : ∀ s, ω s ^ (2 : ℕ) ≤ M) (hωd : ∀ t, HasDerivAt ω (dω t) t)
    (hωpos : ∀ t, 0 < ω t) (hK : ∀ t, |dω t| ≤ K * ω t) (y₀ : ℝ × ℝ) {t : ℝ} (ht : t ∈ Icc a b) :
    hillEnergy ω (hillSolution ω y₀) (hillSolutionDeriv ω y₀) t ≤
      hillEnergy ω (hillSolution ω y₀) (hillSolutionDeriv ω y₀) a * Real.exp (2 * K * (t - a)) :=
  hillEnergy_le_of_logDeriv_le hωd (hasDerivAt_hillSolution hω hM1 hM y₀)
    (hasDerivAt_hillSolutionDeriv hω hM1 hM y₀)
    (fun s => hillEquation ω y₀ s) hωpos hK ht

end Solution

end GaloisForLFunctions.HTGeometry
