import GaloisForLFunctions.HTGeometry.HillPropagatorSymbol

/-!
# A propagation speed, bundled with its estimates

Every statement of the driven evolution carries the same eight hypotheses on the speed: positive,
continuous, differentiable, bounded above and below, with a bounded logarithmic derivative. Bundling
them once makes the rest of the development readable, and gives the window constants — the size of
the propagator and its Lipschitz constant on a window of times — a name.

All bounds are uniform in the spatial frequency; that is the content of the previous file, and here
it is only packaged.
-/

namespace GaloisForLFunctions.HTGeometry

/-- A propagation speed together with the estimates the evolution needs. -/
structure HillSpeed where
  /-- The mass of the species. -/
  mass : ℝ
  /-- The propagation speed as a function of time. -/
  speed : ℝ → ℝ
  /-- Its derivative. -/
  speedDeriv : ℝ → ℝ
  /-- A bound on the logarithmic derivative of the speed. -/
  logBound : ℝ
  /-- A bound on the speed. -/
  sizeBound : ℝ
  /-- A positive lower bound for the speed. -/
  lower : ℝ
  mass_pos : 0 < mass
  continuous_speed : Continuous speed
  hasDerivAt_speed : ∀ t, HasDerivAt speed (speedDeriv t) t
  speed_pos : ∀ t, 0 < speed t
  abs_speedDeriv_le : ∀ t, |speedDeriv t| ≤ logBound * speed t
  speed_sq_le : ∀ t, speed t ^ 2 ≤ sizeBound ^ 2
  lower_pos : 0 < lower
  lower_le : ∀ t, lower ≤ speed t

namespace HillSpeed

section Data

variable {E : Type*} [NormedAddCommGroup E] (a : HillSpeed)

theorem logBound_nonneg : 0 ≤ a.logBound := by
  have h0 : (0 : ℝ) ≤ |a.speedDeriv 0| := abs_nonneg _
  have h1 := a.abs_speedDeriv_le 0
  have h2 := a.speed_pos 0
  nlinarith

/-- The fibre frequency at a spatial frequency. -/
noncomputable def freq (a : HillSpeed) (ξ : E) : ℝ → ℝ := massiveFreq a.mass a.speed ‖ξ‖

theorem freq_pos (ξ : E) (t : ℝ) : 0 < a.freq ξ t := massiveFreq_pos a.mass_pos _ _ _

/-- The speed ratio that controls every bound. -/
noncomputable def ratio (a : HillSpeed) : ℝ := hillSpeedRatio a.speed a.lower

theorem one_le_ratio : 1 ≤ a.ratio := one_le_hillSpeedRatio _ _

theorem ratio_nonneg : 0 ≤ a.ratio := hillSpeedRatio_nonneg _ _

/-! ## The symbols -/

/-- The propagator symbol. -/
noncomputable def propSymbol (a : HillSpeed) (t s : ℝ) (ξ : E) : ℝ :=
  hillPropSymbol a.mass a.speed t s ξ

/-- Its derivative in the first time. -/
noncomputable def propSymbolTimeDeriv (a : HillSpeed) (t s : ℝ) (ξ : E) : ℝ :=
  hillPropSymbolTimeDeriv a.mass a.speed t s ξ

/-- Its derivative in the second time. -/
noncomputable def propSymbolBaseDeriv (a : HillSpeed) (t s : ℝ) (ξ : E) : ℝ :=
  hillPropSymbolBaseDeriv a.mass a.speed t s ξ

/-- The damped free symbol. -/
noncomputable def coscSymbol (a : HillSpeed) (t : ℝ) (ξ : E) : ℝ :=
  hillCoscSymbol a.mass a.speed t ξ

/-- Its time derivative. -/
noncomputable def coscSymbolDeriv (a : HillSpeed) (t : ℝ) (ξ : E) : ℝ :=
  hillCoscSymbolDeriv a.mass a.speed t ξ

/-! ## The pointwise bounds -/

theorem abs_propSymbol_le (t s : ℝ) (ξ : E) :
    |a.propSymbol t s ξ| ≤ 2 * (a.ratio * a.mass⁻¹) *
      (Real.exp (a.logBound * |t|) * Real.exp (a.logBound * |s|)) :=
  abs_hillPropSymbol_le (C := a.sizeBound) a.mass_pos a.continuous_speed a.hasDerivAt_speed
    a.speed_pos a.abs_speedDeriv_le a.speed_sq_le a.lower_pos a.lower_le t s ξ

theorem abs_propSymbolTimeDeriv_le (t s : ℝ) (ξ : E) :
    |a.propSymbolTimeDeriv t s ξ| ≤ 2 * a.ratio *
      (Real.exp (a.logBound * |t|) * Real.exp (a.logBound * |s|)) :=
  abs_hillPropSymbolTimeDeriv_le (C := a.sizeBound) a.mass_pos a.continuous_speed
    a.hasDerivAt_speed a.speed_pos a.abs_speedDeriv_le a.speed_sq_le a.lower_pos a.lower_le t s ξ

theorem abs_propSymbolBaseDeriv_le (t s : ℝ) (ξ : E) :
    |a.propSymbolBaseDeriv t s ξ| ≤ 2 * a.ratio *
      (Real.exp (a.logBound * |t|) * Real.exp (a.logBound * |s|)) :=
  abs_hillPropSymbolBaseDeriv_le (C := a.sizeBound) a.mass_pos a.continuous_speed
    a.hasDerivAt_speed a.speed_pos a.abs_speedDeriv_le a.speed_sq_le a.lower_pos a.lower_le t s ξ

theorem abs_coscSymbol_le (t : ℝ) (ξ : E) :
    |a.coscSymbol t ξ| ≤ a.ratio * a.mass⁻¹ * Real.exp (a.logBound * |t|) :=
  abs_hillCoscSymbol_le (C := a.sizeBound) a.mass_pos a.continuous_speed a.hasDerivAt_speed
    a.speed_pos a.abs_speedDeriv_le a.speed_sq_le a.lower_pos a.lower_le t ξ

theorem abs_coscSymbolDeriv_le (t : ℝ) (ξ : E) :
    |a.coscSymbolDeriv t ξ| ≤ Real.exp (a.logBound * |t|) :=
  abs_hillCoscSymbolDeriv_le (C := a.sizeBound) a.mass_pos a.continuous_speed a.hasDerivAt_speed
    a.speed_pos a.abs_speedDeriv_le a.speed_sq_le t ξ

/-! ## The derivatives and the continuity in the frequency -/

theorem hasDerivAt_propSymbol_time (s : ℝ) (ξ : E) (t : ℝ) :
    HasDerivAt (fun r : ℝ => a.propSymbol r s ξ) (a.propSymbolTimeDeriv t s ξ) t :=
  hasDerivAt_hillPropSymbol_time (C := a.sizeBound) a.mass_pos a.continuous_speed a.speed_sq_le
    s ξ t

theorem hasDerivAt_propSymbol_base (t : ℝ) (ξ : E) (s : ℝ) :
    HasDerivAt (fun r : ℝ => a.propSymbol t r ξ) (a.propSymbolBaseDeriv t s ξ) s :=
  hasDerivAt_hillPropSymbol_base (C := a.sizeBound) a.mass_pos a.continuous_speed a.speed_sq_le
    t ξ s

theorem hasDerivAt_coscSymbol (ξ : E) (t : ℝ) :
    HasDerivAt (fun r : ℝ => a.coscSymbol r ξ) (a.coscSymbolDeriv t ξ) t :=
  hasDerivAt_hillCoscSymbol (C := a.sizeBound) a.mass_pos a.continuous_speed a.speed_sq_le ξ t

theorem continuous_propSymbol_freq (t s : ℝ) : Continuous fun ξ : E => a.propSymbol t s ξ :=
  continuous_hillPropSymbol_freq (C := a.sizeBound) a.mass_pos a.continuous_speed a.speed_sq_le t s

theorem continuous_coscSymbol_freq (t : ℝ) : Continuous fun ξ : E => a.coscSymbol t ξ :=
  continuous_hillCoscSymbol_freq (C := a.sizeBound) a.mass_pos a.continuous_speed a.speed_sq_le t

/-! ## The window constants -/

/-- The size of the propagator symbol on the window `[-T, T]`. -/
noncomputable def propSize (a : HillSpeed) (T : ℝ) : ℝ :=
  2 * (a.ratio * a.mass⁻¹) * (Real.exp (a.logBound * T) * Real.exp (a.logBound * T))

/-- Its Lipschitz constant on that window. -/
noncomputable def propLip (a : HillSpeed) (T : ℝ) : ℝ :=
  2 * a.ratio * (Real.exp (a.logBound * T) * Real.exp (a.logBound * T))

/-- The size of the damped free symbol on that window. -/
noncomputable def coscSize (a : HillSpeed) (T : ℝ) : ℝ :=
  a.ratio * a.mass⁻¹ * Real.exp (a.logBound * T)

theorem exp_le_window {T t : ℝ} (ht : |t| ≤ T) :
    Real.exp (a.logBound * |t|) ≤ Real.exp (a.logBound * T) :=
  Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht a.logBound_nonneg)

theorem propSize_nonneg (T : ℝ) : 0 ≤ a.propSize T := by
  have h1 : (0 : ℝ) ≤ a.ratio * a.mass⁻¹ :=
    mul_nonneg a.ratio_nonneg (le_of_lt (inv_pos.mpr a.mass_pos))
  have h2 : (0 : ℝ) ≤ Real.exp (a.logBound * T) * Real.exp (a.logBound * T) :=
    mul_nonneg (le_of_lt (Real.exp_pos _)) (le_of_lt (Real.exp_pos _))
  rw [propSize]
  positivity

theorem propLip_nonneg (T : ℝ) : 0 ≤ a.propLip T := by
  rw [propLip]
  have := a.ratio_nonneg
  positivity

theorem coscSize_nonneg (T : ℝ) : 0 ≤ a.coscSize T := by
  rw [coscSize]
  have h1 := a.ratio_nonneg
  have h2 : (0 : ℝ) < a.mass⁻¹ := inv_pos.mpr a.mass_pos
  positivity

theorem abs_propSymbol_le_window {T t s : ℝ} (ht : |t| ≤ T) (hs : |s| ≤ T) (ξ : E) :
    |a.propSymbol t s ξ| ≤ a.propSize T := by
  refine (a.abs_propSymbol_le t s ξ).trans ?_
  have hfac : (0 : ℝ) ≤ 2 * (a.ratio * a.mass⁻¹) := by
    have h1 : (0 : ℝ) ≤ a.ratio * a.mass⁻¹ :=
      mul_nonneg a.ratio_nonneg (le_of_lt (inv_pos.mpr a.mass_pos))
    linarith
  refine mul_le_mul_of_nonneg_left ?_ hfac
  exact mul_le_mul (a.exp_le_window ht) (a.exp_le_window hs) (le_of_lt (Real.exp_pos _))
    (le_of_lt (Real.exp_pos _))

theorem abs_propSymbolTimeDeriv_le_window {T t s : ℝ} (ht : |t| ≤ T) (hs : |s| ≤ T) (ξ : E) :
    |a.propSymbolTimeDeriv t s ξ| ≤ a.propLip T := by
  refine (a.abs_propSymbolTimeDeriv_le t s ξ).trans ?_
  have hfac : (0 : ℝ) ≤ 2 * a.ratio := by
    have := a.ratio_nonneg
    linarith
  refine mul_le_mul_of_nonneg_left ?_ hfac
  exact mul_le_mul (a.exp_le_window ht) (a.exp_le_window hs) (le_of_lt (Real.exp_pos _))
    (le_of_lt (Real.exp_pos _))

theorem abs_propSymbolBaseDeriv_le_window {T t s : ℝ} (ht : |t| ≤ T) (hs : |s| ≤ T) (ξ : E) :
    |a.propSymbolBaseDeriv t s ξ| ≤ a.propLip T := by
  refine (a.abs_propSymbolBaseDeriv_le t s ξ).trans ?_
  have hfac : (0 : ℝ) ≤ 2 * a.ratio := by
    have := a.ratio_nonneg
    linarith
  refine mul_le_mul_of_nonneg_left ?_ hfac
  exact mul_le_mul (a.exp_le_window ht) (a.exp_le_window hs) (le_of_lt (Real.exp_pos _))
    (le_of_lt (Real.exp_pos _))

theorem abs_coscSymbol_le_window {T t : ℝ} (ht : |t| ≤ T) (ξ : E) :
    |a.coscSymbol t ξ| ≤ a.coscSize T := by
  refine (a.abs_coscSymbol_le t ξ).trans ?_
  have hfac : (0 : ℝ) ≤ a.ratio * a.mass⁻¹ :=
    mul_nonneg a.ratio_nonneg (le_of_lt (inv_pos.mpr a.mass_pos))
  exact mul_le_mul_of_nonneg_left (a.exp_le_window ht) hfac

theorem abs_coscSymbolDeriv_le_window {T t : ℝ} (ht : |t| ≤ T) (ξ : E) :
    |a.coscSymbolDeriv t ξ| ≤ Real.exp (a.logBound * T) :=
  (a.abs_coscSymbolDeriv_le t ξ).trans (a.exp_le_window ht)

end Data

end HillSpeed

end GaloisForLFunctions.HTGeometry
