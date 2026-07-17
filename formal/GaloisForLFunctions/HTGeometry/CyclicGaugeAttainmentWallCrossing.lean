import GaloisForLFunctions.HTGeometry.PeriodIncidenceMultiplier
import GaloisForLFunctions.HTGeometry.GammaPeriodicConstraintCorona

/-!
# A quantitative cyclic gauge--attainment wall crossing

For the shrinking cyclic periods `q_n = 1 / (n+1)`, the primitive normalized exponential gauge
has first-jet size `2π(n+1)`, while the regularized period-incidence symbol has size
`1 / (n+2)`.  The two escape rates obey the exact conservation law

`‖w(q_n)‖⁻¹ = 1 + ‖g_n'(0)‖ / (2π)`.

Thus the nonconstant fixed gauge escaping along the discrete side and the approximate-null
incidence direction appearing at the nondiscrete boundary are not merely simultaneous: in this
rank-one model they are reciprocal coordinates of the same degenerating period.  The identity is
a quantitative bridge, not a claim that an individual gauge is canonically selected for an
arbitrary period source.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The positive generator of the shrinking cyclic source `(1 / (n+1)) ℤ`. -/
def cyclicWallPeriod (n : ℕ) : ℂ := (((n + 1 : ℕ) : ℂ))⁻¹

/-- The primitive normalized character fixed by translation through `cyclicWallPeriod n`. -/
def cyclicWallGauge (n : ℕ) : ℂ → ℂ := gammaPeriodicMode (n + 1)

theorem cyclicWallPeriod_ne_zero (n : ℕ) : cyclicWallPeriod n ≠ 0 := by
  exact inv_ne_zero (by exact_mod_cast (Nat.succ_ne_zero n))

@[simp] theorem cyclicWallGauge_zero (n : ℕ) : cyclicWallGauge n 0 = 1 := by
  simp [cyclicWallGauge, gammaPeriodicMode]

/-- The escaping character is fixed by the corresponding shrinking cyclic source. -/
theorem cyclicWallGauge_periodic (n : ℕ) :
    Function.Periodic (cyclicWallGauge n) (cyclicWallPeriod n) := by
  intro z
  simp only [cyclicWallGauge, gammaPeriodicMode]
  rw [mul_add, Complex.exp_add]
  have hphase :
      gammaPeriodicFrequency (n + 1) * cyclicWallPeriod n =
        2 * (Real.pi : ℂ) * Complex.I := by
    have hn : (((n + 1 : ℕ) : ℂ)) ≠ 0 := by
      exact_mod_cast (Nat.succ_ne_zero n)
    simp only [gammaPeriodicFrequency, cyclicWallPeriod]
    field_simp [hn]
  rw [hphase, Complex.exp_two_pi_mul_I, mul_one]

theorem norm_cyclicWallPeriod (n : ℕ) :
    ‖cyclicWallPeriod n‖ = ((n + 1 : ℕ) : ℝ)⁻¹ := by
  rw [cyclicWallPeriod, norm_inv, Complex.norm_natCast]

/-- The first logarithmic character jet grows at the reciprocal period scale. -/
theorem norm_cyclicWallGauge_firstJet (n : ℕ) :
    ‖iteratedDeriv 1 (cyclicWallGauge n) 0‖ =
      2 * Real.pi * (n + 1 : ℕ) := by
  rw [cyclicWallGauge, iteratedDeriv_gammaPeriodicMode_zero]
  simp only [pow_one, gammaPeriodicFrequency]
  change ‖(((n + 1 : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))‖ = _
  rw [norm_mul, Complex.norm_natCast, norm_mul, norm_mul,
    Complex.norm_real, Complex.norm_I]
  simp only [Complex.norm_ofNat, Real.norm_eq_abs, abs_of_pos Real.pi_pos, mul_one]
  push_cast
  ring

/-- **Exact gauge--attainment conservation.**  Gauge-jet escape and inverse incidence-symbol
blow-up differ by the bounded regularization constant `1`, at every scale rather than only
asymptotically. -/
theorem cyclicWall_gaugeAttainment_conservation (n : ℕ) :
    ‖GaloisForLFunctions.regularizedPeriodWeight (cyclicWallPeriod n)‖⁻¹ =
      1 + ‖iteratedDeriv 1 (cyclicWallGauge n) 0‖ / (2 * Real.pi) := by
  rw [GaloisForLFunctions.norm_regularizedPeriodWeight,
    norm_cyclicWallPeriod, norm_cyclicWallGauge_firstJet]
  have hn : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  field_simp [hn.ne']
  ring

theorem cyclicWallPeriod_tendsto_zero :
    Tendsto cyclicWallPeriod atTop (𝓝 0) := by
  have hfun : cyclicWallPeriod = fun n : ℕ ↦ ((n : ℂ) + 1)⁻¹ := by
    funext n
    simp only [cyclicWallPeriod, Nat.cast_add, Nat.cast_one]
  rw [hfun]
  simpa only [one_div] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℂ))

theorem cyclicWallGauge_firstJet_tendsto_atTop :
    Tendsto (fun n ↦ ‖iteratedDeriv 1 (cyclicWallGauge n) 0‖) atTop atTop := by
  have hcast : Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  convert hcast.const_mul_atTop (by positivity : 0 < 2 * Real.pi) using 1
  funext n
  exact norm_cyclicWallGauge_firstJet n

theorem cyclicWallIncidenceWeight_tendsto_zero :
    Tendsto
      (fun n ↦ GaloisForLFunctions.regularizedPeriodWeight (cyclicWallPeriod n))
      atTop (𝓝 0) :=
  GaloisForLFunctions.tendsto_regularizedPeriodWeight_zero
    cyclicWallPeriod_tendsto_zero

theorem norm_cyclicWallIncidenceWeight_tendsto_zero :
    Tendsto
      (fun n ↦ ‖GaloisForLFunctions.regularizedPeriodWeight (cyclicWallPeriod n)‖)
      atTop (𝓝 0) :=
  tendsto_zero_iff_norm_tendsto_zero.mp cyclicWallIncidenceWeight_tendsto_zero

end

end GaloisForLFunctions.HTGeometry
