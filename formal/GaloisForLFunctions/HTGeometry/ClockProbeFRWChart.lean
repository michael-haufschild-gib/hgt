import GaloisForLFunctions.HTGeometry.ClockProbeHomogeneousChart

/-!
# Clock probes on an expanding chart

The homogeneous determination theorem is not vacuous: the charts it applies to include the
Friedmann–Robertson–Walker family, one time direction and `d` spatial directions scaled by
`e^{σ(t)}` for an arbitrary smooth `σ`.  Its inverse metric is `diag(-1, e^{-2σ}, …, e^{-2σ})` and
its volume density is `e^{dσ}`.

For every such chart and every `C¹` potential of time there are genuine clock probes about every
time, and the potential is determined by them. So an expanding universe with an arbitrary
expansion history poses no obstruction to reading the clock potential off clock data.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

open scoped ContDiff

/-- Diagonal of the inverse Friedmann–Robertson–Walker metric: `-1` in the time direction,
`e^{-2σ}` in each spatial direction. -/
noncomputable def frwDiag {d : ℕ} (scale : ℝ → ℝ) (t : ℝ) (i : Fin (d + 1)) : ℝ :=
  if i = 0 then -1 else Real.exp (-2 * scale t)

/-- Inverse Friedmann–Robertson–Walker metric at time `t`. -/
noncomputable def frwCoeff {d : ℕ} (scale : ℝ → ℝ) (t : ℝ) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  Matrix.diagonal (frwDiag scale t)

theorem frwCoeff_zero_zero {d : ℕ} (scale : ℝ → ℝ) (t : ℝ) :
    frwCoeff (d := d) scale t 0 0 = -1 := by
  simp [frwCoeff, frwDiag]

theorem contDiff_scale_comp {d : ℕ} {scale : ℝ → ℝ} (hscale : ContDiff ℝ ∞ scale) :
    ContDiff ℝ ∞ fun x : Fin (d + 1) → ℝ => scale (x 0) :=
  hscale.comp (contDiff_apply ℝ ℝ 0)

/-- The Friedmann–Robertson–Walker chart of an arbitrary smooth expansion history. -/
noncomputable def frwChart {d : ℕ} {scale : ℝ → ℝ} (hscale : ContDiff ℝ ∞ scale) :
    SmoothMetricChart (d + 1) where
  inverseMetric x := frwCoeff scale (x 0)
  density x := Real.exp (d * scale (x 0))
  contDiff_inverseMetric := by
    intro i j
    by_cases hij : i = j
    · rw [hij]
      by_cases hj0 : j = 0
      · rw [hj0]
        have h : (fun x : Fin (d + 1) → ℝ => frwCoeff (d := d) scale (x 0) 0 0)
            = fun _ => (-1 : ℝ) := by
          funext x
          exact frwCoeff_zero_zero scale (x 0)
        rw [h]
        exact contDiff_const
      · have h : (fun x : Fin (d + 1) → ℝ => frwCoeff (d := d) scale (x 0) j j)
            = fun x => Real.exp (-2 * scale (x 0)) := by
          funext x
          simp [frwCoeff, frwDiag, hj0]
        rw [h]
        exact Real.contDiff_exp.comp (contDiff_const.mul (contDiff_scale_comp hscale))
    · have h : (fun x : Fin (d + 1) → ℝ => frwCoeff (d := d) scale (x 0) i j)
          = fun _ => (0 : ℝ) := by
        funext x
        simp [frwCoeff, hij]
      rw [h]
      exact contDiff_const
  contDiff_density :=
    Real.contDiff_exp.comp (contDiff_const.mul (contDiff_scale_comp hscale))
  density_pos := fun _ => Real.exp_pos _
  inverseMetric_symm := by
    intro x i j
    simp only [frwCoeff, Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij
      rfl
    · rw [if_neg hij, if_neg (Ne.symm hij)]

theorem frwChart_inverseMetric {d : ℕ} {scale : ℝ → ℝ} (hscale : ContDiff ℝ ∞ scale)
    (x : Fin (d + 1) → ℝ) :
    (frwChart hscale).inverseMetric x = frwCoeff scale (x 0) := rfl

theorem frwChart_density {d : ℕ} {scale : ℝ → ℝ} (hscale : ContDiff ℝ ∞ scale)
    (x : Fin (d + 1) → ℝ) :
    (frwChart (d := d) hscale).density x = Real.exp (d * scale (x 0)) := rfl

theorem contDiff_frwLeading {d : ℕ} {scale : ℝ → ℝ} (hscale : ContDiff ℝ ∞ scale) :
    ContDiff ℝ 1 fun t => Real.exp (d * scale t) * frwCoeff (d := d) scale t 0 0 := by
  have h : (fun t => Real.exp ((d : ℝ) * scale t) * frwCoeff (d := d) scale t 0 0)
      = fun t => -Real.exp ((d : ℝ) * scale t) := by
    funext t
    rw [frwCoeff_zero_zero]
    ring
  rw [h]
  exact (Real.contDiff_exp.comp (contDiff_const.mul (hscale.of_le (by simp)))).neg

theorem frwLeading_ne_zero {d : ℕ} (scale : ℝ → ℝ) (t : ℝ) :
    Real.exp ((d : ℝ) * scale t) * frwCoeff (d := d) scale t 0 0 ≠ 0 := by
  rw [frwCoeff_zero_zero, mul_neg_one, neg_ne_zero]
  exact ne_of_gt (Real.exp_pos _)

/-- **Clock probes on an expanding chart.** For every smooth expansion history and every `C¹`
potential of time, the equation `□u + Vu = 0` has a solution about every time, constant on the
spatial slices and normalized to one on the initial slice. -/
theorem exists_frw_localProbe {d : ℕ} {scale : ℝ → ℝ} (hscale : ContDiff ℝ ∞ scale)
    {V : ℝ → ℝ} (hV : ContDiff ℝ 1 V) (a : ℝ) :
    ∃ (u : (Fin (d + 1) → ℝ) → ℝ) (ε : ℝ), 0 < ε ∧
      (∀ x : Fin (d + 1) → ℝ, x 0 = a → u x = 1) ∧
      (∀ x : Fin (d + 1) → ℝ, x 0 ∈ Ioo (a - ε) (a + ε) →
        SolvesPotentialWaveAt (frwChart hscale).dalembert (timeLift V) u x) :=
  exists_homogeneous_localProbe (frwChart_inverseMetric hscale) (frwChart_density hscale)
    (contDiff_frwLeading hscale) (frwLeading_ne_zero scale)
    ((Real.contDiff_exp.comp (contDiff_const.mul (hscale.of_le (by simp)))).mul hV) a

/-- **The clock potential of an expanding chart is determined by clock data.** No nondegeneracy
hypothesis is assumed; the probes are constructed. -/
theorem frw_potential_eq {d : ℕ} {scale : ℝ → ℝ} (hscale : ContDiff ℝ ∞ scale)
    {V : ℝ → ℝ} (hV : ContDiff ℝ 1 V) {other : (Fin (d + 1) → ℝ) → ℝ}
    (hother : ∀ (b : ℝ) (u : (Fin (d + 1) → ℝ) → ℝ) (ε : ℝ), 0 < ε →
      (∀ x : Fin (d + 1) → ℝ, x 0 ∈ Ioo (b - ε) (b + ε) →
        SolvesPotentialWaveAt (frwChart hscale).dalembert (timeLift V) u x) →
      (∀ x : Fin (d + 1) → ℝ, x 0 ∈ Ioo (b - ε) (b + ε) →
        SolvesPotentialWaveAt (frwChart hscale).dalembert other u x)) :
    other = timeLift V :=
  chartPotential_eq_of_homogeneous (frwChart_inverseMetric hscale) (frwChart_density hscale)
    (contDiff_frwLeading hscale) (frwLeading_ne_zero scale)
    ((Real.contDiff_exp.comp (contDiff_const.mul (hscale.of_le (by simp)))).mul hV) hother

end GaloisForLFunctions.HTGeometry
