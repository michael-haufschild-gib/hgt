import GaloisForLFunctions.HTGeometry.HillDrivenClockProbe
import GaloisForLFunctions.HTGeometry.HillProbeAnywhere
import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonRegularProbes

/-!
# A driven probe at every event

The evolution starts on the slice `t = 0`, so its field is nonvanishing near events of that slice
only. Restarting *both* data at a prescribed time — the speed and the convolving family — and
translating the resulting field back in the chart returns a solution of the original equation, with
the original potential: the wave operator of a speed is carried to the wave operator of the shifted
speed by a translation of the time coordinate, and the chart potential of a shifted family is the
chart potential of the family at the translated event.

That gives probes on a neighbourhood of an arbitrary event, and hence — with the realization of an
arbitrary smooth potential as the chart potential of a real family — the corpus's `OpenProbes`
interface for a variable speed and an arbitrary smooth potential.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory BoundedContinuousFunction

open scoped ContDiff

section Anywhere

variable {d K : ℕ}

/-- The speed datum, restarted at a prescribed time. -/
noncomputable def HillSpeed.shift (a : HillSpeed) (t₀ : ℝ) : HillSpeed where
  mass := a.mass
  speed := hillSpeedShift a.speed t₀
  speedDeriv := fun r => a.speedDeriv (r + t₀)
  logBound := a.logBound
  sizeBound := a.sizeBound
  lower := a.lower
  mass_pos := a.mass_pos
  continuous_speed := continuous_hillSpeedShift a.continuous_speed t₀
  hasDerivAt_speed := hasDerivAt_hillSpeedShift a.hasDerivAt_speed t₀
  speed_pos := hillSpeedShift_pos a.speed_pos t₀
  abs_speedDeriv_le := hillSpeedShift_deriv_le a.abs_speedDeriv_le t₀
  speed_sq_le := hillSpeedShift_sq_le a.speed_sq_le t₀
  lower_pos := a.lower_pos
  lower_le := hillSpeedShift_low a.lower_le t₀

theorem HillSpeed.shift_speed (a : HillSpeed) (t₀ : ℝ) :
    (a.shift t₀).speed = hillSpeedShift a.speed t₀ := rfl

theorem HillSpeed.shift_mass (a : HillSpeed) (t₀ : ℝ) : (a.shift t₀).mass = a.mass := rfl

/-- **The wave operator of a speed is the wave operator of the shifted speed, translated.** -/
theorem hillWaveOp_comp_timeShift {c : ℝ → ℝ} {v : (Fin (d + 1) → ℝ) → ℝ} (t₀ : ℝ)
    (hdiff1 : ∀ z : Fin (d + 1) → ℝ, DifferentiableAt ℝ v z)
    (hdiff2 : ∀ (j : Fin (d + 1)) (z : Fin (d + 1) → ℝ),
      DifferentiableAt ℝ (coordPartial j v) z) (y : Fin (d + 1) → ℝ) :
    hillWaveOp d c (fun z : Fin (d + 1) → ℝ => v (z + kgTimeShiftVec d t₀)) y
      = hillWaveOp d (hillSpeedShift c t₀) v (y + kgTimeShiftVec d t₀) := by
  have hspeed : hillSpeedShift c t₀ ((y + kgTimeShiftVec d t₀) 0) = c (y 0) := by
    rw [add_kgTimeShiftVec_zero]
    show c (y 0 - t₀ + t₀) = c (y 0)
    congr 1
    ring
  rw [hillWaveOp, hillWaveOp, hspeed, coordPartial_sq_comp_add_const hdiff1 hdiff2 0 y]
  congr 2
  exact Finset.sum_congr rfl fun i _ => coordPartial_sq_comp_add_const hdiff1 hdiff2 i.succ y

theorem hillDrivenChartPotential_timeShift
    (b : WienerFamily (EuclideanSpace ℝ (Fin d)) (K + 2)) (t₀ : ℝ) (y : Fin (d + 1) → ℝ) :
    hillDrivenChartPotential (b.timeShift t₀) (y + kgTimeShiftVec d t₀)
      = hillDrivenChartPotential b y := by
  rw [hillDrivenChartPotential_eq, hillDrivenChartPotential_eq, kgChartPotential_timeShift]

/-- **The chart field is positive at any event of the initial slice**, for the datum attached to
that event's point. -/
theorem hillDrivenChartField_pos_of_time_zero
    (hN : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) < (K + 2 : ℕ)) (a : HillSpeed)
    (b : WienerFamily (EuclideanSpace ℝ (Fin d)) (K + 2)) {y₀ : Fin (d + 1) → ℝ}
    (hy₀ : y₀ 0 = 0) :
    0 < hillDrivenChartField a b (hillDrivenProbeDatum d (kgSpatial d y₀)) y₀ := by
  have hval : hillDrivenChartField a b (hillDrivenProbeDatum d (kgSpatial d y₀)) y₀
      = (hillDrivenField a b (hillDrivenProbeDatum d (kgSpatial d y₀)) (y₀ 0)
          (kgSpatial d y₀)).re := rfl
  rw [hval, hy₀, hillDrivenField_zero_apply, Complex.ofReal_re]
  exact integral_hillDrivenStartWeight_pos hN a

/-- **A driven probe at every event**, with its regularity. -/
theorem exists_hillDrivenProbe_at
    (hK : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) < K) (a : HillSpeed)
    (b : WienerFamily (EuclideanSpace ℝ (Fin d)) (K + 2)) (hreal : IsRealFamily b)
    (y₀ : Fin (d + 1) → ℝ) :
    ∃ (W : Set (Fin (d + 1) → ℝ)) (u : (Fin (d + 1) → ℝ) → ℝ), IsOpen W ∧ y₀ ∈ W ∧
      SmoothMetricChart.DifferentiablePartialsOn u W ∧
      SolvesPotentialWaveOn (hillWaveOp d a.speed)
        (fun y => hillDrivenChartPotential b y - a.mass ^ (2 : ℕ)) u W ∧ (∀ y ∈ W, u y ≠ 0) := by
  have hdim : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) < (K + 2 : ℕ) := by
    push_cast
    linarith
  have hN : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) + 1 < (K + 2 : ℕ) := by
    push_cast
    linarith
  set t₀ : ℝ := y₀ 0 with ht₀
  set sh : Fin (d + 1) → ℝ := kgTimeShiftVec d t₀ with hsh
  set a' : HillSpeed := a.shift t₀ with ha'
  set b' : WienerFamily (EuclideanSpace ℝ (Fin d)) (K + 2) := b.timeShift t₀ with hb'
  have hreal' : IsRealFamily b' := isRealFamily_timeShift hreal t₀
  set x₀ : EuclideanSpace ℝ (Fin d) := kgSpatial d y₀ with hx₀
  set G₀ : EuclideanSpace ℝ (Fin d) →ᵇ ℂ := hillDrivenProbeDatum d x₀ with hG₀
  set v : (Fin (d + 1) → ℝ) → ℝ := hillDrivenChartField a' b' G₀ with hv
  have hzero : (y₀ + sh) 0 = 0 := by
    rw [hsh, add_kgTimeShiftVec_zero, ht₀]
    ring
  have hspatial : kgSpatial d (y₀ + sh) = x₀ := by
    rw [hsh, kgSpatial_add_kgTimeShiftVec]
  have hpos : 0 < v (y₀ + sh) := by
    have h := hillDrivenChartField_pos_of_time_zero (K := K) hdim a' b' hzero
    rw [hspatial] at h
    exact h
  have hcont : Continuous v := continuous_hillDrivenChartField hdim a' b' G₀
  have hshiftcont : Continuous fun z : Fin (d + 1) → ℝ => v (z + sh) :=
    hcont.comp (continuous_id.add continuous_const)
  have hne : ∀ᶠ z in nhds y₀, v (z + sh) ≠ 0 := by
    have hval : (fun z : Fin (d + 1) → ℝ => v (z + sh)) y₀ ≠ 0 := ne_of_gt hpos
    exact hshiftcont.continuousAt.eventually_ne hval
  obtain ⟨W, hWsub, hWopen, hWmem⟩ := mem_nhds_iff.mp hne
  have hdiff1 : ∀ z : Fin (d + 1) → ℝ, DifferentiableAt ℝ v z := fun z =>
    (hasFDerivAt_hillDrivenChartField hN a' b' G₀ z).differentiableAt
  have hdiff2 : ∀ (j : Fin (d + 1)) (z : Fin (d + 1) → ℝ),
      DifferentiableAt ℝ (coordPartial j v) z := fun j z =>
    differentiableAt_coordPartial_hillDrivenChartField hK a' b' G₀ j z
  refine ⟨W, fun z : Fin (d + 1) → ℝ => v (z + sh), hWopen, hWmem, ⟨?_, ?_⟩, fun y _ => ?_,
    fun y hy => hWsub hy⟩
  · exact fun z _ => differentiableAt_comp_add_const hdiff1 z
  · intro j z _
    rw [coordPartial_comp_add_const_fun hdiff1 j]
    exact differentiableAt_comp_add_const (hdiff2 j) z
  · have hsolve := solvesPotentialWave_hillDrivenChartField hK a' b' G₀ hreal' (y + sh)
    have hcov := hillWaveOp_comp_timeShift (c := a.speed) (v := v) t₀ hdiff1 hdiff2 y
    show hillWaveOp d a.speed (fun z : Fin (d + 1) → ℝ => v (z + sh)) y +
      (hillDrivenChartPotential b y - a.mass ^ (2 : ℕ)) * v (y + sh) = 0
    rw [hcov, ← hillDrivenChartPotential_timeShift b t₀ y]
    exact hsolve

/-- **The corpus's `OpenProbes` interface for a variable speed with the potential of a real
family.** -/
theorem openProbes_hillWaveOp_driven
    (hK : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) < K) (a : HillSpeed)
    (b : WienerFamily (EuclideanSpace ℝ (Fin d)) (K + 2)) (hreal : IsRealFamily b) :
    OpenProbes (hillWaveOp d a.speed)
      (fun y => hillDrivenChartPotential b y - a.mass ^ (2 : ℕ)) := by
  intro y₀
  obtain ⟨W, u, hWopen, hWmem, _, hsolve, hne⟩ := exists_hillDrivenProbe_at hK a b hreal y₀
  exact ⟨W, hWopen, hWmem, u, hsolve, hne⟩

/-- **And the regular form**, which the conformal transfer consumes. -/
theorem regularOpenProbes_hillWaveOp_driven
    (hK : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) < K) (a : HillSpeed)
    (b : WienerFamily (EuclideanSpace ℝ (Fin d)) (K + 2)) (hreal : IsRealFamily b) :
    RegularOpenProbes (hillWaveOp d a.speed)
      (fun y => hillDrivenChartPotential b y - a.mass ^ (2 : ℕ)) := by
  intro y₀
  obtain ⟨W, u, hWopen, hWmem, hreg, hsolve, hne⟩ := exists_hillDrivenProbe_at hK a b hreal y₀
  exact ⟨W, hWopen, hWmem, u, hreg, hsolve, hne⟩

/-! ## An arbitrary smooth potential, at every event -/

/-- **Clock probes for a variable propagation speed and an arbitrary smooth potential, at every
event.** -/
theorem openProbes_hillWaveOp_smooth
    (hK : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) < K) (a : HillSpeed)
    {P : ℝ × EuclideanSpace ℝ (Fin d) → ℝ} (hP : ContDiff ℝ ∞ P) :
    OpenProbes (hillWaveOp d a.speed) (fun y : Fin (d + 1) → ℝ => P (y 0, kgSpatial d y)) := by
  intro y₀
  have hP' : ContDiff ℝ ∞ fun p : ℝ × EuclideanSpace ℝ (Fin d) => P p + (a.mass ^ (2 : ℕ) - 1) :=
    hP.add contDiff_const
  obtain ⟨B, V, hBreal, hVopen, hVmem, hVeq⟩ :=
    exists_locally_kgChartPotential_of_smooth_spacetime (N := K + 2) hP' y₀
  obtain ⟨W, u, hWopen, hWmem, _, hsolve, hne⟩ := exists_hillDrivenProbe_at hK a B hBreal y₀
  refine ⟨V ∩ W, hVopen.inter hWopen, ⟨hVmem, hWmem⟩, u, fun y hy => ?_, fun y hy => hne y hy.2⟩
  have hpot : hillDrivenChartPotential B y - a.mass ^ (2 : ℕ) = P (y 0, kgSpatial d y) := by
    have hval := hVeq hy.1
    rw [hillDrivenChartPotential_eq, ← hval]
    ring
  show hillWaveOp d a.speed u y + P (y 0, kgSpatial d y) * u y = 0
  rw [← hpot]
  exact hsolve y hy.2

end Anywhere

end GaloisForLFunctions.HTGeometry
