import GaloisForLFunctions.HTGeometry.ConformalMetricLowRegularity
import GaloisForLFunctions.HTGeometry.KleinGordonSpacetimeProbe

/-!
# The constructed probes have the regularity the conformal calculus consumes

The probe interface records only that a field solves the equation on an open set and does not vanish
there. Transporting a probe to a conformally rescaled chart needs one more fact about it: that its
first partial derivatives are differentiable.

The hyperbolic construction supplies exactly that, and no more — the field is differentiated twice
and its second derivatives are not known to be continuous. This file carries the regularity through
the probe interface, so that the constructed probes are usable by the conformal transfer.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped ContDiff

namespace SmoothMetricChart

variable {d : ℕ}

/-- Translation preserves the regularity class. -/
theorem DifferentiablePartials.comp_add_const {u : (Fin d → ℝ) → ℝ}
    (hu : DifferentiablePartials u) (c : Fin d → ℝ) :
    DifferentiablePartials fun z : Fin d → ℝ => u (z + c) where
  base := fun y => (hasFDerivAt_comp_add_const (hu.base (y + c)).hasFDerivAt).differentiableAt
  coord := by
    intro j y
    rw [coordPartial_comp_add_const_fun (fun z => hu.base z) j]
    exact (hasFDerivAt_comp_add_const (hu.coord j (y + c)).hasFDerivAt).differentiableAt

end SmoothMetricChart

/-! ## The chart field -/

section ChartField

variable {d N : ℕ} (a : WienerFamily (EuclideanSpace ℝ (Fin d)) N)
  (G₀ : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℂ)

/-- **The constructed chart field has differentiable partials.** -/
theorem differentiablePartials_kgChartField
    (hN : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) + 2 < N) :
    SmoothMetricChart.DifferentiablePartials (kgChartField a G₀) where
  base := fun y => (hasFDerivAt_kgChartField a G₀ hN y).differentiableAt
  coord := fun j y => differentiableAt_coordPartial_kgChartField a G₀ hN j y

end ChartField

/-! ## Probes carrying their regularity -/

section RegularProbes

variable {d N : ℕ}

/-- Clock probes whose fields have differentiable partials: the interface the conformal transfer
consumes. -/
def RegularOpenProbes (wave : ((Fin d → ℝ) → ℝ) → (Fin d → ℝ) → ℝ)
    (potential : (Fin d → ℝ) → ℝ) : Prop :=
  ∀ x : Fin d → ℝ, ∃ W : Set (Fin d → ℝ), IsOpen W ∧ x ∈ W ∧ ∃ u : (Fin d → ℝ) → ℝ,
    SmoothMetricChart.DifferentiablePartials u ∧
      SolvesPotentialWaveOn wave potential u W ∧ ∀ y ∈ W, u y ≠ 0

theorem RegularOpenProbes.openProbes {wave : ((Fin d → ℝ) → ℝ) → (Fin d → ℝ) → ℝ}
    {potential : (Fin d → ℝ) → ℝ} (h : RegularOpenProbes wave potential) :
    OpenProbes wave potential := by
  intro x
  obtain ⟨W, hWopen, hxW, u, _, hu, hune⟩ := h x
  exact ⟨W, hWopen, hxW, u, hu, hune⟩

variable (A : WienerFamily (EuclideanSpace ℝ (Fin d)) N)

/-- **A regular probe at every event.** -/
theorem regularOpenProbes_kgChartPotential
    (hN : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) + 2 < N) (hreal : IsRealFamily A) :
    RegularOpenProbes (kgWaveOp d) (kgChartPotential A) := by
  intro y₀
  set t₀ : ℝ := y₀ 0 with ht₀
  set x₀ : EuclideanSpace ℝ (Fin d) := kgSpatial d y₀ with hx₀
  set c : Fin (d + 1) → ℝ := kgTimeShiftVec d t₀ with hc
  set B : WienerFamily (EuclideanSpace ℝ (Fin d)) N := A.timeShift t₀ with hB
  have hshift : Continuous fun z : Fin (d + 1) → ℝ => z + c := continuous_add_const c
  have h1 : (y₀ + c) 0 = 0 := by
    rw [hc, add_kgTimeShiftVec_zero, ht₀]
    ring
  have h2 : kgSpatial d (y₀ + c) = x₀ := by
    rw [hc, kgSpatial_add_kgTimeShiftVec, hx₀]
  have hmap : Filter.Tendsto (fun z : Fin (d + 1) → ℝ =>
      (((z + c) 0, kgSpatial d (z + c)) : ℝ × EuclideanSpace ℝ (Fin d))) (nhds y₀)
      (nhds (0, x₀)) := by
    have hcont : Continuous fun z : Fin (d + 1) → ℝ =>
        (((z + c) 0, kgSpatial d (z + c)) : ℝ × EuclideanSpace ℝ (Fin d)) :=
      ((continuous_apply 0).comp hshift).prodMk ((continuous_kgSpatial d).comp hshift)
    have h : Filter.Tendsto (fun z : Fin (d + 1) → ℝ =>
        (((z + c) 0, kgSpatial d (z + c)) : ℝ × EuclideanSpace ℝ (Fin d))) (nhds y₀)
        (nhds (((y₀ + c) 0, kgSpatial d (y₀ + c)) : ℝ × EuclideanSpace ℝ (Fin d))) :=
      hcont.continuousAt
    rw [h1, h2] at h
    exact h
  have hev : ∀ᶠ z in nhds y₀, kgChartField B (kgConjChar x₀) (z + c) ≠ 0 :=
    hmap.eventually (eventually_kgRealField_ne_zero B hN x₀)
  obtain ⟨W, hWsub, hWopen, hWmem⟩ := mem_nhds_iff.mp hev
  refine ⟨W, hWopen, hWmem, fun z : Fin (d + 1) → ℝ => kgChartField B (kgConjChar x₀) (z + c),
    (differentiablePartials_kgChartField B (kgConjChar x₀) hN).comp_add_const c,
    fun z _ => ?_, fun z hz => hWsub hz⟩
  have hwave := kgWaveOp_kgChartField B (kgConjChar x₀) hN (isRealFamily_timeShift hreal t₀)
    (z + c)
  have htrans := kgWaveOp_comp_add_const B hN (kgConjChar x₀) c z
  show kgWaveOp d (fun w : Fin (d + 1) → ℝ => kgChartField B (kgConjChar x₀) (w + c)) z
    + kgChartPotential A z * kgChartField B (kgConjChar x₀) (z + c) = 0
  rw [htrans, ← kgChartPotential_timeShift A t₀ z]
  exact hwave

/-- **Regular probes are a local matter**, exactly as ordinary ones. -/
theorem regularOpenProbes_of_locally_kgChartPotential
    (hN : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) + 2 < N)
    {P : (Fin (d + 1) → ℝ) → ℝ}
    (h : ∀ y₀ : Fin (d + 1) → ℝ, ∃ (B : WienerFamily (EuclideanSpace ℝ (Fin d)) N)
      (W : Set (Fin (d + 1) → ℝ)), IsRealFamily B ∧ IsOpen W ∧ y₀ ∈ W ∧
        Set.EqOn P (kgChartPotential B) W) :
    RegularOpenProbes (kgWaveOp d) P := by
  intro y₀
  obtain ⟨B, W, hBreal, hWopen, hWmem, hWeq⟩ := h y₀
  obtain ⟨W', hW'open, hW'mem, u, hureg, hu, hune⟩ :=
    regularOpenProbes_kgChartPotential B hN hBreal y₀
  refine ⟨W ∩ W', hWopen.inter hW'open, ⟨hWmem, hW'mem⟩, u, hureg, fun z hz => ?_,
    fun z hz => hune z hz.2⟩
  have hzeq : P z = kgChartPotential B z := hWeq hz.1
  have hsolve := hu z hz.2
  show kgWaveOp d u z + P z * u z = 0
  rw [hzeq]
  exact hsolve

/-- **Regular clock probes for every smooth spacetime potential.** -/
theorem regularOpenProbes_of_smooth_spacetime
    (hN : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) + 2 < N)
    {P : ℝ × EuclideanSpace ℝ (Fin d) → ℝ} (hP : ContDiff ℝ ∞ P) :
    RegularOpenProbes (kgWaveOp d) (fun y : Fin (d + 1) → ℝ => P (y 0, kgSpatial d y)) :=
  regularOpenProbes_of_locally_kgChartPotential hN
    (exists_locally_kgChartPotential_of_smooth_spacetime hP)

end RegularProbes

/-! ## Transfer along a conformal rescaling -/

section Transfer

variable {d : ℕ} (M : SmoothMetricChart d)

open ExponentialSecondOrderClockCalculus

/-- **Regular probes transfer along a conformal rescaling of the chart.** The conjugated field is
again regular, so the transfer may be iterated. -/
theorem regularOpenProbes_conformalRescale {sigma : (Fin d → ℝ) → ℝ}
    (hsigma : ContDiff ℝ ∞ sigma) {V : (Fin d → ℝ) → ℝ}
    (h : RegularOpenProbes M.dalembert V) :
    RegularOpenProbes (M.conformalRescale sigma hsigma).dalembert
      (M.conformalTransferPotential sigma V) := by
  intro x
  obtain ⟨W, hWopen, hxW, u, hureg, hu, hune⟩ := h x
  have hweight : ContDiff ℝ ∞ fun y => Real.exp (-conformalDimensionWeight d * sigma y) :=
    Real.contDiff_exp.comp (contDiff_const.mul hsigma)
  refine ⟨W, hWopen, hxW,
    fun y => Real.exp (-conformalDimensionWeight d * sigma y) * u y,
    SmoothMetricChart.DifferentiablePartials.mul_left hweight hureg, fun z hz => ?_,
    fun z hz => ?_⟩
  · exact M.solvesPotentialWaveAt_conformalRescale sigma hsigma hureg (hu z hz)
  · exact mul_ne_zero (Real.exp_ne_zero _) (hune z hz)

end Transfer

end GaloisForLFunctions.HTGeometry
