import GaloisForLFunctions.HTGeometry.HillDrivenProbeDatum
import GaloisForLFunctions.HTGeometry.ClockPotentialLocalDetermination
import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonSpacetimeProbe

/-!
# Clock probes of a variable speed, with a potential

The driven chart field solves the potential-dressed wave equation of its speed everywhere, and the
datum of the previous file makes it positive at a prescribed event of the initial slice. Continuity
spreads that to a neighbourhood, so the corpus's local-probe interface is met there — now for the
potential of an arbitrary admissible convolving family, not just for a constant.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory BoundedContinuousFunction

open scoped ContDiff

section Probe

variable {d K : ℕ}

/-- **Clock probes for the wave operator of a variable speed, dressed by the potential of a real
family**, on a neighbourhood of any event of the initial slice. -/
theorem exists_localProbesOn_hillDrivenChart
    (hK : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) < K) (a : HillSpeed)
    (b : WienerFamily (EuclideanSpace ℝ (Fin d)) (K + 2)) (hreal : IsRealFamily b)
    (x₀ : EuclideanSpace ℝ (Fin d)) :
    ∃ region : Set (Fin (d + 1) → ℝ), IsOpen region ∧ kgChartEvent d x₀ ∈ region ∧
      LocalProbesOn (hillWaveOp d a.speed)
        (fun y => hillDrivenChartPotential b y - a.mass ^ (2 : ℕ)) region := by
  have hdim : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) < (K + 2 : ℕ) := by
    push_cast
    linarith
  have hN : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) + 1 < (K + 2 : ℕ) := by
    push_cast
    linarith
  have hcont : Continuous (hillDrivenChartField a b (hillDrivenProbeDatum d x₀)) :=
    continuous_hillDrivenChartField hdim a b (hillDrivenProbeDatum d x₀)
  have hpos : 0 < hillDrivenChartField a b (hillDrivenProbeDatum d x₀) (kgChartEvent d x₀) :=
    hillDrivenChartField_event_pos hdim a b x₀
  have hne : ∀ᶠ y in nhds (kgChartEvent d x₀),
      hillDrivenChartField a b (hillDrivenProbeDatum d x₀) y ≠ 0 :=
    hcont.continuousAt.eventually_ne (ne_of_gt hpos)
  obtain ⟨region, hsub, hopen, hmem⟩ := mem_nhds_iff.mp hne
  refine ⟨region, hopen, hmem, fun y hy => ?_⟩
  exact ⟨hillDrivenChartField a b (hillDrivenProbeDatum d x₀),
    solvesPotentialWave_hillDrivenChartField hK a b (hillDrivenProbeDatum d x₀) hreal y,
    hsub hy⟩

/-- **The probes determine the dressed potential on their region.** -/
theorem potential_eqOn_of_hillDrivenProbes
    (hK : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) < K) (a : HillSpeed)
    (b : WienerFamily (EuclideanSpace ℝ (Fin d)) (K + 2)) (hreal : IsRealFamily b)
    (x₀ : EuclideanSpace ℝ (Fin d)) {other : (Fin (d + 1) → ℝ) → ℝ} :
    ∃ region : Set (Fin (d + 1) → ℝ), IsOpen region ∧ kgChartEvent d x₀ ∈ region ∧
      ((∀ (u : (Fin (d + 1) → ℝ) → ℝ) (y : Fin (d + 1) → ℝ),
        SolvesPotentialWaveAt (hillWaveOp d a.speed)
            (fun z => hillDrivenChartPotential b z - a.mass ^ (2 : ℕ)) u y →
          SolvesPotentialWaveAt (hillWaveOp d a.speed) other u y) →
        Set.EqOn other (fun y => hillDrivenChartPotential b y - a.mass ^ (2 : ℕ)) region) := by
  obtain ⟨region, hopen, hmem, hprobes⟩ :=
    exists_localProbesOn_hillDrivenChart hK a b hreal x₀
  refine ⟨region, hopen, hmem, fun h => ?_⟩
  refine potential_eqOn_of_localProbes (wave := hillWaveOp d a.speed) (fun y hy => ?_)
  obtain ⟨u, hu, hune⟩ := hprobes y hy
  exact ⟨u, hu, h u y hu, hune⟩


/-! ## An arbitrary smooth potential -/

theorem hillDrivenChartPotential_eq (b : WienerFamily (EuclideanSpace ℝ (Fin d)) (K + 2))
    (y : Fin (d + 1) → ℝ) : hillDrivenChartPotential b y = kgChartPotential b y + 1 := by
  rw [hillDrivenChartPotential, kgChartPotential]
  ring

/-- **Clock probes for a variable speed and an arbitrary smooth potential**, on a neighbourhood of
any event of the initial slice.

The potential is realized as the chart potential of a real convolving family — the same realization
as in the flat case — and the driven field of that family is the probe. -/
theorem exists_localProbesOn_hillWaveOp_smooth
    (hK : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) < K) (a : HillSpeed)
    {P : ℝ × EuclideanSpace ℝ (Fin d) → ℝ} (hP : ContDiff ℝ ∞ P)
    (x₀ : EuclideanSpace ℝ (Fin d)) :
    ∃ region : Set (Fin (d + 1) → ℝ), IsOpen region ∧ kgChartEvent d x₀ ∈ region ∧
      LocalProbesOn (hillWaveOp d a.speed)
        (fun y : Fin (d + 1) → ℝ => P (y 0, kgSpatial d y)) region := by
  have hP' : ContDiff ℝ ∞ fun p : ℝ × EuclideanSpace ℝ (Fin d) => P p + (a.mass ^ (2 : ℕ) - 1) :=
    hP.add contDiff_const
  obtain ⟨B, W, hBreal, hWopen, hWmem, hWeq⟩ :=
    exists_locally_kgChartPotential_of_smooth_spacetime (N := K + 2) hP' (kgChartEvent d x₀)
  obtain ⟨R, hRopen, hRmem, hRprobes⟩ := exists_localProbesOn_hillDrivenChart hK a B hBreal x₀
  refine ⟨W ∩ R, hWopen.inter hRopen, ⟨hWmem, hRmem⟩, fun y hy => ?_⟩
  obtain ⟨u, hu, hune⟩ := hRprobes y hy.2
  refine ⟨u, ?_, hune⟩
  have hpot : hillDrivenChartPotential B y - a.mass ^ (2 : ℕ) = P (y 0, kgSpatial d y) := by
    have hval := hWeq hy.1
    rw [hillDrivenChartPotential_eq, ← hval]
    ring
  show hillWaveOp d a.speed u y + P (y 0, kgSpatial d y) * u y = 0
  rw [← hpot]
  exact hu

end Probe

end GaloisForLFunctions.HTGeometry
