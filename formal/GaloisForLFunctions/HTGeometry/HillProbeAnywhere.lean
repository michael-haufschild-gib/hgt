import GaloisForLFunctions.HTGeometry.HillClockProbe
import GaloisForLFunctions.HTGeometry.KleinGordonProbeAnywhere
import GaloisForLFunctions.HTGeometry.KleinGordonRegularProbes

/-!
# A probe at every event of a variable-speed chart

The evolution starts on the slice `t = 0`, so its field is only known to be nonvanishing near events
of that slice. Shifting the speed in time moves the initial slice to any prescribed time, and
translating the resulting field back in the chart returns a solution of the *original* equation:
the wave operator of a speed is carried to the wave operator of the shifted speed by a translation
of the time coordinate.

That gives a nonvanishing solution on a neighbourhood of an arbitrary event, which is the corpus's
`OpenProbes` interface for the constant potential `-m²`.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

open scoped RealInnerProductSpace

section Shift

variable {d : ℕ} {m K C cmin : ℝ} {c dc : ℝ → ℝ} {G : EuclideanSpace ℝ (Fin d) → ℂ}

/-- The speed, restarted at a prescribed time. -/
noncomputable def hillSpeedShift (c : ℝ → ℝ) (t₀ : ℝ) : ℝ → ℝ := fun s => c (s + t₀)

theorem hillSpeedShift_apply (c : ℝ → ℝ) (t₀ s : ℝ) : hillSpeedShift c t₀ s = c (s + t₀) := rfl

theorem continuous_hillSpeedShift (hc : Continuous c) (t₀ : ℝ) :
    Continuous (hillSpeedShift c t₀) := hc.comp (continuous_id.add continuous_const)

theorem hasDerivAt_hillSpeedShift (hcd : ∀ r, HasDerivAt c (dc r) r) (t₀ r : ℝ) :
    HasDerivAt (hillSpeedShift c t₀) (dc (r + t₀)) r :=
  HasDerivAt.comp_add_const r t₀ (hcd (r + t₀))

theorem hillSpeedShift_pos (hcpos : ∀ r, 0 < c r) (t₀ : ℝ) : ∀ r, 0 < hillSpeedShift c t₀ r :=
  fun r => hcpos (r + t₀)

theorem hillSpeedShift_deriv_le (hK : ∀ r, |dc r| ≤ K * c r) (t₀ : ℝ) :
    ∀ r, |dc (r + t₀)| ≤ K * hillSpeedShift c t₀ r := fun r => hK (r + t₀)

theorem hillSpeedShift_sq_le (hC : ∀ r, c r ^ (2 : ℕ) ≤ C ^ (2 : ℕ)) (t₀ : ℝ) :
    ∀ r, hillSpeedShift c t₀ r ^ (2 : ℕ) ≤ C ^ (2 : ℕ) := fun r => hC (r + t₀)

theorem hillSpeedShift_low (hclow : ∀ r, cmin ≤ c r) (t₀ : ℝ) :
    ∀ r, cmin ≤ hillSpeedShift c t₀ r := fun r => hclow (r + t₀)

/-- **The wave operator of a speed is the wave operator of the shifted speed, translated.** -/
theorem hillWaveOp_comp_add_const (hm : 0 < m) (hc : Continuous c)
    (hcd : ∀ r, HasDerivAt c (dc r) r) (hcpos : ∀ r, 0 < c r) (hK : ∀ r, |dc r| ≤ K * c r)
    (hC : ∀ r, c r ^ (2 : ℕ) ≤ C ^ (2 : ℕ)) (hcmin : 0 < cmin) (hclow : ∀ r, cmin ≤ c r) (hG : Continuous G)
    (h2 : Integrable (fun ξ : EuclideanSpace ℝ (Fin d) => kgFreq ξ ^ (2 : ℕ) * ‖G ξ‖) (volume))
    (t₀ : ℝ) (y : Fin (d + 1) → ℝ) :
    hillWaveOp d c
        (fun z : Fin (d + 1) → ℝ =>
          hillChartField m (hillSpeedShift c t₀) G (z + kgTimeShiftVec d t₀)) y
      = hillWaveOp d (hillSpeedShift c t₀) (hillChartField m (hillSpeedShift c t₀) G)
          (y + kgTimeShiftVec d t₀) := by
  have hcs := continuous_hillSpeedShift hc t₀
  have hcsd := hasDerivAt_hillSpeedShift (dc := dc) hcd t₀
  have hcspos := hillSpeedShift_pos hcpos t₀
  have hcsK := hillSpeedShift_deriv_le (K := K) hK t₀
  have hcsC := hillSpeedShift_sq_le (C := C) hC t₀
  have hcslow := hillSpeedShift_low (cmin := cmin) hclow t₀
  have h1 := integrable_kgFreq_mul_of_sq hG h2
  have h0 := integrable_of_kgFreq_mul hG h1
  have hwA := integrable_massWeight (c := hillSpeedShift c t₀) hm (hcspos 0) hG h1
  have hdiff1 : ∀ z : Fin (d + 1) → ℝ,
      DifferentiableAt ℝ (hillChartField m (hillSpeedShift c t₀) G) z := fun z =>
    (hasFDerivAt_hillChartField (C := C) hm hcs hcsd hcspos hcsK hcsC hcmin hcslow hG h0 hwA h1
      z).differentiableAt
  have hdiff2 : ∀ (j : Fin (d + 1)) (z : Fin (d + 1) → ℝ),
      DifferentiableAt ℝ (coordPartial j (hillChartField m (hillSpeedShift c t₀) G)) z :=
    fun j z => differentiableAt_coordPartial_hillChartField (C := C) hm hcs hcsd hcspos hcsK hcsC
      hcmin hcslow hG h2 j z
  have hspeed : hillSpeedShift c t₀ ((y + kgTimeShiftVec d t₀) 0) = c (y 0) := by
    rw [add_kgTimeShiftVec_zero]
    show c (y 0 - t₀ + t₀) = c (y 0)
    congr 1
    ring
  rw [hillWaveOp, hillWaveOp, hspeed,
    coordPartial_sq_comp_add_const hdiff1 hdiff2 0 y]
  congr 2
  exact Finset.sum_congr rfl fun i _ => coordPartial_sq_comp_add_const hdiff1 hdiff2 i.succ y

/-! ## The probe at an arbitrary event -/

/-- **A clock probe at every event of the variable-speed chart**, with its regularity: a
nonvanishing solution of the dressed equation for the constant potential `-m²` on an open
neighbourhood of the event, whose partial derivatives are differentiable. -/
theorem exists_hillProbe_at (hm : 0 < m) (hc : Continuous c)
    (hcd : ∀ r, HasDerivAt c (dc r) r) (hcpos : ∀ r, 0 < c r) (hK : ∀ r, |dc r| ≤ K * c r)
    (hC : ∀ r, c r ^ (2 : ℕ) ≤ C ^ (2 : ℕ)) (hcmin : 0 < cmin) (hclow : ∀ r, cmin ≤ c r)
    (y₀ : Fin (d + 1) → ℝ) :
    ∃ (W : Set (Fin (d + 1) → ℝ)) (u : (Fin (d + 1) → ℝ) → ℝ), IsOpen W ∧ y₀ ∈ W ∧
      SmoothMetricChart.DifferentiablePartialsOn u W ∧
      SolvesPotentialWaveOn (hillWaveOp d c) (fun _ => -(m ^ (2 : ℕ))) u W ∧ (∀ y ∈ W, u y ≠ 0) := by
  set t₀ : ℝ := y₀ 0 with ht₀
  set sh : Fin (d + 1) → ℝ := kgTimeShiftVec d t₀ with hsh
  set x₀ : EuclideanSpace ℝ (Fin d) := kgSpatial d y₀ with hx₀
  set G : EuclideanSpace ℝ (Fin d) → ℂ := hillProbeDatum d x₀ with hG'
  have hG : Continuous G := continuous_hillProbeDatum x₀
  have h2 : Integrable (fun ξ : EuclideanSpace ℝ (Fin d) => kgFreq ξ ^ (2 : ℕ) * ‖G ξ‖) (volume) :=
    integrable_kgFreq_pow_mul_hillProbeDatum x₀ 2
  have h1 := integrable_kgFreq_mul_of_sq hG h2
  have h0 := integrable_of_kgFreq_mul hG h1
  have hcs := continuous_hillSpeedShift hc t₀
  have hcsd := hasDerivAt_hillSpeedShift (dc := dc) hcd t₀
  have hcspos := hillSpeedShift_pos hcpos t₀
  have hcsK := hillSpeedShift_deriv_le (K := K) hK t₀
  have hcsC := hillSpeedShift_sq_le (C := C) hC t₀
  have hcslow := hillSpeedShift_low (cmin := cmin) hclow t₀
  have hzero : (y₀ + sh) 0 = 0 := by
    rw [hsh, add_kgTimeShiftVec_zero, ht₀]
    ring
  have hspatial : kgSpatial d (y₀ + sh) = x₀ := by
    rw [hsh, kgSpatial_add_kgTimeShiftVec]
  have hne : (kgSynthesis G (kgSpatial d (y₀ + sh))).re ≠ 0 := by
    rw [hspatial]
    exact re_kgSynthesis_hillProbeDatum_ne_zero x₀
  have hnear := eventually_hillChartField_ne_zero (m := m) (c := hillSpeedShift c t₀) (C := C)
    (cmin := cmin) hm hcs hcsd hcspos hcsK hcsC hcmin hcslow hG h0 hzero hne
  have hmap : Filter.Tendsto (fun z : Fin (d + 1) → ℝ => z + sh) (nhds y₀) (nhds (y₀ + sh)) :=
    (continuous_id.add continuous_const).continuousAt
  obtain ⟨region, hsub, hopen, hmem⟩ := mem_nhds_iff.mp (hmap.eventually hnear)
  have hwA := integrable_massWeight (c := hillSpeedShift c t₀) hm (hcspos 0) hG h1
  have hdiff1 : ∀ z : Fin (d + 1) → ℝ,
      DifferentiableAt ℝ (hillChartField m (hillSpeedShift c t₀) G) z := fun z =>
    (hasFDerivAt_hillChartField (C := C) hm hcs hcsd hcspos hcsK hcsC hcmin hcslow hG h0 hwA h1
      z).differentiableAt
  have hdiff2 : ∀ (j : Fin (d + 1)) (z : Fin (d + 1) → ℝ),
      DifferentiableAt ℝ (coordPartial j (hillChartField m (hillSpeedShift c t₀) G)) z :=
    fun j z => differentiableAt_coordPartial_hillChartField (C := C) hm hcs hcsd hcspos hcsK hcsC
      hcmin hcslow hG h2 j z
  refine ⟨region, fun z : Fin (d + 1) → ℝ =>
    hillChartField m (hillSpeedShift c t₀) G (z + sh), hopen, hmem, ⟨?_, ?_⟩, fun y hy => ?_,
    fun y hy => hsub hy⟩
  · exact fun z _ => differentiableAt_comp_add_const hdiff1 z
  · intro j z _
    rw [coordPartial_comp_add_const_fun hdiff1 j]
    exact differentiableAt_comp_add_const (hdiff2 j) z
  · have hsolve := solvesPotentialWave_hillChartField (C := C) hm hcs hcsd hcspos hcsK hcsC hcmin
      hcslow hG h2 (y + sh)
    show hillWaveOp d c
        (fun z : Fin (d + 1) → ℝ => hillChartField m (hillSpeedShift c t₀) G (z + sh)) y +
      -(m ^ (2 : ℕ)) * hillChartField m (hillSpeedShift c t₀) G (y + sh) = 0
    rw [hillWaveOp_comp_add_const (C := C) (cmin := cmin) hm hc hcd hcpos hK hC hcmin hclow hG h2
      t₀ y]
    exact hsolve

/-- **A clock probe at every event**: the corpus's `OpenProbes` interface for the constant
potential `-m²`. -/
theorem openProbes_hillWaveOp (hm : 0 < m) (hc : Continuous c)
    (hcd : ∀ r, HasDerivAt c (dc r) r) (hcpos : ∀ r, 0 < c r) (hK : ∀ r, |dc r| ≤ K * c r)
    (hC : ∀ r, c r ^ (2 : ℕ) ≤ C ^ (2 : ℕ)) (hcmin : 0 < cmin) (hclow : ∀ r, cmin ≤ c r) :
    OpenProbes (hillWaveOp d c) (fun _ => -(m ^ (2 : ℕ))) := by
  intro y₀
  obtain ⟨W, u, hopen, hmem, _, hsolve, hne⟩ :=
    exists_hillProbe_at (C := C) hm hc hcd hcpos hK hC hcmin hclow y₀
  exact ⟨W, hopen, hmem, u, hsolve, hne⟩

/-- **The probes carry their regularity**: the interface the conformal transfer consumes. -/
theorem regularOpenProbes_hillWaveOp (hm : 0 < m) (hc : Continuous c)
    (hcd : ∀ r, HasDerivAt c (dc r) r) (hcpos : ∀ r, 0 < c r) (hK : ∀ r, |dc r| ≤ K * c r)
    (hC : ∀ r, c r ^ (2 : ℕ) ≤ C ^ (2 : ℕ)) (hcmin : 0 < cmin) (hclow : ∀ r, cmin ≤ c r) :
    RegularOpenProbes (hillWaveOp d c) (fun _ => -(m ^ (2 : ℕ))) := by
  intro y₀
  obtain ⟨W, u, hopen, hmem, hreg, hsolve, hne⟩ :=
    exists_hillProbe_at (C := C) hm hc hcd hcpos hK hC hcmin hclow y₀
  exact ⟨W, hopen, hmem, u, hreg, hsolve, hne⟩

end Shift

end GaloisForLFunctions.HTGeometry
