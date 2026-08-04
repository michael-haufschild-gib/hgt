import GaloisForLFunctions.HTGeometry.HillChartWave
import GaloisForLFunctions.HTGeometry.KleinGordonProbeExamples
import GaloisForLFunctions.HTGeometry.ClockPotentialLocalDetermination

/-!
# Clock probes for a wave operator of variable speed

The wave operator of a speed `c` on the chart is the alternating sum of the pure second coordinate
derivatives, the spatial ones weighted by `c(t)²`. The field equation says exactly that the chart
field of the evolution solves the dressed equation for the constant potential `-m²`.

A compactly supported datum whose synthesis at a prescribed point is positive — the symmetrised bump
of the corpus, modulated by the conjugate character — makes the field nonvanishing on a whole
neighbourhood of the event, so the corpus's local-probe interface is met there.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

open scoped RealInnerProductSpace

section WaveOperator

variable {d : ℕ} {m K C cmin : ℝ} {c dc : ℝ → ℝ} {G : EuclideanSpace ℝ (Fin d) → ℂ}

/-- The wave operator of a time-dependent speed on the chart. -/
noncomputable def hillWaveOp (d : ℕ) (c : ℝ → ℝ) :
    ((Fin (d + 1) → ℝ) → ℝ) → (Fin (d + 1) → ℝ) → ℝ :=
  fun u y => -(coordPartial 0 (coordPartial 0 u) y) +
    c (y 0) ^ 2 * ∑ i : Fin d, coordPartial i.succ (coordPartial i.succ u) y

/-- **The chart field solves the potential-dressed wave equation** of its own speed, for the
constant potential `-m²`. -/
theorem solvesPotentialWave_hillChartField (hm : 0 < m) (hc : Continuous c)
    (hcd : ∀ r, HasDerivAt c (dc r) r) (hcpos : ∀ r, 0 < c r) (hK : ∀ r, |dc r| ≤ K * c r)
    (hC : ∀ r, c r ^ 2 ≤ C ^ 2) (hcmin : 0 < cmin) (hclow : ∀ r, cmin ≤ c r) (hG : Continuous G)
    (h2 : Integrable (fun ξ : EuclideanSpace ℝ (Fin d) => kgFreq ξ ^ 2 * ‖G ξ‖) (volume)) :
    SolvesPotentialWave (hillWaveOp d c) (fun _ => -(m ^ 2)) (hillChartField m c G) := by
  intro y
  have hwave := hillChartField_wave_identity (C := C) hm hc hcd hcpos hK hC hcmin hclow hG h2 y
  show hillWaveOp d c (hillChartField m c G) y + -(m ^ 2) * hillChartField m c G y = 0
  rw [hillWaveOp, hwave]
  ring

end WaveOperator

section Datum

variable {d : ℕ}

/-- A compactly supported datum whose synthesis at a prescribed point is positive. -/
noncomputable def hillProbeDatum (d : ℕ) (x₀ : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) → ℂ := fun ξ => kgConjChar x₀ ξ * kgBumpFun d ξ

theorem continuous_hillProbeDatum (x₀ : EuclideanSpace ℝ (Fin d)) :
    Continuous (hillProbeDatum d x₀) :=
  (Complex.continuous_conj.comp (continuous_kgChar' x₀)).mul (continuous_kgBumpFun d)

theorem hasCompactSupport_hillProbeDatum (x₀ : EuclideanSpace ℝ (Fin d)) :
    HasCompactSupport (hillProbeDatum d x₀) :=
  HasCompactSupport.mul_left (hasCompactSupport_kgBumpFun d)

/-- **The datum is admissible at every weight.** -/
theorem integrable_kgFreq_pow_mul_hillProbeDatum (x₀ : EuclideanSpace ℝ (Fin d)) (N : ℕ) :
    Integrable (fun ξ : EuclideanSpace ℝ (Fin d) => kgFreq ξ ^ N * ‖hillProbeDatum d x₀ ξ‖)
      (volume) := by
  have hcs : HasCompactSupport
      (fun ξ : EuclideanSpace ℝ (Fin d) => kgFreq ξ ^ N * ‖hillProbeDatum d x₀ ξ‖) := by
    have h : HasCompactSupport ((fun ξ : EuclideanSpace ℝ (Fin d) => kgFreq ξ ^ N) *
        fun ξ : EuclideanSpace ℝ (Fin d) => ‖hillProbeDatum d x₀ ξ‖) :=
      HasCompactSupport.mul_left (hasCompactSupport_hillProbeDatum x₀).norm
    exact h
  exact Continuous.integrable_of_hasCompactSupport
    ((continuous_kgFreq.pow N).mul (continuous_hillProbeDatum x₀).norm) hcs

/-- **The synthesis of the datum at its own point is the integral of the bump.** -/
theorem kgSynthesis_hillProbeDatum (x₀ : EuclideanSpace ℝ (Fin d)) :
    kgSynthesis (hillProbeDatum d x₀) x₀
      = (((∫ η : EuclideanSpace ℝ (Fin d), ((kgBump d) η + (kgBump d) (-η))) : ℝ) : ℂ) := by
  rw [kgSynthesis, ← integral_complex_ofReal]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  show kgChar x₀ ξ * (kgConjChar x₀ ξ * kgBumpFun d ξ)
    = (((kgBump d) ξ + (kgBump d) (-ξ) : ℝ) : ℂ)
  rw [← mul_assoc, kgChar_mul_kgConjChar, one_mul, kgBumpFun]

/-- **The real part of that synthesis is positive.** -/
theorem re_kgSynthesis_hillProbeDatum_ne_zero (x₀ : EuclideanSpace ℝ (Fin d)) :
    (kgSynthesis (hillProbeDatum d x₀) x₀).re ≠ 0 := by
  rw [kgSynthesis_hillProbeDatum, Complex.ofReal_re]
  exact ne_of_gt (integral_kgBumpFun_pos d)

end Datum

section Probes

variable {d : ℕ} {m K C cmin : ℝ} {c dc : ℝ → ℝ}

/-- **Clock probes for the wave operator of a variable speed**, on a neighbourhood of any event of
the initial slice. -/
theorem exists_localProbesOn_hillWaveOp (hm : 0 < m) (hc : Continuous c)
    (hcd : ∀ r, HasDerivAt c (dc r) r) (hcpos : ∀ r, 0 < c r) (hK : ∀ r, |dc r| ≤ K * c r)
    (hC : ∀ r, c r ^ 2 ≤ C ^ 2) (hcmin : 0 < cmin) (hclow : ∀ r, cmin ≤ c r)
    {y₀ : Fin (d + 1) → ℝ} (hy₀ : y₀ 0 = 0) :
    ∃ region : Set (Fin (d + 1) → ℝ), IsOpen region ∧ y₀ ∈ region ∧
      LocalProbesOn (hillWaveOp d c) (fun _ => -(m ^ 2)) region := by
  set x₀ : EuclideanSpace ℝ (Fin d) := kgSpatial d y₀ with hx₀
  set G : EuclideanSpace ℝ (Fin d) → ℂ := hillProbeDatum d x₀ with hG'
  have hG : Continuous G := continuous_hillProbeDatum x₀
  have h2 : Integrable (fun ξ : EuclideanSpace ℝ (Fin d) => kgFreq ξ ^ 2 * ‖G ξ‖) (volume) :=
    integrable_kgFreq_pow_mul_hillProbeDatum x₀ 2
  have h1 := integrable_kgFreq_mul_of_sq hG h2
  have h0 := integrable_of_kgFreq_mul hG h1
  have hne : (kgSynthesis G x₀).re ≠ 0 := re_kgSynthesis_hillProbeDatum_ne_zero x₀
  have hnear := eventually_hillChartField_ne_zero (m := m) (c := c) (C := C) (cmin := cmin)
    hm hc hcd hcpos hK hC hcmin hclow hG h0 hy₀ hne
  obtain ⟨region, hsub, hopen, hmem⟩ := mem_nhds_iff.mp hnear
  refine ⟨region, hopen, hmem, fun y hy => ?_⟩
  exact ⟨hillChartField m c G,
    solvesPotentialWave_hillChartField (C := C) hm hc hcd hcpos hK hC hcmin hclow hG h2 y,
    hsub hy⟩

end Probes

end GaloisForLFunctions.HTGeometry
