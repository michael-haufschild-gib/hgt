import GaloisForLFunctions.RHTower.ChiDualUnitAmplitudeJets

open Complex Set Filter Topology MeasureTheory
noncomputable section
namespace RHTower


private theorem continuousOn_chiDualUnitPower (j : ℂ) :
    ContinuousOn (fun p : ℂ × ℝ => (p.2 : ℂ) ^ (p.1 - j)) {p | 0 < p.2} := by
  have hlog : ContinuousOn (fun p : ℂ × ℝ => Real.log p.2) {p | 0 < p.2} :=
    (contDiffOn_id.log (fun _ hx => ne_of_gt hx) :
      ContDiffOn ℝ 2 Real.log (Ioi (0 : ℝ))).continuousOn.comp
        continuous_snd.continuousOn (fun _ hx => hx)
  have he : ContinuousOn (fun p : ℂ × ℝ =>
      Complex.exp ((Real.log p.2 : ℂ) * (p.1 - j))) {p | 0 < p.2} := by fun_prop
  apply he.congr
  intro p hp
  dsimp only
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (ne_of_gt hp)),
    ← Complex.ofReal_log (le_of_lt hp)]

/-- All three literal amplitude jets are jointly continuous on the positive
spatial ray, including their compact complex parameter. -/
theorem continuousOn_chiDualUnitSpatialJets :
    ContinuousOn (fun p : ℂ × ℝ => chiDualUnitSpatialAmplitude p.1 p.2) {p | 0 < p.2} ∧
    ContinuousOn (fun p : ℂ × ℝ => chiDualUnitSpatialFirst p.1 p.2) {p | 0 < p.2} ∧
    ContinuousOn (fun p : ℂ × ℝ => chiDualUnitSpatialSecond p.1 p.2) {p | 0 < p.2} := by
  have hc1 : ContDiffOn ℝ 1 (deriv smoothAFECutoff) (Ioi (0 : ℝ)) :=
    contDiffOn_smoothAFECutoff_pos.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hc2 : ContDiffOn ℝ 0 (deriv (deriv smoothAFECutoff)) (Ioi (0 : ℝ)) :=
    hc1.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have h0 : ContinuousOn (fun p : ℂ × ℝ => smoothAFECutoff p.2) {p | 0 < p.2} :=
    contDiffOn_smoothAFECutoff_pos.continuousOn.comp continuous_snd.continuousOn (fun _ hx => hx)
  have h1 : ContinuousOn (fun p : ℂ × ℝ => deriv smoothAFECutoff p.2) {p | 0 < p.2} :=
    hc1.continuousOn.comp continuous_snd.continuousOn (fun _ hx => hx)
  have h2 : ContinuousOn (fun p : ℂ × ℝ => deriv (deriv smoothAFECutoff) p.2)
      {p | 0 < p.2} :=
    hc2.continuousOn.comp continuous_snd.continuousOn (fun _ hx => hx)
  have hp1 := continuousOn_chiDualUnitPower 1
  have hp2 := continuousOn_chiDualUnitPower 2
  have hp3 := continuousOn_chiDualUnitPower 3
  refine ⟨?_, ?_, ?_⟩
  · unfold chiDualUnitSpatialAmplitude
    fun_prop
  · unfold chiDualUnitSpatialFirst
    fun_prop
  · unfold chiDualUnitSpatialSecond
    fun_prop

/-- A single positive bound controls the actual first two spatial derivatives
and the amplitude itself on every fixed compact disc and normalized block. -/
theorem exists_chiDualUnitSpatialJets_bound (c : ℂ) (r : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s ∈ Metric.closedBall c r, ∀ x ∈ Icc (1 / 6 : ℝ) (1 / 3),
      ‖chiDualUnitSpatialAmplitude s x‖ ≤ C ∧
      ‖chiDualUnitSpatialFirst s x‖ ≤ C ∧
      ‖chiDualUnitSpatialSecond s x‖ ≤ C := by
  let K : Set (ℂ × ℝ) := Metric.closedBall c r ×ˢ Icc (1 / 6 : ℝ) (1 / 3)
  have hK : IsCompact K := (isCompact_closedBall c r).prod isCompact_Icc
  have hsub : K ⊆ {p : ℂ × ℝ | 0 < p.2} := by
    intro p hp
    have hx : (1 / 6 : ℝ) ≤ p.2 := hp.2.1
    change 0 < p.2
    linarith
  obtain ⟨h0, h1, h2⟩ := continuousOn_chiDualUnitSpatialJets
  obtain ⟨C0, hC0⟩ := hK.exists_bound_of_continuousOn (h0.mono hsub)
  obtain ⟨C1, hC1⟩ := hK.exists_bound_of_continuousOn (h1.mono hsub)
  obtain ⟨C2, hC2⟩ := hK.exists_bound_of_continuousOn (h2.mono hsub)
  refine ⟨1 + |C0| + |C1| + |C2|, by positivity, ?_⟩
  intro s hs x hx
  have hp : (s, x) ∈ K := ⟨hs, hx⟩
  have hbound0 := hC0 (s, x) hp
  have hbound1 := hC1 (s, x) hp
  have hbound2 := hC2 (s, x) hp
  dsimp only at hbound0 hbound1 hbound2
  constructor
  · linarith [le_abs_self C0, abs_nonneg C1, abs_nonneg C2]
  constructor
  · linarith [le_abs_self C1, abs_nonneg C0, abs_nonneg C2]
  · linarith [le_abs_self C2, abs_nonneg C0, abs_nonneg C1]

end RHTower
