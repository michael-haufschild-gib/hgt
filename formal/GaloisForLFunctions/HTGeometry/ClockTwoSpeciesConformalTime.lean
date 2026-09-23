import GaloisForLFunctions.HTGeometry.ClockProbePlaneWave
import GaloisForLFunctions.HTGeometry.ConformalClockTwoSpeciesScaleLaw

/-!
# The two-species law closed end to end in conformal time

For a conformal factor depending only on the zeroth coordinate — the cosmological case, where
`e^{2σ}η` is the Friedmann geometry written in conformal time — the effective potential of a clock
species is itself a function of the zeroth coordinate:

`V_μ^σ(x) = μ e^{2σ(x⁰)} - a (ε₀)⁻¹ σ''(x⁰) - a² (ε₀)⁻¹ σ'(x⁰)²`.

The flat base chart is homogeneous, so local probes exist for that potential unconditionally, and
each species' potential is pinned by its own clock data. Subtracting the two and dividing by the
calibrated mass difference returns `e^{2σ}` exactly.

This is the headline claim of the card, discharged with no nondegeneracy hypothesis for the
cosmological conformal class.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

open scoped ContDiff

variable {d : ℕ}

/-! ## The lifted conformal factor on a flat chart -/

theorem contDiff_timeLift {σ₀ : ℝ → ℝ} (hσ : ContDiff ℝ ∞ σ₀) :
    ContDiff ℝ ∞ (timeLift (d := d) σ₀) :=
  hσ.comp (contDiff_apply ℝ ℝ 0)

theorem contDiff_deriv_infty {σ₀ : ℝ → ℝ} (hσ : ContDiff ℝ ∞ σ₀) :
    ContDiff ℝ ∞ (deriv σ₀) := (contDiff_infty_iff_deriv.mp hσ).2

theorem coordPartial_timeLift_deriv {σ₀ : ℝ → ℝ} (hσ : ContDiff ℝ ∞ σ₀)
    (x : Fin (d + 1) → ℝ) :
    coordPartial (0 : Fin (d + 1)) (timeLift σ₀) x = deriv σ₀ (x 0) :=
  coordPartial_timeLift_zero ((hσ.differentiable (by simp) (x 0)).hasDerivAt)

theorem coordPartial_timeLift_eq {σ₀ : ℝ → ℝ} (hσ : ContDiff ℝ ∞ σ₀) :
    coordPartial (0 : Fin (d + 1)) (timeLift σ₀) = timeLift (deriv σ₀) := by
  funext x
  exact coordPartial_timeLift_deriv hσ x

theorem coordPartial_timeLift_eq_zero (σ₀ : ℝ → ℝ) {i : Fin (d + 1)} (hi : i ≠ 0) :
    coordPartial i (timeLift (d := d) σ₀) = fun _ => 0 := by
  funext x
  exact coordPartial_timeLift_of_ne σ₀ hi x

theorem coordPartial_sq_timeLift {σ₀ : ℝ → ℝ} (hσ : ContDiff ℝ ∞ σ₀) (i : Fin (d + 1))
    (x : Fin (d + 1) → ℝ) :
    coordPartial i (coordPartial i (timeLift σ₀)) x
      = if i = 0 then deriv (deriv σ₀) (x 0) else 0 := by
  by_cases hi : i = 0
  · subst hi
    rw [coordPartial_timeLift_eq hσ, if_pos rfl]
    exact coordPartial_timeLift_deriv (contDiff_deriv_infty hσ) x
  · rw [coordPartial_timeLift_eq_zero σ₀ hi, if_neg hi]
    exact coordPartial_const i 0 x

theorem dalembert_timeLift_flat (eps : Fin (d + 1) → ℝ) (heps : ∀ i, eps i ≠ 0)
    {σ₀ : ℝ → ℝ} (hσ : ContDiff ℝ ∞ σ₀) (x : Fin (d + 1) → ℝ) :
    (SmoothPseudoMetric.ofSignature eps heps).chart.dalembert (timeLift σ₀) x
      = (eps 0)⁻¹ * deriv (deriv σ₀) (x 0) := by
  rw [SmoothPseudoMetric.ofSignature_dalembert eps heps (contDiff_timeLift hσ) x,
    Finset.sum_eq_single (0 : Fin (d + 1))]
  · rw [coordPartial_sq_timeLift hσ, if_pos rfl]
  · intro i _ hi
    rw [coordPartial_sq_timeLift hσ, if_neg hi, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ (0 : Fin (d + 1))) h

theorem gradPair_timeLift_flat (eps : Fin (d + 1) → ℝ) (heps : ∀ i, eps i ≠ 0)
    {σ₀ : ℝ → ℝ} (hσ : ContDiff ℝ ∞ σ₀) (x : Fin (d + 1) → ℝ) :
    (SmoothPseudoMetric.ofSignature eps heps).chart.gradPair (timeLift σ₀) (timeLift σ₀) x
      = (eps 0)⁻¹ * (deriv σ₀ (x 0) * deriv σ₀ (x 0)) := by
  rw [ofSignature_gradPair, Finset.sum_eq_single (0 : Fin (d + 1))]
  · rw [coordPartial_timeLift_deriv hσ]
    ring
  · intro i _ hi
    rw [coordPartial_timeLift_of_ne σ₀ hi x]
    ring
  · intro h
    exact absurd (Finset.mem_univ (0 : Fin (d + 1))) h

/-! ## The effective potential as a function of conformal time -/

/-- Effective clock potential of a conformal factor of conformal time. -/
noncomputable def conformalTimePotential (invEps a massSq : ℝ) (σ₀ : ℝ → ℝ) : ℝ → ℝ :=
  fun t => massSq * Real.exp (2 * σ₀ t)
    - (a * (invEps * deriv (deriv σ₀) t)
        + a ^ (2 : ℕ) * (invEps * (deriv σ₀ t * deriv σ₀ t)))

theorem conformalPotential_timeLift (eps : Fin (d + 1) → ℝ) (heps : ∀ i, eps i ≠ 0)
    {σ₀ : ℝ → ℝ} (hσ : ContDiff ℝ ∞ σ₀) (a massSq : ℝ) (x : Fin (d + 1) → ℝ) :
    (SmoothPseudoMetric.ofSignature eps heps).chart.conformalPotential a massSq
        (timeLift σ₀) x
      = conformalTimePotential (eps 0)⁻¹ a massSq σ₀ (x 0) := by
  rw [SmoothMetricChart.conformalPotential, SmoothMetricChart.conformalDefect,
    dalembert_timeLift_flat eps heps hσ x, gradPair_timeLift_flat eps heps hσ x,
    conformalTimePotential]
  rfl

theorem contDiff_conformalTimePotential (invEps a massSq : ℝ) {σ₀ : ℝ → ℝ}
    (hσ : ContDiff ℝ ∞ σ₀) :
    ContDiff ℝ 1 (conformalTimePotential invEps a massSq σ₀) := by
  have h1 : ContDiff ℝ ∞ (deriv σ₀) := contDiff_deriv_infty hσ
  have h2 : ContDiff ℝ ∞ (deriv (deriv σ₀)) := contDiff_deriv_infty h1
  have hexp : ContDiff ℝ 1 fun t => massSq * Real.exp (2 * σ₀ t) :=
    contDiff_const.mul
      ((Real.contDiff_exp.comp (contDiff_const.mul hσ)).of_le (by simp))
  have hterm1 : ContDiff ℝ 1 fun t => a * (invEps * deriv (deriv σ₀) t) :=
    contDiff_const.mul (contDiff_const.mul (h2.of_le (by simp)))
  have hterm2 : ContDiff ℝ 1 fun t => a ^ (2 : ℕ) * (invEps * (deriv σ₀ t * deriv σ₀ t)) :=
    contDiff_const.mul
      (contDiff_const.mul ((h1.of_le (by simp)).mul (h1.of_le (by simp))))
  exact hexp.sub (hterm1.add hterm2)

/-! ## Probes and determination on the flat chart -/

theorem flat_inverseMetric_homogeneous (eps : Fin (d + 1) → ℝ) (heps : ∀ i, eps i ≠ 0) :
    ∀ x : Fin (d + 1) → ℝ, (SmoothPseudoMetric.ofSignature eps heps).chart.inverseMetric x
      = (fun _ : ℝ => Matrix.diagonal fun i => (eps i)⁻¹) (x 0) := fun x =>
  SmoothPseudoMetric.ofSignature_inverseMetric eps heps x

theorem flat_density_homogeneous (eps : Fin (d + 1) → ℝ) (heps : ∀ i, eps i ≠ 0) :
    ∀ x : Fin (d + 1) → ℝ, (SmoothPseudoMetric.ofSignature eps heps).chart.density x
      = (fun _ : ℝ => Real.sqrt |∏ k, eps k|) (x 0) := fun x =>
  SmoothPseudoMetric.ofSignature_density eps heps x

theorem flat_leading_contDiff (eps : Fin (d + 1) → ℝ) :
    ContDiff ℝ 1 fun t : ℝ => (fun _ : ℝ => Real.sqrt |∏ k, eps k|) t *
      (fun _ : ℝ => Matrix.diagonal fun i => (eps i)⁻¹) t (0 : Fin (d + 1)) 0 :=
  contDiff_const

theorem flat_leading_ne_zero (eps : Fin (d + 1) → ℝ) (heps : ∀ i, eps i ≠ 0) (t : ℝ) :
    (fun _ : ℝ => Real.sqrt |∏ k, eps k|) t *
      (fun _ : ℝ => Matrix.diagonal fun i => (eps i)⁻¹) t (0 : Fin (d + 1)) 0 ≠ 0 := by
  have hpos : (0 : ℝ) < Real.sqrt |∏ k, eps k| := by
    rw [← SmoothPseudoMetric.ofSignature_density eps heps (0 : Fin (d + 1) → ℝ)]
    exact (SmoothPseudoMetric.ofSignature eps heps).chart.density_pos _
  show Real.sqrt |∏ k, eps k| * (Matrix.diagonal fun i => (eps i)⁻¹) (0 : Fin (d + 1)) 0 ≠ 0
  rw [Matrix.diagonal_apply_eq]
  exact mul_ne_zero (ne_of_gt hpos) (inv_ne_zero (heps 0))

/-- **Clock probes for a conformal-time species.** -/
theorem exists_conformalTime_localProbe (eps : Fin (d + 1) → ℝ) (heps : ∀ i, eps i ≠ 0)
    {σ₀ : ℝ → ℝ} (hσ : ContDiff ℝ ∞ σ₀) (a massSq b : ℝ) :
    ∃ (u : (Fin (d + 1) → ℝ) → ℝ) (ε : ℝ), 0 < ε ∧
      (∀ x : Fin (d + 1) → ℝ, x 0 = b → u x = 1) ∧
      (∀ x : Fin (d + 1) → ℝ, x 0 ∈ Ioo (b - ε) (b + ε) →
        SolvesPotentialWaveAt (SmoothPseudoMetric.ofSignature eps heps).chart.dalembert
          (timeLift (conformalTimePotential (eps 0)⁻¹ a massSq σ₀)) u x) :=
  exists_homogeneous_localProbe (flat_inverseMetric_homogeneous eps heps)
    (flat_density_homogeneous eps heps) (flat_leading_contDiff eps)
    (flat_leading_ne_zero eps heps)
    (contDiff_const.mul (contDiff_conformalTimePotential (eps 0)⁻¹ a massSq hσ)) b

/-- **The effective potential of a conformal-time species is determined by its clock data.** -/
theorem conformalTimePotential_determined (eps : Fin (d + 1) → ℝ) (heps : ∀ i, eps i ≠ 0)
    {σ₀ : ℝ → ℝ} (hσ : ContDiff ℝ ∞ σ₀) (a massSq : ℝ)
    {other : (Fin (d + 1) → ℝ) → ℝ}
    (hother : ∀ (b : ℝ) (u : (Fin (d + 1) → ℝ) → ℝ) (ε : ℝ), 0 < ε →
      (∀ x : Fin (d + 1) → ℝ, x 0 ∈ Ioo (b - ε) (b + ε) →
        SolvesPotentialWaveAt (SmoothPseudoMetric.ofSignature eps heps).chart.dalembert
          (timeLift (conformalTimePotential (eps 0)⁻¹ a massSq σ₀)) u x) →
      (∀ x : Fin (d + 1) → ℝ, x 0 ∈ Ioo (b - ε) (b + ε) →
        SolvesPotentialWaveAt (SmoothPseudoMetric.ofSignature eps heps).chart.dalembert
          other u x)) :
    other = timeLift (conformalTimePotential (eps 0)⁻¹ a massSq σ₀) :=
  chartPotential_eq_of_homogeneous (flat_inverseMetric_homogeneous eps heps)
    (flat_density_homogeneous eps heps) (flat_leading_contDiff eps)
    (flat_leading_ne_zero eps heps)
    (contDiff_const.mul (contDiff_conformalTimePotential (eps 0)⁻¹ a massSq hσ)) hother

/-! ## The two-species reconstruction -/

theorem conformalTimePotential_difference (invEps a massSq₁ massSq₂ : ℝ) (σ₀ : ℝ → ℝ) (t : ℝ) :
    conformalTimePotential invEps a massSq₁ σ₀ t
        - conformalTimePotential invEps a massSq₂ σ₀ t
      = (massSq₁ - massSq₂) * Real.exp (2 * σ₀ t) := by
  simp only [conformalTimePotential]
  ring

/-- **The two-species law, closed end to end in conformal time.** From the clock data of two
species with distinct calibrated masses on a conformally flat cosmological chart, the conformal
scale is recovered pointwise — with no nondegeneracy hypothesis. -/
theorem twoSpecies_conformalTime_reconstruction (eps : Fin (d + 1) → ℝ)
    (heps : ∀ i, eps i ≠ 0) {σ₀ : ℝ → ℝ} (hσ : ContDiff ℝ ∞ σ₀) (a : ℝ)
    {massSq₁ massSq₂ : ℝ} (hmass : massSq₁ ≠ massSq₂)
    {other₁ other₂ : (Fin (d + 1) → ℝ) → ℝ}
    (h₁ : ∀ (b : ℝ) (u : (Fin (d + 1) → ℝ) → ℝ) (ε : ℝ), 0 < ε →
      (∀ x : Fin (d + 1) → ℝ, x 0 ∈ Ioo (b - ε) (b + ε) →
        SolvesPotentialWaveAt (SmoothPseudoMetric.ofSignature eps heps).chart.dalembert
          (timeLift (conformalTimePotential (eps 0)⁻¹ a massSq₁ σ₀)) u x) →
      (∀ x : Fin (d + 1) → ℝ, x 0 ∈ Ioo (b - ε) (b + ε) →
        SolvesPotentialWaveAt (SmoothPseudoMetric.ofSignature eps heps).chart.dalembert
          other₁ u x))
    (h₂ : ∀ (b : ℝ) (u : (Fin (d + 1) → ℝ) → ℝ) (ε : ℝ), 0 < ε →
      (∀ x : Fin (d + 1) → ℝ, x 0 ∈ Ioo (b - ε) (b + ε) →
        SolvesPotentialWaveAt (SmoothPseudoMetric.ofSignature eps heps).chart.dalembert
          (timeLift (conformalTimePotential (eps 0)⁻¹ a massSq₂ σ₀)) u x) →
      (∀ x : Fin (d + 1) → ℝ, x 0 ∈ Ioo (b - ε) (b + ε) →
        SolvesPotentialWaveAt (SmoothPseudoMetric.ofSignature eps heps).chart.dalembert
          other₂ u x))
    (x : Fin (d + 1) → ℝ) :
    reconstructedScale other₁ other₂ massSq₁ massSq₂ x = Real.exp (2 * σ₀ (x 0)) := by
  rw [conformalTimePotential_determined eps heps hσ a massSq₁ h₁,
    conformalTimePotential_determined eps heps hσ a massSq₂ h₂, reconstructedScale]
  show (conformalTimePotential (eps 0)⁻¹ a massSq₁ σ₀ (x 0)
      - conformalTimePotential (eps 0)⁻¹ a massSq₂ σ₀ (x 0)) / (massSq₁ - massSq₂)
    = Real.exp (2 * σ₀ (x 0))
  rw [conformalTimePotential_difference]
  field_simp [sub_ne_zero.mpr hmass]

/-- The same statement against the chart-level effective potential of the card. -/
theorem twoSpecies_conformalTime_potential_agrees (eps : Fin (d + 1) → ℝ)
    (heps : ∀ i, eps i ≠ 0) {σ₀ : ℝ → ℝ} (hσ : ContDiff ℝ ∞ σ₀) (a massSq : ℝ) :
    (SmoothPseudoMetric.ofSignature eps heps).chart.conformalPotential a massSq (timeLift σ₀)
      = timeLift (conformalTimePotential (eps 0)⁻¹ a massSq σ₀) := by
  funext x
  exact conformalPotential_timeLift eps heps hσ a massSq x

end GaloisForLFunctions.HTGeometry
