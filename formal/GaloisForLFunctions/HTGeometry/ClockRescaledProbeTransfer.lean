import GaloisForLFunctions.HTGeometry.ClockMasslessReference

/-!
# The remaining input, transported to the physical Klein–Gordon equation

The conformal conjugation of the card is an identity between two operators. Read as a statement
about *solutions* it becomes a bijection: `u ↦ e^{-aσ} u` carries solutions of `□_g u + V_μ^σ u = 0`
to solutions of the physical massive equation `□_{g̃} f + μ f = 0` on the rescaled chart, and back
by `f ↦ e^{aσ} f`. The map is smoothness-preserving and zero-preserving, because `e^{aσ}` is smooth
and nowhere zero.

So the last open input of the inverse step is exactly the physical statement that the massive
Klein–Gordon field on the rescaled spacetime admits, at every event, a smooth solution nonvanishing
there. Together with the massless reference — which costs nothing — that single statement yields the
conformal scale.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped ContDiff

open ExponentialSecondOrderClockCalculus

variable {d : ℕ}

theorem exp_neg_mul_exp_mul (c : ℝ) (σ f : (Fin d → ℝ) → ℝ) :
    (fun y => Real.exp (-c * σ y) * (Real.exp (c * σ y) * f y)) = f := by
  funext y
  rw [← mul_assoc, ← Real.exp_add]
  have hz : -c * σ y + c * σ y = 0 := by ring
  rw [hz, Real.exp_zero, one_mul]

/-- Solutions of the physical massive Klein–Gordon equation on the rescaled chart. -/
def SolvesRescaledKleinGordon (M : SmoothMetricChart d) (σ : (Fin d → ℝ) → ℝ)
    (hσ : ContDiff ℝ ∞ σ) (massSq : ℝ) (f : (Fin d → ℝ) → ℝ) : Prop :=
  ∀ x, (M.conformalRescale σ hσ).dalembert f x + massSq * f x = 0

/-- **A physical solution conjugates to a probe of the effective potential.** -/
theorem solvesPotentialWave_of_rescaled (M : SmoothMetricChart d) {σ : (Fin d → ℝ) → ℝ}
    (hσ : ContDiff ℝ ∞ σ) {u : (Fin d → ℝ) → ℝ} (hu : ContDiff ℝ ∞ u) (massSq : ℝ)
    (h : ∀ x, (M.conformalRescale σ hσ).dalembert
        (fun y => Real.exp (-conformalDimensionWeight d * σ y) * u y) x
        + massSq * (Real.exp (-conformalDimensionWeight d * σ x) * u x) = 0) :
    SolvesPotentialWave M.dalembert
      (M.conformalPotential (conformalDimensionWeight d) massSq σ) u := by
  intro x
  have hc := M.conformalKleinGordon_conjugation hσ hu massSq x
  rw [h x, mul_zero] at hc
  linarith [hc]

/-- **A probe of the effective potential conjugates to a physical solution.** -/
theorem rescaled_of_solvesPotentialWave (M : SmoothMetricChart d) {σ : (Fin d → ℝ) → ℝ}
    (hσ : ContDiff ℝ ∞ σ) {u : (Fin d → ℝ) → ℝ} (hu : ContDiff ℝ ∞ u) (massSq : ℝ)
    (h : SolvesPotentialWave M.dalembert
      (M.conformalPotential (conformalDimensionWeight d) massSq σ) u) :
    SolvesRescaledKleinGordon M σ hσ massSq
      (fun y => Real.exp (-conformalDimensionWeight d * σ y) * u y) := by
  intro x
  have hc := M.conformalKleinGordon_conjugation hσ hu massSq x
  rw [h x] at hc
  have hne : Real.exp ((conformalDimensionWeight d + 2) * σ x) ≠ 0 := Real.exp_ne_zero _
  exact (mul_eq_zero.mp hc).resolve_left hne

/-- **The remaining input, in physical form.** If the massive Klein–Gordon field on the rescaled
chart has at every event a smooth solution nonvanishing there, the effective potential of that
species is determined. -/
theorem noCommonZero_of_rescaled_probeFamily (M : SmoothMetricChart d)
    {σ : (Fin d → ℝ) → ℝ} (hσ : ContDiff ℝ ∞ σ) (massSq : ℝ)
    (hprobe : ∀ x : Fin d → ℝ, ∃ f : (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ f ∧
      SolvesRescaledKleinGordon M σ hσ massSq f ∧ f x ≠ 0) :
    NoCommonZero M.dalembert
      (M.conformalPotential (conformalDimensionWeight d) massSq σ) := by
  intro x
  obtain ⟨f, hf, hsolve, hfx⟩ := hprobe x
  have hexp : ContDiff ℝ ∞ fun y => Real.exp (conformalDimensionWeight d * σ y) :=
    Real.contDiff_exp.comp (contDiff_const.mul hσ)
  have hfun := exp_neg_mul_exp_mul (conformalDimensionWeight d) σ f
  have hpt := congrFun hfun
  refine ⟨fun y => Real.exp (conformalDimensionWeight d * σ y) * f y, ?_, ?_⟩
  · rw [mem_solutionSet_iff]
    refine solvesPotentialWave_of_rescaled M hσ (hexp.mul hf) massSq ?_
    intro y
    rw [hfun, hpt y]
    exact hsolve y
  · exact mul_ne_zero (Real.exp_ne_zero _) hfx

/-- **The converse.** A probe family for the effective potential is a physical probe family. -/
theorem exists_rescaled_probe_of_noCommonZero (M : SmoothMetricChart d)
    {σ : (Fin d → ℝ) → ℝ} (hσ : ContDiff ℝ ∞ σ) (massSq : ℝ) {u : (Fin d → ℝ) → ℝ}
    (hu : ContDiff ℝ ∞ u) (x : Fin d → ℝ) (hux : u x ≠ 0)
    (h : SolvesPotentialWave M.dalembert
      (M.conformalPotential (conformalDimensionWeight d) massSq σ) u) :
    ∃ f : (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ f ∧
      SolvesRescaledKleinGordon M σ hσ massSq f ∧ f x ≠ 0 := by
  refine ⟨fun y => Real.exp (-conformalDimensionWeight d * σ y) * u y, ?_,
    rescaled_of_solvesPotentialWave M hσ hu massSq h, ?_⟩
  · exact (Real.contDiff_exp.comp (contDiff_const.mul hσ)).mul hu
  · exact mul_ne_zero (Real.exp_ne_zero _) hux

/-! ## The scale from one physical probe family -/

/-- **The whole inverse step from one physical hypothesis.** Given, for one massive species, a
smooth solution of the physical Klein–Gordon equation nonvanishing at each event, the conformal
scale is recovered pointwise — the massless reference costs nothing. -/
theorem scale_reconstruction_of_rescaled_probeFamily (M : SmoothMetricChart d)
    {σ : (Fin d → ℝ) → ℝ} (hσ : ContDiff ℝ ∞ σ) {massSq : ℝ} (hmass : massSq ≠ 0)
    (hprobe : ∀ x : Fin d → ℝ, ∃ f : (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ f ∧
      SolvesRescaledKleinGordon M σ hσ massSq f ∧ f x ≠ 0)
    {other₁ other₂ : (Fin d → ℝ) → ℝ}
    (h₁ : ∀ u ∈ solutionSet M.dalembert
        (M.conformalPotential (conformalDimensionWeight d) massSq σ),
      SolvesPotentialWave M.dalembert other₁ u)
    (h₂ : ∀ u ∈ solutionSet M.dalembert
        (M.conformalPotential (conformalDimensionWeight d) 0 σ),
      SolvesPotentialWave M.dalembert other₂ u)
    (x : Fin d → ℝ) :
    reconstructedScale other₁ other₂ massSq 0 x = Real.exp (2 * σ x) :=
  twoSpecies_reconstruction_massless_reference M (conformalDimensionWeight d) hσ hmass
    (noCommonZero_of_rescaled_probeFamily M hσ massSq hprobe) h₁ h₂ x

end GaloisForLFunctions.HTGeometry
