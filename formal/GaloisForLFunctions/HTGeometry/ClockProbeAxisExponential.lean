import GaloisForLFunctions.HTGeometry.ClockProbeTranslationFamily
import GaloisForLFunctions.HTGeometry.ConformalMetricDalembertian

/-!
# An explicit nonvanishing probe family for a diagonal clock geometry

The determination half of the potential-recovery problem reduces everything to one demand: an
action-closed probe family with a nonvanishing observation. This file supplies such a family for a
constant diagonal metric chart, so the whole chain is inhabited rather than conditional.

The probes are axis exponentials `x ↦ c e^{s x_{i₀}}`. They are everywhere nonvanishing, they solve
the potential-dressed wave equation of the chart for the constant potential `-ε_{i₀}⁻¹ s²`, and the
family of all their nonzero multiples is closed under translation of events. Translations act
transitively, so a single observation determines the potential at every event.

Both signs of constant potential are reachable in a Lorentzian signature: a timelike axis gives one
sign and a spacelike axis the other.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped BigOperators ContDiff

variable {d : ℕ}

/-- Coordinate projections have the expected partial derivatives. -/
theorem coordPartial_proj (i i₀ : Fin d) (x : Fin d → ℝ) :
    coordPartial i (fun y : Fin d → ℝ => y i₀) x = if i₀ = i then 1 else 0 := by
  have h : HasFDerivAt (fun y : Fin d → ℝ => y i₀)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i₀) x :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i₀).hasFDerivAt
  rw [coordPartial, h.fderiv]
  simp [Pi.single_apply]

/-- An axis exponential probe. -/
noncomputable def axisExponential (i₀ : Fin d) (s c : ℝ) : (Fin d → ℝ) → ℝ :=
  fun x => c * Real.exp (s * x i₀)

theorem axisExponential_ne_zero {i₀ : Fin d} {s c : ℝ} (hc : c ≠ 0) (x : Fin d → ℝ) :
    axisExponential i₀ s c x ≠ 0 :=
  mul_ne_zero hc (Real.exp_ne_zero _)

theorem contDiff_axisLinear (i₀ : Fin d) (s : ℝ) :
    ContDiff ℝ ∞ fun x : Fin d → ℝ => s * x i₀ :=
  contDiff_const.mul (contDiff_apply ℝ ℝ i₀)

theorem contDiff_axisExponential (i₀ : Fin d) (s c : ℝ) :
    ContDiff ℝ ∞ (axisExponential i₀ s c) :=
  contDiff_const.mul ((contDiff_axisLinear i₀ s).exp)

theorem coordPartial_axisLinear (i i₀ : Fin d) (s : ℝ) (x : Fin d → ℝ) :
    coordPartial i (fun y : Fin d → ℝ => s * y i₀) x = s * (if i₀ = i then 1 else 0) := by
  rw [coordPartial_const_mul
    (differentiableAt_of_contDiff_infty (contDiff_apply ℝ ℝ i₀) x) s i, coordPartial_proj]

theorem coordPartial_axisExponential (i i₀ : Fin d) (s c : ℝ) (x : Fin d → ℝ) :
    coordPartial i (axisExponential i₀ s c) x =
      (if i₀ = i then s else 0) * axisExponential i₀ s c x := by
  have hlin := differentiableAt_of_contDiff_infty (contDiff_axisLinear i₀ s) x
  show coordPartial i (fun y : Fin d → ℝ => c * Real.exp (s * y i₀)) x =
    (if i₀ = i then s else 0) * (c * Real.exp (s * x i₀))
  rw [coordPartial_const_mul (differentiableAt_of_contDiff_infty
    ((contDiff_axisLinear i₀ s).exp) x) c i, coordPartial_exp hlin i,
    coordPartial_axisLinear]
  by_cases h : i₀ = i
  · rw [if_pos h, if_pos h]
    ring
  · rw [if_neg h, if_neg h]
    ring

/-- The axis exponential is an eigenfunction of the second partial derivative. -/
theorem coordPartial_coordPartial_axisExponential (i i₀ : Fin d) (s c : ℝ) (x : Fin d → ℝ) :
    coordPartial i (coordPartial i (axisExponential i₀ s c)) x =
      (if i₀ = i then s ^ 2 else 0) * axisExponential i₀ s c x := by
  have hrw : coordPartial i (axisExponential i₀ s c) =
      axisExponential i₀ s ((if i₀ = i then s else 0) * c) := by
    funext y
    rw [coordPartial_axisExponential]
    simp only [axisExponential]
    ring
  rw [hrw, coordPartial_axisExponential]
  by_cases h : i₀ = i <;> simp only [h, if_true, if_false, axisExponential] <;> ring

/-- **The axis exponential solves the chart wave equation with a constant potential.** -/
theorem dalembert_axisExponential (eps : Fin d → ℝ) (heps : ∀ i, eps i ≠ 0)
    (i₀ : Fin d) (s c : ℝ) (x : Fin d → ℝ) :
    (SmoothPseudoMetric.ofSignature eps heps).chart.dalembert (axisExponential i₀ s c) x =
      (eps i₀)⁻¹ * s ^ 2 * axisExponential i₀ s c x := by
  rw [SmoothPseudoMetric.ofSignature_dalembert eps heps (contDiff_axisExponential i₀ s c) x]
  rw [Finset.sum_eq_single i₀]
  · have hif : (if i₀ = i₀ then s ^ 2 else 0) = s ^ 2 := if_pos rfl
    rw [coordPartial_coordPartial_axisExponential, hif]
    ring
  · intro j _ hj
    rw [coordPartial_coordPartial_axisExponential]
    have : i₀ ≠ j := fun h => hj h.symm
    simp [this]
  · intro h
    exact absurd (Finset.mem_univ i₀) h

/-- The constant potential solved by an axis exponential. -/
noncomputable def axisPotential (eps : Fin d → ℝ) (i₀ : Fin d) (s : ℝ) : (Fin d → ℝ) → ℝ :=
  fun _ => -((eps i₀)⁻¹ * s ^ 2)

theorem solvesPotentialWave_axisExponential (eps : Fin d → ℝ) (heps : ∀ i, eps i ≠ 0)
    (i₀ : Fin d) (s c : ℝ) :
    SolvesPotentialWave (SmoothPseudoMetric.ofSignature eps heps).chart.dalembert
      (axisPotential eps i₀ s) (axisExponential i₀ s c) := by
  intro x
  rw [dalembert_axisExponential eps heps i₀ s c x, axisPotential]
  ring

/-! ### The translation-closed family -/

/-- All nonzero multiples of one axis exponential. -/
def axisExponentialFamily (i₀ : Fin d) (s : ℝ) : Set ((Fin d → ℝ) → ℝ) :=
  {u | ∃ c : ℝ, c ≠ 0 ∧ u = axisExponential i₀ s c}

/-- Translation of events. -/
def eventTranslation (a x : Fin d → ℝ) : Fin d → ℝ := x + a

theorem eventTranslation_transitive (x y : Fin d → ℝ) :
    ∃ a : Fin d → ℝ, eventTranslation a y = x :=
  ⟨x - y, by simp [eventTranslation]⟩

/-- **The axis exponential family is translation closed.** -/
theorem probeActionClosed_axisExponentialFamily (i₀ : Fin d) (s : ℝ) :
    ProbeActionClosed (eventTranslation (d := d)) (axisExponentialFamily i₀ s) := by
  rintro a u ⟨c, hc, rfl⟩
  refine ⟨c * Real.exp (s * a i₀), mul_ne_zero hc (Real.exp_ne_zero _), ?_⟩
  funext x
  simp only [axisExponential, eventTranslation, Pi.add_apply]
  rw [mul_add, Real.exp_add]
  ring

theorem solvesPotentialWave_axisExponentialFamily (eps : Fin d → ℝ) (heps : ∀ i, eps i ≠ 0)
    (i₀ : Fin d) (s : ℝ) :
    ∀ u ∈ axisExponentialFamily i₀ s,
      SolvesPotentialWave (SmoothPseudoMetric.ofSignature eps heps).chart.dalembert
        (axisPotential eps i₀ s) u := by
  rintro u ⟨c, hc, rfl⟩
  exact solvesPotentialWave_axisExponential eps heps i₀ s c

/-- **The probe family determines its potential at every event.** -/
theorem potentialDeterminationSet_axisExponentialFamily (i₀ : Fin d) (s : ℝ) :
    potentialDeterminationSet (axisExponentialFamily i₀ s) = Set.univ := by
  refine potentialDeterminationSet_eq_univ_of_exists_ne_zero
    (probeActionClosed_axisExponentialFamily i₀ s) eventTranslation_transitive
    (u := axisExponential i₀ s 1) ⟨1, one_ne_zero, rfl⟩ (x₀ := 0) ?_
  exact axisExponential_ne_zero one_ne_zero 0

/-- **The construction closes the determination problem for a diagonal chart.** Any potential
explaining the axis exponential family is the axis potential, everywhere. -/
theorem potential_eq_axisPotential (eps : Fin d → ℝ) (heps : ∀ i, eps i ≠ 0)
    (i₀ : Fin d) (s : ℝ) {other : (Fin d → ℝ) → ℝ}
    (hother : ∀ u ∈ axisExponentialFamily i₀ s,
      SolvesPotentialWave (SmoothPseudoMetric.ofSignature eps heps).chart.dalembert other u) :
    other = axisPotential eps i₀ s :=
  potential_eq_of_repeatable (probeActionClosed_axisExponentialFamily i₀ s)
    eventTranslation_transitive (u := axisExponential i₀ s 1) ⟨1, one_ne_zero, rfl⟩
    (axisExponential_ne_zero one_ne_zero 0) hother
    (solvesPotentialWave_axisExponentialFamily eps heps i₀ s)

end GaloisForLFunctions.HTGeometry
