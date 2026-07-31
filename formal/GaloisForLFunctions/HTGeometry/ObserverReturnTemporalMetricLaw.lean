import GaloisForLFunctions.HTGeometry.AbstractSpectralDefect

/-!
# Observer return temporal metric

An observer sees finitely many integer-coordinate gap actions. Their
positive weights define a quadratic temporal metric. The exact phase-return
defect is universally comparable with this metric whenever every visible
action lies in the principal phase window.

This is the local geometric core of time--return duality: exact relation
rank determines how many temporal coordinates survive, while the quadratic
form determines their return geometry.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Evaluation of one observer-visible gap on temporal coordinates. -/
def observerTemporalCoordinateAction
    {J κ : Type*} [Fintype κ]
    (gap : J → κ → ℝ) (theta : κ → ℝ) (j : J) : ℝ :=
  ∑ k, gap j k * theta k

/-- Observer temporal metric: weighted Gram energy of all visible gap
actions. -/
def observerTemporalMetricEnergy
    {J κ : Type*} [Fintype J] [Fintype κ]
    (weight : J → ℝ) (gap : J → κ → ℝ)
    (theta : κ → ℝ) : ℝ :=
  ∑ j, weight j *
    observerTemporalCoordinateAction gap theta j ^ 2

/-- Exact trigonometric return defect associated with the same gap data. -/
def observerReturnPhaseDefect
    {J κ : Type*} [Fintype J] [Fintype κ]
    (weight : J → ℝ) (gap : J → κ → ℝ)
    (theta : κ → ℝ) : ℝ :=
  ∑ j, weight j *
    (2 * (1 - Real.cos
      (observerTemporalCoordinateAction gap theta j)))

/-- The visible gaps separate every temporal coordinate direction. -/
def ObserverTemporalMetricNondegenerate
    {J κ : Type*} [Fintype κ]
    (gap : J → κ → ℝ) : Prop :=
  ∀ theta : κ → ℝ,
    (∀ j, observerTemporalCoordinateAction gap theta j = 0) →
      theta = 0

theorem observerTemporalMetricEnergy_nonneg
    {J κ : Type*} [Fintype J] [Fintype κ]
    (weight : J → ℝ) (gap : J → κ → ℝ)
    (hweight : ∀ j, 0 ≤ weight j)
    (theta : κ → ℝ) :
    0 ≤ observerTemporalMetricEnergy weight gap theta := by
  exact Finset.sum_nonneg fun j _ =>
    mul_nonneg (hweight j) (sq_nonneg _)

/-- Global upper quadratic control: the exact return defect never exceeds
the temporal metric energy. -/
theorem observerReturnPhaseDefect_le_temporalMetricEnergy
    {J κ : Type*} [Fintype J] [Fintype κ]
    (weight : J → ℝ) (gap : J → κ → ℝ)
    (hweight : ∀ j, 0 ≤ weight j)
    (theta : κ → ℝ) :
    observerReturnPhaseDefect weight gap theta ≤
      observerTemporalMetricEnergy weight gap theta := by
  apply Finset.sum_le_sum
  intro j _hj
  apply mul_le_mul_of_nonneg_left _ (hweight j)
  have hcos :
      1 - observerTemporalCoordinateAction gap theta j ^ 2 / 2 ≤
        Real.cos (observerTemporalCoordinateAction gap theta j) :=
    Real.one_sub_sq_div_two_le_cos
  linarith

/-- Principal-window lower quadratic control. The temporal metric energy is
at most `π²/4` times the exact phase-return defect. -/
theorem temporalMetricEnergy_le_pi_sq_div_four_mul_returnDefect
    {J κ : Type*} [Fintype J] [Fintype κ]
    (weight : J → ℝ) (gap : J → κ → ℝ)
    (hweight : ∀ j, 0 ≤ weight j)
    (theta : κ → ℝ)
    (hphase : ∀ j,
      |observerTemporalCoordinateAction gap theta j| ≤ Real.pi) :
    observerTemporalMetricEnergy weight gap theta ≤
      Real.pi ^ 2 / 4 *
        observerReturnPhaseDefect weight gap theta := by
  have hpi : 0 < Real.pi := Real.pi_pos
  rw [observerTemporalMetricEnergy, observerReturnPhaseDefect,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _hj
  have hcos :=
    HTGeometry.AbstractSpectralFamily.two_div_pi_sq_mul_sq_le_one_sub_cos
      (hphase j)
  have hscalar :
      observerTemporalCoordinateAction gap theta j ^ 2 ≤
        Real.pi ^ 2 / 4 *
          (2 * (1 - Real.cos
            (observerTemporalCoordinateAction gap theta j))) := by
    calc
      observerTemporalCoordinateAction gap theta j ^ 2 =
          (Real.pi ^ 2 / 2) *
            (2 / Real.pi ^ 2 *
              observerTemporalCoordinateAction gap theta j ^ 2) := by
        field_simp
      _ ≤ (Real.pi ^ 2 / 2) *
          (1 - Real.cos
            (observerTemporalCoordinateAction gap theta j)) :=
        mul_le_mul_of_nonneg_left hcos (by positivity)
      _ = Real.pi ^ 2 / 4 *
          (2 * (1 - Real.cos
            (observerTemporalCoordinateAction gap theta j))) := by ring
  calc
    weight j * observerTemporalCoordinateAction gap theta j ^ 2 ≤
        weight j * (Real.pi ^ 2 / 4 *
          (2 * (1 - Real.cos
            (observerTemporalCoordinateAction gap theta j)))) :=
      mul_le_mul_of_nonneg_left hscalar (hweight j)
    _ = Real.pi ^ 2 / 4 *
        (weight j * (2 * (1 - Real.cos
          (observerTemporalCoordinateAction gap theta j)))) := by ring

/-- Positive visible weights and gap nondegeneracy make the temporal metric
positive definite. -/
theorem observerTemporalMetricEnergy_eq_zero_iff
    {J κ : Type*} [Fintype J] [Fintype κ]
    (weight : J → ℝ) (gap : J → κ → ℝ)
    (hweight : ∀ j, 0 < weight j)
    (hnondegenerate : ObserverTemporalMetricNondegenerate gap)
    (theta : κ → ℝ) :
    observerTemporalMetricEnergy weight gap theta = 0 ↔
      theta = 0 := by
  constructor
  · intro hzero
    apply hnondegenerate theta
    intro j
    have hterm :
        weight j * observerTemporalCoordinateAction gap theta j ^ 2 ≤
          observerTemporalMetricEnergy weight gap theta := by
      rw [observerTemporalMetricEnergy]
      exact Finset.single_le_sum
        (fun i _hi => mul_nonneg (hweight i).le (sq_nonneg _))
        (Finset.mem_univ j)
    rw [hzero] at hterm
    have htermZero :
        weight j * observerTemporalCoordinateAction gap theta j ^ 2 = 0 :=
      le_antisymm hterm
        (mul_nonneg (hweight j).le (sq_nonneg _))
    rcases mul_eq_zero.mp htermZero with hw | hs
    · exact absurd hw (hweight j).ne'
    · exact sq_eq_zero_iff.mp hs
  · rintro rfl
    simp [observerTemporalMetricEnergy,
      observerTemporalCoordinateAction]

/-- In the principal phase chart the exact return defect vanishes only at
the origin of observer-visible time. -/
theorem observerReturnPhaseDefect_eq_zero_iff_of_phaseBound
    {J κ : Type*} [Fintype J] [Fintype κ]
    (weight : J → ℝ) (gap : J → κ → ℝ)
    (hweight : ∀ j, 0 < weight j)
    (hnondegenerate : ObserverTemporalMetricNondegenerate gap)
    (theta : κ → ℝ)
    (hphase : ∀ j,
      |observerTemporalCoordinateAction gap theta j| ≤ Real.pi) :
    observerReturnPhaseDefect weight gap theta = 0 ↔
      theta = 0 := by
  constructor
  · intro hzero
    apply (observerTemporalMetricEnergy_eq_zero_iff
      weight gap hweight hnondegenerate theta).mp
    have hnonneg :=
      observerTemporalMetricEnergy_nonneg
        weight gap (fun j => (hweight j).le) theta
    have hupper :=
      temporalMetricEnergy_le_pi_sq_div_four_mul_returnDefect
        weight gap (fun j => (hweight j).le) theta hphase
    rw [hzero, mul_zero] at hupper
    exact le_antisymm hupper hnonneg
  · rintro rfl
    simp [observerReturnPhaseDefect,
      observerTemporalCoordinateAction]

end

end GaloisForLFunctions.HTGeometry
