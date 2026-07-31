import GaloisForLFunctions.HTGeometry.ObserverReturnTemporalCoercivityLaw
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Local volume law for observer return

The temporal metric controls the complete local high-fidelity target between
two Euclidean balls. The inner radius is proportional to the square root of
the allowed return defect, and so is the outer radius. This is the
finite-dimensional volume brick behind the recurrence Weyl exponent.
-/

open scoped BigOperators
open Set
open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Local observer-return target inside one Euclidean phase chart. -/
def observerReturnLocalTarget
    {J : Type*} [Fintype J] {τ : ℕ}
    (weight : J → ℝ) (gap : J → Fin τ → ℝ)
    (r ε : ℝ) : Set (EuclideanSpace ℝ (Fin τ)) :=
  {theta |
    ‖theta‖ < r ∧
      observerReturnPhaseDefect weight gap
        (fun k => theta k) < ε}

/-- An explicit inner ball lies inside the local observer-return target. -/
theorem ball_subset_observerReturnLocalTarget
    {J : Type*} [Fintype J] {τ : ℕ}
    (weight : J → ℝ) (gap : J → Fin τ → ℝ)
    (hweight : ∀ j, 0 ≤ weight j)
    {r ε M : ℝ} (hε : 0 < ε) (hM : 0 < M)
    (hmetricUpper : ∀ theta : EuclideanSpace ℝ (Fin τ),
      observerTemporalMetricEnergy weight gap (fun k => theta k) ≤
        M * ‖theta‖ ^ 2)
    (hradius : Real.sqrt (ε / M) ≤ r) :
    Metric.ball (0 : EuclideanSpace ℝ (Fin τ))
        (Real.sqrt (ε / M)) ⊆
      observerReturnLocalTarget weight gap r ε := by
  intro theta htheta
  rw [Metric.mem_ball, dist_zero_right] at htheta
  rw [observerReturnLocalTarget, Set.mem_setOf_eq]
  have hradpos : 0 < Real.sqrt (ε / M) :=
    Real.sqrt_pos.2 (div_pos hε hM)
  have hnorm : ‖theta‖ < r := htheta.trans_le hradius
  refine ⟨hnorm, ?_⟩
  have hdefect :=
    observerReturnPhaseDefect_le_temporalMetricEnergy
      weight gap hweight (fun k => theta k)
  have hmetric := hmetricUpper theta
  have hsq :
      ‖theta‖ ^ 2 < (Real.sqrt (ε / M)) ^ 2 :=
    (sq_lt_sq₀ (norm_nonneg theta) hradpos.le).2 htheta
  rw [Real.sq_sqrt (div_nonneg hε.le hM.le)] at hsq
  calc
    observerReturnPhaseDefect weight gap (fun k => theta k) ≤
        observerTemporalMetricEnergy weight gap
          (fun k => theta k) := hdefect
    _ ≤ M * ‖theta‖ ^ 2 := hmetric
    _ < M * (ε / M) := mul_lt_mul_of_pos_left hsq hM
    _ = ε := by field_simp

/-- Every point in the local observer-return target lies in an explicit
outer ball. -/
theorem observerReturnLocalTarget_subset_closedBall
    {J : Type*} [Fintype J] {τ : ℕ}
    (weight : J → ℝ) (gap : J → Fin τ → ℝ)
    (hweight : ∀ j, 0 ≤ weight j)
    {r ε m : ℝ} (hε : 0 < ε) (hm : 0 < m)
    (hmetricLower : ∀ theta : EuclideanSpace ℝ (Fin τ),
      m * ‖theta‖ ^ 2 ≤
        observerTemporalMetricEnergy weight gap (fun k => theta k))
    (hphase : ∀ theta : EuclideanSpace ℝ (Fin τ),
      ‖theta‖ < r →
      ∀ j, |observerTemporalCoordinateAction gap
        (fun k => theta k) j| ≤ Real.pi) :
    observerReturnLocalTarget weight gap r ε ⊆
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin τ))
        (Real.sqrt ((Real.pi ^ 2 / 4) * ε / m)) := by
  intro theta htheta
  rw [observerReturnLocalTarget, Set.mem_setOf_eq] at htheta
  rw [Metric.mem_closedBall, dist_zero_right]
  have hmetric := hmetricLower theta
  have hdefect :=
    temporalMetricEnergy_le_pi_sq_div_four_mul_returnDefect
      weight gap hweight (fun k => theta k) (hphase theta htheta.1)
  have hsq :
      ‖theta‖ ^ 2 <
        (Real.pi ^ 2 / 4) * ε / m := by
    apply (lt_div_iff₀ hm).2
    calc
      ‖theta‖ ^ 2 * m = m * ‖theta‖ ^ 2 := by ring
      _ ≤ observerTemporalMetricEnergy weight gap
            (fun k => theta k) := hmetric
      _ ≤ Real.pi ^ 2 / 4 *
          observerReturnPhaseDefect weight gap
            (fun k => theta k) := hdefect
      _ < Real.pi ^ 2 / 4 * ε := by
        exact mul_lt_mul_of_pos_left htheta.2 (by positivity)
  have hinside :
      0 ≤ (Real.pi ^ 2 / 4) * ε / m := by positivity
  have hsqrt :
      (Real.sqrt ((Real.pi ^ 2 / 4) * ε / m)) ^ 2 =
        (Real.pi ^ 2 / 4) * ε / m :=
    Real.sq_sqrt hinside
  have hsqrtNonneg :
      0 ≤ Real.sqrt ((Real.pi ^ 2 / 4) * ε / m) :=
    Real.sqrt_nonneg _
  nlinarith [norm_nonneg theta]

/-- **Local recurrence-volume law.** The complete local return target is
trapped between Euclidean balls whose radii are constant multiples of
`√ε`. Hence its volume has the universal `ε^(τ/2)` dimensional scale. -/
theorem observerReturnLocalTarget_volume_ball_sandwich
    {J : Type*} [Fintype J] {τ : ℕ}
    (weight : J → ℝ) (gap : J → Fin τ → ℝ)
    (hweight : ∀ j, 0 ≤ weight j)
    {r ε m M : ℝ} (hε : 0 < ε) (hm : 0 < m) (hM : 0 < M)
    (hmetricLower : ∀ theta : EuclideanSpace ℝ (Fin τ),
      m * ‖theta‖ ^ 2 ≤
        observerTemporalMetricEnergy weight gap (fun k => theta k))
    (hmetricUpper : ∀ theta : EuclideanSpace ℝ (Fin τ),
      observerTemporalMetricEnergy weight gap (fun k => theta k) ≤
        M * ‖theta‖ ^ 2)
    (hphase : ∀ theta : EuclideanSpace ℝ (Fin τ),
      ‖theta‖ < r →
      ∀ j, |observerTemporalCoordinateAction gap
        (fun k => theta k) j| ≤ Real.pi)
    (hradius : Real.sqrt (ε / M) ≤ r) :
    volume (Metric.ball (0 : EuclideanSpace ℝ (Fin τ))
        (Real.sqrt (ε / M))) ≤
      volume (observerReturnLocalTarget weight gap r ε) ∧
    volume (observerReturnLocalTarget weight gap r ε) ≤
      volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin τ))
        (Real.sqrt ((Real.pi ^ 2 / 4) * ε / m))) := by
  exact ⟨measure_mono
      (ball_subset_observerReturnLocalTarget
        weight gap hweight hε hM hmetricUpper hradius),
    measure_mono
      (observerReturnLocalTarget_subset_closedBall
        weight gap hweight hε hm hmetricLower hphase)⟩

end

end GaloisForLFunctions.HTGeometry
