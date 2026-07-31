import GaloisForLFunctions.HTGeometry.ObserverReturnTemporalCoercivityLaw
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Local volume law for observer return

The temporal metric controls the complete local high-fidelity target between
two Euclidean balls. The inner radius is proportional to the square root of
the allowed return defect, and so is the outer radius. This is the
finite-dimensional volume brick behind the recurrence Weyl exponent.
-/

open scoped BigOperators ENNReal
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

/-- **Automatic local recurrence Weyl law.** For every finite separating
positively weighted gap family there are positive chart and metric constants
for which every sufficiently small return target is trapped between balls
of radii proportional to `√ε`. No coercivity or chart hypothesis remains:
both follow from observer separation and finiteness. -/
theorem exists_observerReturnLocalTarget_volume_ball_sandwich
    {J : Type*} [Fintype J] {τ : ℕ}
    (weight : J → ℝ) (gap : J → Fin τ → ℝ)
    (hweight : ∀ j, 0 < weight j)
    (hnondegenerate : ObserverTemporalMetricNondegenerate gap) :
    ∃ r m M : ℝ, 0 < r ∧ 0 < m ∧ 0 < M ∧
      ∀ ε : ℝ, 0 < ε → Real.sqrt (ε / M) ≤ r →
        volume (Metric.ball (0 : EuclideanSpace ℝ (Fin τ))
            (Real.sqrt (ε / M))) ≤
          volume (observerReturnLocalTarget weight gap r ε) ∧
        volume (observerReturnLocalTarget weight gap r ε) ≤
          volume (Metric.closedBall
            (0 : EuclideanSpace ℝ (Fin τ))
            (Real.sqrt ((Real.pi ^ 2 / 4) * ε / m))) := by
  obtain ⟨m, M, hm, hM, hbounds⟩ :=
    observerTemporalMetricEnergy_two_sided_bounds
      weight gap hweight hnondegenerate
  obtain ⟨r, hr, hphase⟩ :=
    exists_observerTemporalPrincipalPhaseRadius gap
  refine ⟨r, m, M, hr, hm, hM, fun ε hε hradius => ?_⟩
  exact observerReturnLocalTarget_volume_ball_sandwich
    weight gap (fun j => (hweight j).le) hε hm hM
    (fun theta => (hbounds theta).1)
    (fun theta => (hbounds theta).2)
    hphase hradius

/-- Euclidean unit-ball volume in observer temporal dimension `τ`. -/
def observerTemporalUnitBallVolume (τ : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal
    (Real.sqrt Real.pi ^ τ /
      Real.Gamma ((τ : ℝ) / 2 + 1))

/-- **Explicit local recurrence Weyl bounds.** In every positive temporal
dimension, the complete local target is bounded by exact multiples of the
`τ`-th power of `√ε`. Thus the high-fidelity return exponent is `τ / 2`,
with no dimension-linear error term in the exponent. -/
theorem exists_observerReturnLocalTarget_weyl_bounds
    {J : Type*} [Fintype J] {τ : ℕ} (hτ : 0 < τ)
    (weight : J → ℝ) (gap : J → Fin τ → ℝ)
    (hweight : ∀ j, 0 < weight j)
    (hnondegenerate : ObserverTemporalMetricNondegenerate gap) :
    ∃ r m M : ℝ, 0 < r ∧ 0 < m ∧ 0 < M ∧
      ∀ ε : ℝ, 0 < ε → Real.sqrt (ε / M) ≤ r →
        ENNReal.ofReal (Real.sqrt (ε / M)) ^ τ *
              observerTemporalUnitBallVolume τ ≤
          volume (observerReturnLocalTarget weight gap r ε) ∧
        volume (observerReturnLocalTarget weight gap r ε) ≤
          ENNReal.ofReal
              (Real.sqrt ((Real.pi ^ 2 / 4) * ε / m)) ^ τ *
            observerTemporalUnitBallVolume τ := by
  letI : Nonempty (Fin τ) := Fin.pos_iff_nonempty.mp hτ
  obtain ⟨r, m, M, hr, hm, hM, hbounds⟩ :=
    exists_observerReturnLocalTarget_volume_ball_sandwich
      weight gap hweight hnondegenerate
  refine ⟨r, m, M, hr, hm, hM, fun ε hε hradius => ?_⟩
  have h := hbounds ε hε hradius
  simpa [EuclideanSpace.volume_ball,
    EuclideanSpace.volume_closedBall,
    observerTemporalUnitBallVolume] using h

end

end GaloisForLFunctions.HTGeometry
