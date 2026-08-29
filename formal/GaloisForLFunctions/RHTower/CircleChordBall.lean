import GaloisForLFunctions.HTGeometry.CompletedTimeSmallBall
import GaloisForLFunctions.HTGeometry.ProjectiveChoiAdaptiveCubeUnionWindowLaw
import GaloisForLFunctions.RHTower.ProjectiveWeightedTargetVolumeLower

/-!
# Chord balls on the unit additive circle

The set of phases whose chord to the identity is at most `δ` is squeezed between two metric balls
by the two-sided chord estimate `4‖y‖ ≤ ‖e(y) − 1‖ ≤ 2π‖y‖`.  Normalized Haar measure of a metric
ball is twice its radius, so the chord ball has measure between `δ/π` and `δ/2`.

These are the exact one-coordinate constants of the forest-coordinate volume law.
-/

namespace RHTower

open MeasureTheory Metric GaloisForLFunctions.HTGeometry
open scoped ENNReal NNReal

noncomputable section

/-- The set of phases within chord distance `δ` of the identity. -/
def chordBall (δ : ℝ) : Set UnitAddCircle := {y | ‖fourier 1 y - 1‖ ≤ δ}

theorem measurableSet_chordBall (δ : ℝ) : MeasurableSet (chordBall δ) := by
  have hcont : Continuous fun y : UnitAddCircle => ‖fourier 1 y - 1‖ := by fun_prop
  exact hcont.measurable measurableSet_Iic

theorem ball_subset_chordBall {δ : ℝ} :
    ball (0 : UnitAddCircle) (δ / (2 * Real.pi)) ⊆ chordBall δ := by
  intro y hy
  rw [mem_ball, dist_zero_right] at hy
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hmul : ‖y‖ * (2 * Real.pi) < δ := (lt_div_iff₀ hpi).1 hy
  have h := norm_fourier_one_sub_one_le_two_pi_mul_norm y
  show ‖fourier 1 y - 1‖ ≤ δ
  nlinarith [h, hmul]

theorem chordBall_subset_closedBall (δ : ℝ) :
    chordBall δ ⊆ closedBall (0 : UnitAddCircle) (δ / 4) := by
  intro y hy
  rw [mem_closedBall, dist_zero_right]
  have h := four_mul_norm_le_norm_fourier_one_sub_one y
  have hy' : ‖fourier 1 y - 1‖ ≤ δ := hy
  linarith

/-- **Lower measure bound for a chord ball.** -/
theorem ofReal_le_volume_chordBall {δ : ℝ} (hsmall : δ ≤ Real.pi) :
    ENNReal.ofReal (δ / Real.pi) ≤ volume (chordBall δ) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hrad : δ / (2 * Real.pi) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hball : volume (ball (0 : UnitAddCircle) (δ / (2 * Real.pi)))
      = ENNReal.ofReal (2 * (δ / (2 * Real.pi))) := by
    rw [volume_eq_haarAddCircle]
    exact haarAddCircle_ball_zero hrad
  have hmono := measure_mono (μ := (volume : Measure UnitAddCircle))
    (ball_subset_chordBall (δ := δ))
  rw [hball] at hmono
  have hval : 2 * (δ / (2 * Real.pi)) = δ / Real.pi := by
    field_simp
  rwa [hval] at hmono

/-- **Upper measure bound for a chord ball.** -/
theorem volume_chordBall_le {δ : ℝ} (hδ : 0 ≤ δ) :
    volume (chordBall δ) ≤ ENNReal.ofReal (δ / 2) := by
  by_cases hbig : 2 ≤ δ
  · have hone : volume (chordBall δ) ≤ 1 := by
      calc volume (chordBall δ) ≤ volume (Set.univ : Set UnitAddCircle) :=
            measure_mono (Set.subset_univ _)
        _ = 1 := by
            rw [AddCircle.measure_univ]
            simp
    refine hone.trans ?_
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from by simp]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  · push Not at hbig
    refine ENNReal.le_of_forall_pos_le_add ?_
    intro ε hε _
    have hεR : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
    set t : ℝ := min ((ε : ℝ) / 2) ((2 - δ) / 8) with ht
    have htpos : 0 < t := lt_min (by linarith) (by linarith)
    have htε : t ≤ (ε : ℝ) / 2 := min_le_left _ _
    have htδ : t ≤ (2 - δ) / 8 := min_le_right _ _
    have hrhalf : δ / 4 + t ≤ 1 / 2 := by linarith
    have hsub : chordBall δ ⊆ ball (0 : UnitAddCircle) (δ / 4 + t) := by
      intro y hy
      have hclosed := chordBall_subset_closedBall δ hy
      rw [mem_closedBall, dist_zero_right] at hclosed
      rw [mem_ball, dist_zero_right]
      linarith
    have hball : volume (ball (0 : UnitAddCircle) (δ / 4 + t))
        = ENNReal.ofReal (2 * (δ / 4 + t)) := by
      rw [volume_eq_haarAddCircle]
      exact haarAddCircle_ball_zero hrhalf
    calc volume (chordBall δ) ≤ volume (ball (0 : UnitAddCircle) (δ / 4 + t)) :=
          measure_mono hsub
      _ = ENNReal.ofReal (2 * (δ / 4 + t)) := hball
      _ ≤ ENNReal.ofReal (δ / 2 + (ε : ℝ)) := ENNReal.ofReal_le_ofReal (by linarith)
      _ = ENNReal.ofReal (δ / 2) + ENNReal.ofReal ((ε : ℝ)) :=
          ENNReal.ofReal_add (by linarith) (le_of_lt hεR)
      _ = ENNReal.ofReal (δ / 2) + (ε : ℝ≥0∞) := by
          rw [ENNReal.ofReal_coe_nnreal]

end

end RHTower