import GaloisForLFunctions.HTGeometry.RelativeGapCurvature
import GaloisForLFunctions.HTGeometry.PositiveExpSumLogConvex
import GaloisForLFunctions.HTGeometry.CommonRealPartTuranDeterminant
import GaloisForLFunctions.HTGeometry.ConstitutiveStaticHeterogeneityObserver

/-!
# Relative-gap signals of positive exponential packets

Discrete relative acceleration of a positive exponential mixture is nonnegative
at every sampling scale. Its exact determinant is a pairwise dispersion of the
sampled mode multipliers. This applies equally to static-heterogeneity partitions.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open scoped BigOperators

/-- Positive exponential coefficients supply a packet without sign premises. -/
def positiveExpPacket {m : ℕ} (w a : Fin (m + 1) → ℝ) (t : ℝ) : ℝ :=
  expSum (fun i => Real.exp (w i)) a t

theorem positiveExpPacket_pos {m : ℕ} (w a : Fin (m + 1) → ℝ) (t : ℝ) :
    0 < positiveExpPacket w a t :=
  expSum_pos _ _ (Nat.succ_pos m) (fun i => Real.exp_pos (w i)) t

/-- Evenly sampled logarithmic curvature is nonnegative in either time direction. -/
theorem positiveExpPacket_log_curvature_nonneg {m : ℕ}
    (w a : Fin (m + 1) → ℝ) (t h : ℝ) :
    0 ≤ logStepCurvature (Real.log (positiveExpPacket w a t))
      (Real.log (positiveExpPacket w a (t + h)))
      (Real.log (positiveExpPacket w a (t + 2 * h))) := by
  have hc := (convexOn_log_expSum (fun i => Real.exp (w i)) a
    (Nat.succ_pos m) (fun i => Real.exp_pos (w i))).2
      (Set.mem_univ t) (Set.mem_univ (t + 2 * h))
      (show 0 ≤ (1 / 2 : ℝ) by positivity)
      (show 0 ≤ (1 / 2 : ℝ) by positivity) (by ring)
  have he : (1 / 2 : ℝ) * t + (1 / 2 : ℝ) * (t + 2 * h) = t + h := by ring
  simp only [smul_eq_mul, he] at hc
  unfold logStepCurvature positiveExpPacket
  linarith

/-- A mixture may decay in absolute size while its relative steps increase. -/
theorem positiveExpPacket_relativeStep_le {m : ℕ}
    (w a : Fin (m + 1) → ℝ) (t h : ℝ) :
    relativeStep (positiveExpPacket w a t) (positiveExpPacket w a (t + h)) ≤
      relativeStep (positiveExpPacket w a (t + h)) (positiveExpPacket w a (t + 2 * h)) := by
  have hr (s r : ℝ) : relativeStep (positiveExpPacket w a s) (positiveExpPacket w a r) =
      logRelativeStep (Real.log (positiveExpPacket w a s)) (Real.log (positiveExpPacket w a r)) := by
    rw [← relativeStep_exp, Real.exp_log (positiveExpPacket_pos w a s),
      Real.exp_log (positiveExpPacket_pos w a r)]
  rw [hr, hr, logRelativeStep_le_iff]
  exact positiveExpPacket_log_curvature_nonneg w a t h

theorem positiveExpPacket_sample_moment {m : ℕ}
    (w a : Fin (m + 1) → ℝ) (t h : ℝ) (k : ℕ) :
    configMoment Finset.univ (fun i => Real.exp (w i) * Real.exp (a i * t))
      (fun i => (Real.exp (a i * h) : ℂ)) k =
        (positiveExpPacket w a (t + (k : ℝ) * h) : ℂ) := by
  unfold configMoment positiveExpPacket expSum
  simp only [← Complex.ofReal_pow, ← Complex.ofReal_mul, ← Complex.ofReal_sum]
  apply congrArg Complex.ofReal
  apply Finset.sum_congr rfl
  intro i _
  have hp : Real.exp (a i * h) ^ k = Real.exp ((k : ℝ) * (a i * h)) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ih, ← Real.exp_add]
      congr 1
      push_cast
      ring
  rw [hp, mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- Relative acceleration is the pairwise dispersion of the sampled multipliers. -/
theorem positiveExpPacket_stepDeterminant_pair_sum {m : ℕ}
    (w a : Fin (m + 1) → ℝ) (t h : ℝ) :
    2 * stepDeterminant (positiveExpPacket w a t) (positiveExpPacket w a (t + h))
      (positiveExpPacket w a (t + 2 * h)) =
        ∑ i, ∑ j,
          (Real.exp (w i) * Real.exp (a i * t)) *
          (Real.exp (w j) * Real.exp (a j * t)) *
          (Real.exp (a i * h) - Real.exp (a j * h)) ^ (2 : ℕ) := by
  have hp := configTuranDeterminant_eq_pair_sum Finset.univ
    (fun i => Real.exp (w i) * Real.exp (a i * t)) (fun i => (Real.exp (a i * h) : ℂ))
  unfold configTuranDeterminant at hp
  simp only [positiveExpPacket_sample_moment, Nat.cast_zero, zero_mul, add_zero,
    Nat.cast_one, one_mul, Nat.cast_ofNat] at hp
  unfold stepDeterminant
  exact_mod_cast hp

/-- Vanishing sampled curvature means every mode has the same sampled multiplier. -/
theorem positiveExpPacket_stepDeterminant_zero_iff {m : ℕ}
    (w a : Fin (m + 1) → ℝ) (t h : ℝ) :
    stepDeterminant (positiveExpPacket w a t) (positiveExpPacket w a (t + h))
      (positiveExpPacket w a (t + 2 * h)) = 0 ↔
        ∀ i j, a i * h = a j * h := by
  let term (i j : Fin (m + 1)) :=
    (Real.exp (w i) * Real.exp (a i * t)) *
    (Real.exp (w j) * Real.exp (a j * t)) *
    (Real.exp (a i * h) - Real.exp (a j * h)) ^ (2 : ℕ)
  have ht (i j : Fin (m + 1)) : 0 ≤ term i j := by dsimp [term]; positivity
  have hp : 2 * stepDeterminant (positiveExpPacket w a t) (positiveExpPacket w a (t + h))
      (positiveExpPacket w a (t + 2 * h)) = ∑ i, ∑ j, term i j :=
    positiveExpPacket_stepDeterminant_pair_sum w a t h
  have hz : stepDeterminant (positiveExpPacket w a t) (positiveExpPacket w a (t + h))
      (positiveExpPacket w a (t + 2 * h)) = 0 ↔ (∑ i, ∑ j, term i j) = 0 := by
    rw [← hp]
    constructor <;> intro hh <;> linarith
  rw [hz]
  constructor
  · intro hh i j
    have hi := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => Finset.sum_nonneg (fun j _ => ht i j))).mp hh i (Finset.mem_univ i)
    have hij := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => ht i j)).mp hi j
      (Finset.mem_univ j)
    have hw : (Real.exp (w i) * Real.exp (a i * t)) *
        (Real.exp (w j) * Real.exp (a j * t)) ≠ 0 := by positivity
    have he := (mul_eq_zero.mp hij).resolve_left hw
    exact Real.exp_injective (sub_eq_zero.mp (sq_eq_zero_iff.mp he))
  · intro hh
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j _
    simp [term, hh i j]

/-- Exact acceleration keeps the positive normalization visible. -/
theorem positiveExpPacket_relativeStep_difference {m : ℕ}
    (w a : Fin (m + 1) → ℝ) (t h : ℝ) :
    relativeStep (positiveExpPacket w a (t + h)) (positiveExpPacket w a (t + 2 * h)) -
      relativeStep (positiveExpPacket w a t) (positiveExpPacket w a (t + h)) =
        stepDeterminant (positiveExpPacket w a t) (positiveExpPacket w a (t + h))
          (positiveExpPacket w a (t + 2 * h)) /
            (positiveExpPacket w a t * positiveExpPacket w a (t + h)) := by
  unfold relativeStep stepDeterminant
  rw [div_sub_div _ _ (positiveExpPacket_pos w a (t + h)).ne'
    (positiveExpPacket_pos w a t).ne']
  congr 1 <;> ring

/-- A neutral relative-gap observation is precisely unresolved spectral dispersion. -/
theorem positiveExpPacket_relativeStep_eq_iff {m : ℕ}
    (w a : Fin (m + 1) → ℝ) (t h : ℝ) :
    relativeStep (positiveExpPacket w a (t + h)) (positiveExpPacket w a (t + 2 * h)) =
      relativeStep (positiveExpPacket w a t) (positiveExpPacket w a (t + h)) ↔
        ∀ i j, a i * h = a j * h := by
  rw [← sub_eq_zero, positiveExpPacket_relativeStep_difference, div_eq_zero_iff]
  have hd := mul_ne_zero (positiveExpPacket_pos w a t).ne'
    (positiveExpPacket_pos w a (t + h)).ne'
  simp only [hd, or_false, positiveExpPacket_stepDeterminant_zero_iff]

/-- Exponential-packet sampling is exactly the static-mixture partition with negated rates. -/
theorem staticHeterogeneityPartition_eq_positiveExpPacket {m : ℕ}
    (w rate : Fin (m + 1) → ℝ) (t : ℝ) :
    _root_.HTGeometry.staticHeterogeneityPartition (fun i => Real.exp (w i)) rate t =
      positiveExpPacket w (fun i => -rate i) t := by
  simp [_root_.HTGeometry.staticHeterogeneityPartition, _root_.HTGeometry.staticHeterogeneityWeight,
    positiveExpPacket, expSum, neg_mul]

theorem staticHeterogeneityPartition_relativeStep_le {m : ℕ}
    (w rate : Fin (m + 1) → ℝ) (t h : ℝ) :
    relativeStep
      (_root_.HTGeometry.staticHeterogeneityPartition (fun i => Real.exp (w i)) rate t)
      (_root_.HTGeometry.staticHeterogeneityPartition (fun i => Real.exp (w i)) rate (t + h)) ≤
    relativeStep
      (_root_.HTGeometry.staticHeterogeneityPartition (fun i => Real.exp (w i)) rate (t + h))
      (_root_.HTGeometry.staticHeterogeneityPartition (fun i => Real.exp (w i)) rate (t + 2 * h)) := by
  simp only [staticHeterogeneityPartition_eq_positiveExpPacket]
  exact positiveExpPacket_relativeStep_le w (fun i => -rate i) t h

end
end GaloisForLFunctions.HTGeometry
