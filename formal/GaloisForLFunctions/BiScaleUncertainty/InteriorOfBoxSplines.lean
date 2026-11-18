import GaloisForLFunctions.BiScaleUncertainty.SplineProbeFiniteShiftBounds

/-!
# Positivity inside the support of the box splines

An interior point of the next convolution has an open interval of
decompositions into interior points of its two factors.
-/

noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge

open MeasureTheory Filter RHTower.WeilDeletion
open scoped Convolution

/-- Every point in the interior of the support has positive convolution density. -/
theorem upow_unit_pos (n : ℕ) {x : ℝ} (hx : |x| < n + 1) :
    0 < upow 1 n x := by
  induction n generalizing x with
  | zero =>
      have hx' : -1 < x ∧ x < 1 := by simpa using abs_lt.mp hx
      change 0 < (Set.Icc (-1 : ℝ) 1).indicator (fun _ => 1 / (2 * 1 : ℝ)) x
      rw [Set.indicator_of_mem (show x ∈ Set.Icc (-1 : ℝ) 1 from ⟨hx'.1.le, hx'.2.le⟩)]
      norm_num
  | succ n ih =>
      have hx' := abs_lt.mp hx
      push_cast at hx'
      let a : ℝ := max (-1) (x - (n + 1))
      let b : ℝ := min 1 (x + (n + 1))
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have hab : a < b := by
        dsimp only [a, b]
        exact max_lt (lt_min (by norm_num) (by linarith only [hx'.1]))
          (lt_min (by linarith only [hx'.2]) (by linarith only [hn]))
      have hi : Integrable (fun t : ℝ => unif 1 t * upow 1 n (x - t)) :=
        ((integrable_upow 1 n).comp_sub_left x).bdd_mul
          (integrable_unif 1).aestronglyMeasurable
          (Eventually.of_forall fun t => by
            simpa only [Real.norm_eq_abs, abs_of_nonneg (unif_nonneg one_pos t)] using unif_one_le_half t)
      have hsub : Set.Ioo a b ⊆ Function.support (fun t => unif 1 t * upow 1 n (x - t)) := by
        intro t ht
        have ht0 : -1 < t := lt_of_le_of_lt (le_max_left _ _) ht.1
        have ht1 : t < 1 := lt_of_lt_of_le ht.2 (min_le_left _ _)
        have htx0 : x - (n + 1) < t := lt_of_le_of_lt (le_max_right _ _) ht.1
        have htx1 : t < x + (n + 1) := lt_of_lt_of_le ht.2 (min_le_right _ _)
        have hp : 0 < upow 1 n (x - t) := ih (abs_lt.mpr
          ⟨by linarith only [htx1], by linarith only [htx0]⟩)
        have hu : unif 1 t = (1 / 2 : ℝ) := by
          unfold unif
          rw [Set.indicator_of_mem (show t ∈ Set.Icc (-1 : ℝ) 1 from ⟨ht0.le, ht1.le⟩)]
          norm_num
        exact (mul_pos (by rw [hu]; norm_num) hp).ne'
      have hv : 0 < volume (Set.Ioo a b) := by
        rw [Real.volume_Ioo]
        exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)
      have hp := (integral_pos_iff_support_of_nonneg
        (fun t => mul_nonneg (unif_nonneg one_pos t) (upow_nonneg one_pos n (x - t))) hi).mpr
          (lt_of_lt_of_le hv (measure_mono hsub))
      simpa only [upow, convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul] using hp

theorem cubicSpline_pos_of_abs_lt_four {x : ℝ} (hx : |x| < 4) : 0 < cubicSpline x :=
  upow_unit_pos 3 (by simpa only [Nat.cast_ofNat, show (3:ℝ)+1=4 by norm_num] using hx)

#print axioms cubicSpline_pos_of_abs_lt_four

end GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge
