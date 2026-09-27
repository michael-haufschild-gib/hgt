import GaloisForLFunctions.RHTower.LogarithmicSawtoothTail
import GaloisForLFunctions.RHTower.LogarithmicDilationPrimitiveQuadrature

/-!
# Uniform control of the reciprocal sawtooth correlation

Reflection reduces the integral to half its interval. There the other
clock is faster. Its signed tail bound controls the smooth exponential,
the complete floor sum, and the constant term separately at unit scale.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace RHTower

theorem logarithmicReciprocalSawtoothCorrelation_eq_twice_half (T : ℝ) :
    logarithmicReciprocalSawtoothCorrelation T =
      2 * ∫ s in (0 : ℝ)..(T / 2),
        logarithmicCenteredSawtooth (T - s) * logarithmicCenteredSawtooth s := by
  let p := fun s => logarithmicCenteredSawtooth (T - s) * logarithmicCenteredSawtooth s
  have href : (∫ s in (T / 2)..T, p s) = ∫ s in (0 : ℝ)..(T / 2), p s := by
    calc
      _ = ∫ s in (0 : ℝ)..(T / 2), p (T - s) := by
        simpa only [sub_self, sub_zero, show T - T / 2 = T / 2 by ring] using
          (intervalIntegral.integral_comp_sub_left p T (a := 0) (b := T / 2)).symm
      _ = _ := by
        apply intervalIntegral.integral_congr
        intro s _
        dsimp only [p]
        rw [sub_sub_cancel]
        exact mul_comm _ _
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_logarithmicReciprocalSawtooth T 0 (T / 2))
    (intervalIntegrable_logarithmicReciprocalSawtooth T (T / 2) T)
  change (∫ s in (0 : ℝ)..(T / 2), p s) + (∫ s in (T / 2)..T, p s) =
    logarithmicReciprocalSawtoothCorrelation T at hadd
  rw [href] at hadd
  change logarithmicReciprocalSawtoothCorrelation T = 2 * ∫ s in (0 : ℝ)..(T / 2), p s
  linarith only [hadd]

theorem abs_logarithmicReciprocalSawtoothCorrelation_le_uniform
    {T : ℝ} (hT : 0 ≤ T) : |logarithmicReciprocalSawtoothCorrelation T| ≤ 5 / 4 := by
  let H := T / 2
  let g := fun s => logarithmicCenteredSawtooth (T - s)
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  have hHT : H ≤ T := by dsimp only [H]; linarith
  have hg : IntervalIntegrable g volume 0 H := by
    simpa only [sub_self, sub_sub_cancel] using
      (intervalIntegrable_logarithmicCenteredSawtooth T (T - H)).comp_sub_left T
  have hex := hg.mul_continuousOn Real.continuous_exp.continuousOn
  have hfloor := intervalIntegrable_mul_logarithmicEntrySum_of_intervalIntegrable
    (fun _ => 1) g hg hH
  have hdec : (∫ s in (0 : ℝ)..H, g s * logarithmicCenteredSawtooth s) =
      (∫ s in (0 : ℝ)..H, g s * Real.exp s) -
        (∫ s in (0 : ℝ)..H, g s * logarithmicEntrySum (fun _ => 1) s) -
          (1 / 2) * ∫ s in (0 : ℝ)..H, g s := by
    rw [← intervalIntegral.integral_sub hex hfloor,
      ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub (hex.sub hfloor) (hg.const_mul (1 / 2))]
    apply intervalIntegral.integral_congr
    intro s _
    dsimp only
    rw [logarithmicEntrySum_one, natCast_floor_eq_intCast_floor (Real.exp_pos s).le]
    dsimp only [logarithmicCenteredSawtooth, Int.fract]
    ring
  have hscale : Real.exp H * Real.exp (-(T - H)) = 1 := by
    rw [← Real.exp_add, show H + -(T - H) = 0 by dsimp only [H]; ring, Real.exp_zero]
  have hunit : |∫ s in (0 : ℝ)..H, g s| ≤ 1 / 4 := by
    change |∫ s in (0 : ℝ)..H, logarithmicCenteredSawtooth (T - s)| ≤ _
    rw [intervalIntegral.integral_comp_sub_left, sub_zero]
    have hb := abs_integral_logarithmicCenteredSawtooth_le (a := T - H) (b := T)
      (by linarith only [hH])
    have he : Real.exp (-(T - H)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith only [hHT])
    linarith only [hb, he]
  have hweighted : |∫ s in (0 : ℝ)..H, g s * Real.exp s| ≤ 1 / 4 := by
    have heq : (∫ s in (0 : ℝ)..H, g s * Real.exp s) =
        Real.exp T * ∫ t in (T - H)..T, Real.exp (-t) * logarithmicCenteredSawtooth t := by
      calc
        _ = ∫ s in (0 : ℝ)..H,
            Real.exp T * (Real.exp (-(T - s)) * logarithmicCenteredSawtooth (T - s)) := by
          apply intervalIntegral.integral_congr
          intro s _
          dsimp only [g]
          rw [← mul_assoc, ← Real.exp_add, show T + -(T - s) = s by ring]
          exact mul_comm _ _
        _ = _ := by
          rw [intervalIntegral.integral_const_mul,
            intervalIntegral.integral_comp_sub_left
              (fun t => Real.exp (-t) * logarithmicCenteredSawtooth t), sub_zero]
    rw [heq, abs_mul, abs_of_pos (Real.exp_pos T)]
    calc
      _ ≤ Real.exp T * (Real.exp (-(2 * (T - H))) / 4) :=
        mul_le_mul_of_nonneg_left
          (abs_integral_exp_neg_mul_logarithmicCenteredSawtooth_le
            (by linarith only [hH] : T - H ≤ T)) (Real.exp_pos T).le
      _ = _ := by
        rw [← mul_div_assoc, ← Real.exp_add,
          show T + -(2 * (T - H)) = 0 by dsimp only [H]; ring, Real.exp_zero]
  have hsteps : |∫ s in (0 : ℝ)..H, g s * logarithmicEntrySum (fun _ => 1) s| ≤ 1 / 4 := by
    rw [integral_mul_logarithmicEntrySum_of_intervalIntegrable _ _ hg hH]
    simp only [one_mul]
    calc
      _ ≤ ∑ n ∈ Finset.Icc 1 ⌊Real.exp H⌋₊, |∫ s in Real.log n..H, g s| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _n ∈ Finset.Icc 1 ⌊Real.exp H⌋₊, Real.exp (-(T - H)) / 4 := by
        apply Finset.sum_le_sum
        intro n hn
        have hnpos : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
        have hlog : Real.log n ≤ H := (Real.log_le_iff_le_exp hnpos).mpr
          ((Nat.le_floor_iff (Real.exp_pos H).le).mp (Finset.mem_Icc.mp hn).2)
        dsimp only [g]
        rw [intervalIntegral.integral_comp_sub_left]
        exact abs_integral_logarithmicCenteredSawtooth_le (by linarith only [hlog])
      _ = (⌊Real.exp H⌋₊ : ℝ) * (Real.exp (-(T - H)) / 4) := by
        simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
      _ ≤ Real.exp H * (Real.exp (-(T - H)) / 4) :=
        mul_le_mul_of_nonneg_right (Nat.floor_le (Real.exp_pos H).le) (by positivity)
      _ = 1 / 4 := by rw [← mul_div_assoc, hscale]
  have hhalf : |∫ s in (0 : ℝ)..H, g s * logarithmicCenteredSawtooth s| ≤ 5 / 8 := by
    rw [hdec]
    calc
      _ ≤ |∫ s in (0 : ℝ)..H, g s * Real.exp s| +
          |∫ s in (0 : ℝ)..H, g s * logarithmicEntrySum (fun _ => 1) s| +
            |(1 / 2) * ∫ s in (0 : ℝ)..H, g s| :=
        (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
      _ ≤ 1 / 4 + 1 / 4 + (1 / 2 : ℝ) * (1 / 4) := by
        rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / 2)]
        exact add_le_add (add_le_add hweighted hsteps)
          (mul_le_mul_of_nonneg_left hunit (by positivity))
      _ = _ := by ring
  rw [logarithmicReciprocalSawtoothCorrelation_eq_twice_half, abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < 2)]
  change 2 * |∫ s in (0 : ℝ)..H, g s * logarithmicCenteredSawtooth s| ≤ _
  linarith only [hhalf]

end RHTower
