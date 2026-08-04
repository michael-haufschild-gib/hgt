import GaloisForLFunctions.RHTower.Sieve.GallagherLemma
import GaloisForLFunctions.RHTower.Sieve.DirichletIntegralBound
import GaloisForLFunctions.RHTower.Sieve.DirichletIntegralMeanValue

/-!
# The Gallagher polynomial is a Dirichlet polynomial

`logPoly a (Icc 1 N) w = ∑_{n ≤ N} a_n n^{2πiw}` is `dirPoly N a' (2πw)` after shifting the index,
so the mean value theorem transfers to the frequency variable of Gallagher's identity:

    ∫_{|w| ≤ W} |logPoly a (Icc 1 N) w|² dw ≤ (2πW + 4N(1+log N))/π · ∑_{n ≤ N} |a_n|² .

The factor `2` from the two halves of the symmetric range cancels the `2π` of the substitution down
to `π`.  Reflecting the negative half costs nothing: conjugating the coefficients leaves the `ℓ²`
norm unchanged.
-/

namespace RHTower.Sieve

open Complex MeasureTheory Finset

/-- Conjugating the coefficients reflects the frequency. -/
theorem dirPoly_conj_neg (N : ℕ) (c : Fin N → ℂ) (t : ℝ) :
    dirPoly N (fun n => (starRingEnd ℂ) (c n)) t = (starRingEnd ℂ) (dirPoly N c (-t)) := by
  rw [dirPoly, dirPoly, map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [map_mul, ← Complex.exp_conj]
  congr 1
  rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
  congr 1
  push_cast
  ring

/-- **The mean value theorem on a symmetric range.** -/
theorem integral_Icc_normSq_dirPoly_symm_le (N : ℕ) (c : Fin N → ℂ) {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in Set.Icc (-T) T, ‖dirPoly N c t‖ ^ 2)
      ≤ 2 * ((T + 4 * (N : ℝ) * (1 + Real.log N)) * ∑ m : Fin N, ‖c m‖ ^ 2) := by
  classical
  set g : ℝ → ℝ := fun t => ‖dirPoly N c t‖ ^ 2 with hg
  have hcg : Continuous g := ((continuous_dirPoly N c).norm).pow 2
  have hii : ∀ x y : ℝ, IntervalIntegrable g volume x y := fun x y =>
    hcg.intervalIntegrable x y
  have hle : -T ≤ T := by linarith
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle,
    ← intervalIntegral.integral_add_adjacent_intervals (hii (-T) 0) (hii 0 T)]
  -- the positive half
  have hpos : (∫ t in (0 : ℝ)..T, g t)
      ≤ (T + 4 * (N : ℝ) * (1 + Real.log N)) * ∑ m : Fin N, ‖c m‖ ^ 2 :=
    integral_normSq_dirPoly_le N c T
  -- the negative half, reflected
  have hrefl : (∫ t in (-T : ℝ)..0, g t) = ∫ t in (0 : ℝ)..T, g (-t) := by
    have h := intervalIntegral.integral_comp_mul_left (a := (0 : ℝ)) (b := T)
      (c := (-1 : ℝ)) g (by norm_num)
    simp only [neg_one_mul, neg_zero] at h
    rw [h, intervalIntegral.integral_symm (-T) 0, smul_eq_mul]
    ring
  have hconj : ∀ t : ℝ, g (-t) = ‖dirPoly N (fun n => (starRingEnd ℂ) (c n)) t‖ ^ 2 := by
    intro t
    rw [hg, dirPoly_conj_neg N c t, RCLike.norm_conj]
  have hneg : (∫ t in (-T : ℝ)..0, g t)
      ≤ (T + 4 * (N : ℝ) * (1 + Real.log N)) * ∑ m : Fin N, ‖c m‖ ^ 2 := by
    rw [hrefl]
    have hcongr : (∫ t in (0 : ℝ)..T, g (-t))
        = ∫ t in (0 : ℝ)..T, ‖dirPoly N (fun n => (starRingEnd ℂ) (c n)) t‖ ^ 2 := by
      exact intervalIntegral.integral_congr fun t _ => hconj t
    rw [hcongr]
    have hbase := integral_normSq_dirPoly_le N (fun n => (starRingEnd ℂ) (c n)) T
    have hnorm : ∑ m : Fin N, ‖(starRingEnd ℂ) (c m)‖ ^ 2 = ∑ m : Fin N, ‖c m‖ ^ 2 := by
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [RCLike.norm_conj]
    rwa [hnorm] at hbase
  linarith

/-- **The Gallagher polynomial is a Dirichlet polynomial.** -/
theorem logPoly_eq_dirPoly (a : ℕ → ℂ) (N : ℕ) (w : ℝ) :
    logPoly a (Finset.Icc 1 N) w
      = dirPoly N (fun n : Fin N => a ((n : ℕ) + 1)) (2 * Real.pi * w) := by
  classical
  rw [logPoly, dirPoly, ← image_succ_univ N, Finset.sum_image (succ_injOn N)]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hcast : ((((m : ℕ) + 1 : ℕ)) : ℝ) = ((m : ℕ) : ℝ) + 1 := by push_cast; ring
  rw [hcast, show (2 * Real.pi * (w * Real.log (((m : ℕ) : ℝ) + 1)))
      = 2 * Real.pi * w * Real.log (((m : ℕ) : ℝ) + 1) from by ring]

/-- **The frequency mean square of the Gallagher polynomial.** -/
theorem integral_Icc_normSq_logPoly_le (a : ℕ → ℂ) (N : ℕ) {W : ℝ} (hW : 0 ≤ W) :
    (∫ w in Set.Icc (-W) W, ‖logPoly a (Finset.Icc 1 N) w‖ ^ 2)
      ≤ (2 * Real.pi * W + 4 * (N : ℝ) * (1 + Real.log N)) / Real.pi
          * ∑ m : Fin N, ‖a ((m : ℕ) + 1)‖ ^ 2 := by
  classical
  set c : Fin N → ℂ := fun n : Fin N => a ((n : ℕ) + 1) with hc
  set g : ℝ → ℝ := fun t => ‖dirPoly N c t‖ ^ 2 with hg
  have hcg : Continuous g := ((continuous_dirPoly N c).norm).pow 2
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hle : -W ≤ W := by linarith
  have hstep : (∫ w in Set.Icc (-W) W, ‖logPoly a (Finset.Icc 1 N) w‖ ^ 2)
      = ∫ w in (-W : ℝ)..W, g (2 * Real.pi * w) := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle]
    refine intervalIntegral.integral_congr fun w _ => ?_
    rw [hg, logPoly_eq_dirPoly a N w]
  rw [hstep]
  rw [intervalIntegral.integral_comp_mul_left g (ne_of_gt hpi)]
  have hsub : (∫ t in (2 * Real.pi * -W : ℝ)..(2 * Real.pi * W), g t)
      = ∫ t in Set.Icc (-(2 * Real.pi * W)) (2 * Real.pi * W), g t := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by nlinarith : -(2 * Real.pi * W) ≤ 2 * Real.pi * W)]
    congr 1
    ring
  rw [hsub, smul_eq_mul]
  have hsymm := integral_Icc_normSq_dirPoly_symm_le N c
    (T := 2 * Real.pi * W) (by positivity)
  have hinv : (0 : ℝ) < (2 * Real.pi)⁻¹ := by positivity
  have hmul := mul_le_mul_of_nonneg_left hsymm hinv.le
  refine le_trans hmul (le_of_eq ?_)
  field_simp
  ring

end RHTower.Sieve
