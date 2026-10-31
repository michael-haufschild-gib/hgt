import GaloisForLFunctions.RHTower.GaussianEvenCarrier
import GaloisForLFunctions.RHTower.HardyPhaseCellCancellation

/-!
# An explicit Gamma dilation constant

A telescoping majorant bounds trigamma on the quarter line by twenty.
Together with the vertical estimate this bounds the logarithmic derivative
of the Gamma phase rate by five, uniformly over all frequencies.
-/

noncomputable section
open Set Filter Topology
namespace GaloisForLFunctions.ArithmeticIncidencePositivity
open _root_.RHTower

/-- The quarter-line trigamma series has the explicit uniform norm bound twenty. -/
theorem norm_deriv_digamma_quarter_le (t : ℝ) :
    ‖deriv Complex.digamma ((1 / 4 : ℂ) + (t : ℂ) * Complex.I)‖ ≤ 20 := by
  let z : ℂ := (1 / 4 : ℂ) + (t : ℂ) * Complex.I
  have hz : z.re = 1 / 4 := by simp only [z]; norm_num
  have hterm (n : ℕ) : ‖((z + (n : ℂ)) ^ 2)⁻¹‖ ≤
      5 * (1 / ((1 / 4 : ℝ) + n) - 1 / ((1 / 4 : ℝ) + (n + 1 : ℕ))) := by
    let a : ℝ := 1 / 4 + n
    have ha : 0 < a := by dsimp only [a]; positivity
    have ha1 : 0 < a + 1 := by positivity
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hge : a ≤ ‖z + (n : ℂ)‖ := by
      have h := Complex.re_le_norm (z + (n : ℂ))
      simpa only [Complex.add_re, Complex.natCast_re, hz, a] using h
    have hs : a ^ 2 ≤ ‖z + (n : ℂ)‖ ^ 2 := pow_le_pow_left₀ ha.le hge 2
    have hrat : 1 / a ^ 2 ≤ 5 * (1 / a - 1 / (a + 1)) := by
      have heq : 5 * (1 / a - 1 / (a + 1)) = 5 / (a * (a + 1)) := by
        field_simp
        ring
      rw [heq, div_le_div_iff₀ (sq_pos_of_pos ha) (mul_pos ha ha1)]
      have hp := mul_nonneg ha.le (show 0 ≤ 4 * a - 1 by dsimp only [a]; linarith only [hn])
      nlinarith only [hp]
    rw [norm_inv, norm_pow, ← one_div]
    have hnorm := one_div_le_one_div_of_le (sq_pos_of_pos ha) hs
    simpa only [a, Nat.cast_add, Nat.cast_one, add_assoc] using hnorm.trans hrat
  have hbound (N : ℕ) : ‖∑ n ∈ Finset.range N, ((z + (n : ℂ)) ^ 2)⁻¹‖ ≤ 20 := by
    calc
      _ ≤ ∑ n ∈ Finset.range N, ‖((z + (n : ℂ)) ^ 2)⁻¹‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.range N,
          5 * (1 / ((1 / 4 : ℝ) + n) - 1 / ((1 / 4 : ℝ) + (n + 1 : ℕ))) :=
        Finset.sum_le_sum fun n _ => hterm n
      _ = 5 * (1 / (1 / 4 : ℝ) - 1 / ((1 / 4 : ℝ) + N)) := by
        rw [← Finset.mul_sum, Finset.sum_range_sub']
        norm_num
      _ ≤ 20 := by
        have h : 0 ≤ ((1 / 4 : ℝ) + N)⁻¹ := inv_nonneg.mpr (by positivity)
        norm_num
        linarith only [h]
  exact le_of_tendsto' (deriv_digamma_partialSum_tendsto (by rw [hz]; norm_num)).norm hbound

/-- A uniform derivative bound obtained directly from the trigamma series. -/
theorem abs_deriv_gammaHardyPhaseRate_le_five (t : ℝ) :
    |deriv gammaHardyPhaseRate t| ≤ 5 := by
  rw [deriv_gammaHardyPhaseRate]
  have harg : linePt t / 2 = (1 / 4 : ℂ) + ((t / 2 : ℝ) : ℂ) * Complex.I := by
    unfold linePt
    push_cast
    ring
  rw [abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  have hb : ‖deriv Complex.digamma (linePt t / 2)‖ ≤ 20 := by
    rw [harg]
    exact norm_deriv_digamma_quarter_le (t / 2)
  have h := (Complex.abs_im_le_norm (deriv Complex.digamma (linePt t / 2))).trans hb
  linarith only [h]

/-- The radial derivative is bounded by five on the whole positive ray. -/
theorem mul_abs_deriv_gammaHardyPhaseRate_le_five {t : ℝ} (ht : 0 < t) :
    t * |deriv gammaHardyPhaseRate t| ≤ 5 := by
  by_cases ht1 : t ≤ 1
  · exact (mul_le_mul_of_nonneg_left (abs_deriv_gammaHardyPhaseRate_le_five t) ht.le).trans
      (by linarith only [ht1])
  · have h1t : 1 ≤ t := (lt_of_not_ge ht1).le
    calc
      _ ≤ t * (1 / t ^ 2 + Real.pi / (4 * t)) :=
        mul_le_mul_of_nonneg_left (abs_deriv_gammaHardyPhaseRate_le ht) ht.le
      _ = 1 / t + Real.pi / 4 := by field_simp [ht.ne']
      _ ≤ 1 + Real.pi / 4 := add_le_add ((div_le_one ht).mpr h1t) le_rfl
      _ ≤ 5 := by linarith only [Real.pi_lt_four]

/-- Positive dilation has the explicit logarithmic Gamma modulus five. -/
theorem gammaHardyPhaseRate_logarithmic_dilation_bound {r : ℝ} (hr : 0 < r) (t : ℝ) :
    |gammaHardyPhaseRate (r * t) - gammaHardyPhaseRate t| ≤ 5 * |Real.log r| := by
  have hd (u : ℝ) : HasDerivAt (fun u => gammaHardyPhaseRate (Real.exp u))
      (deriv gammaHardyPhaseRate (Real.exp u) * Real.exp u) u :=
    (differentiable_gammaHardyPhaseRate (Real.exp u)).hasDerivAt.comp u (Real.hasDerivAt_exp u)
  have hdb (u : ℝ) : ‖deriv (fun u => gammaHardyPhaseRate (Real.exp u)) u‖ ≤ 5 := by
    rw [(hd u).deriv, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos u), mul_comm]
    exact mul_abs_deriv_gammaHardyPhaseRate_le_five (Real.exp_pos u)
  have hpos (s : ℝ) (hs : 0 < s) :
      |gammaHardyPhaseRate (r * s) - gammaHardyPhaseRate s| ≤ 5 * |Real.log r| := by
    have h := Convex.norm_image_sub_le_of_norm_deriv_le
      (s := (univ : Set ℝ)) (fun u _ => (hd u).differentiableAt)
      (fun u _ => hdb u) convex_univ (mem_univ (Real.log s)) (mem_univ (Real.log (r * s)))
    simpa only [Real.exp_log hs, Real.exp_log (mul_pos hr hs), Real.norm_eq_abs,
      Real.log_mul hr.ne' hs.ne', add_sub_cancel_right, Real.exp_add,
      Real.exp_log hr] using h
  have habs (s : ℝ) : gammaHardyPhaseRate |s| = gammaHardyPhaseRate s := by
    rcases le_total 0 s with hs | hs
    · rw [abs_of_nonneg hs]
    · rw [abs_of_nonpos hs, gammaHardyPhaseRate_neg]
  by_cases ht : t = 0
  · simp only [ht, mul_zero, sub_self, abs_zero]
    positivity
  · have h := hpos |t| (abs_pos.mpr ht)
    have heq : r * |t| = |r * t| := by rw [abs_mul, abs_of_pos hr]
    rw [heq, habs, habs] at h
    exact h

end GaloisForLFunctions.ArithmeticIncidencePositivity

#print axioms GaloisForLFunctions.ArithmeticIncidencePositivity.norm_deriv_digamma_quarter_le
#print axioms GaloisForLFunctions.ArithmeticIncidencePositivity.gammaHardyPhaseRate_logarithmic_dilation_bound
