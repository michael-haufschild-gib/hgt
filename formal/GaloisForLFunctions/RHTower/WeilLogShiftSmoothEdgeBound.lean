import GaloisForLFunctions.RHTower.WeilLogShiftCutoffReconstruction

/-!
# Exponential suppression at the recovery cutoff edge

The two facing smooth cutoff factors suppress an overlap of width at most 1/r
by exp(4−4r). On the actual recovery mesh the overlap width is at most 1/n.
The resulting diagonal bound retains this exponential loss, which the earlier
truncated-to-full comparison discarded.
-/

open Filter Topology MeasureTheory Zeta23 Real
open scoped BigOperators

noncomputable section

namespace RHTower

open WeilExcess

/-- The actual smooth transition has an explicit inverse-distance edge bound. -/
theorem smoothTransition_le_exp_edge {x : ℝ} (hx : 0 < x) (hxhalf : x ≤ 1 / 2) :
    smoothTransition x ≤ exp (2 - 1 / x) := by
  have hy : 0 < 1 - x := by linarith
  have hinv : (1 - x)⁻¹ ≤ 2 := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hy).mpr
    linarith
  have hglue : exp (-2) ≤ expNegInvGlue (1 - x) := by
    rw [expNegInvGlue, if_neg (not_le_of_gt hy)]
    apply exp_le_exp.mpr
    linarith only [hinv]
  have hden : exp (-2) ≤ expNegInvGlue x + expNegInvGlue (1 - x) := by
    have hn := expNegInvGlue.nonneg x
    linarith only [hglue, hn]
  change expNegInvGlue x / (expNegInvGlue x + expNegInvGlue (1 - x)) ≤ _
  calc
    _ ≤ expNegInvGlue x / exp (-2) :=
      div_le_div_of_nonneg_left (expNegInvGlue.nonneg x) (exp_pos _) hden
    _ = _ := by
      rw [expNegInvGlue, if_neg (not_le_of_gt hx), ← exp_sub]
      congr 1
      rw [inv_eq_one_div]
      ring

private theorem smoothTransition_pair_le {a b r : ℝ} (hr2 : 2 ≤ r)
    (hab : a + b ≤ 1 / r) :
    smoothTransition a * smoothTransition b ≤ exp (4 - 4 * r) := by
  by_cases ha : 0 < a
  · by_cases hb : 0 < b
    · have hr : 0 < r := by linarith
      have habhalf : a + b ≤ 1 / 2 :=
        hab.trans ((div_le_iff₀ hr).mpr (by linarith))
      have hsa := smoothTransition_le_exp_edge ha (by linarith)
      have hsb := smoothTransition_le_exp_edge hb (by linarith)
      have habpos := add_pos ha hb
      have hid : (1 / a + 1 / b) * (a + b) - 4 = (a - b) ^ 2 / (a * b) := by
        field_simp [ha.ne', hb.ne']
        ring
      have hsq : 0 ≤ (a - b) ^ 2 / (a * b) :=
        div_nonneg (sq_nonneg _) (mul_pos ha hb).le
      have hfour : 4 / (a + b) ≤ 1 / a + 1 / b := by
        apply (div_le_iff₀ habpos).mpr
        linarith only [hid, hsq]
      have hrfour : 4 * r ≤ 4 / (a + b) := by
        apply (le_div_iff₀ habpos).mpr
        have h := (le_div_iff₀ hr).mp hab
        nlinarith only [h]
      calc
        _ ≤ exp (2 - 1 / a) * exp (2 - 1 / b) :=
          mul_le_mul hsa hsb (smoothTransition.nonneg b) (exp_pos _).le
        _ ≤ _ := by
          rw [← exp_add]
          apply exp_le_exp.mpr
          linarith only [hfour, hrfour]
    · rw [smoothTransition.zero_of_nonpos (le_of_not_gt hb), mul_zero]
      exact (exp_pos _).le
  · rw [smoothTransition.zero_of_nonpos (le_of_not_gt ha), zero_mul]
    exact (exp_pos _).le

/-- Two facing cutoff edges supply an exponential loss whenever their total
overlap width is at most the reciprocal of r. -/
theorem bulkCutoff_product_le_exp_edge (L y r t : ℝ) (hr : 2 ≤ r)
    (hmargin : 2 * L - y ≤ 1 / r) :
    bulkCutoff L t * bulkCutoff L (t - y) ≤ exp (4 - 4 * r) := by
  have hpair := smoothTransition_pair_le hr
    (show (L - t) + (L + (t - y)) ≤ 1 / r by linarith only [hmargin])
  have hother : smoothTransition (L + t) * smoothTransition (L - (t - y)) ≤ 1 :=
    mul_le_one₀ (smoothTransition.le_one _) (smoothTransition.nonneg _)
      (smoothTransition.le_one _)
  calc
    _ = (smoothTransition (L - t) * smoothTransition (L + (t - y))) *
        (smoothTransition (L + t) * smoothTransition (L - (t - y))) := by
      unfold bulkCutoff
      ring
    _ ≤ (smoothTransition (L - t) * smoothTransition (L + (t - y))) * 1 :=
      mul_le_mul_of_nonneg_left hother
        (mul_nonneg (smoothTransition.nonneg _) (smoothTransition.nonneg _))
    _ ≤ _ := by simpa only [mul_one] using hpair

/-- The cutoff edge loss survives integration against the full positive kernel. -/
theorem truncatedRiemannAutocorr_le_exp_edge (L y r : ℝ) (hr : 2 ≤ r)
    (hmargin : 2 * L - y ≤ 1 / r) :
    truncatedRiemannAutocorr L y ≤ exp (4 - 4 * r) * riemannAutocorr y := by
  unfold truncatedRiemannAutocorr riemannAutocorr
  rw [← integral_const_mul]
  refine integral_mono (integrable_truncatedRiemannKernel_prod L y)
    ((integrable_riemannKernelReal_mul y).const_mul _) fun t => ?_
  calc
    _ = (bulkCutoff L t * bulkCutoff L (t - y)) *
        (riemannKernelReal t * riemannKernelReal (t - y)) := by
      unfold truncatedRiemannKernelReal
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (bulkCutoff_product_le_exp_edge L y r t hr hmargin)
      (mul_nonneg (riemannKernelReal_pos t).le (riemannKernelReal_pos (t - y)).le)

/-- The actual recovery diagonal lies within a 1/n overlap of the cutoff edge. -/
theorem weilLogShiftRecoveryCutoff_margin_le (n : ℕ) (hn : 2 ≤ n) :
    2 * weilLogShiftRecoveryCutoff n - (log n - log 2) ≤ 1 / (n : ℝ) := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hp : 0 < (n : ℝ) + 1 := by positivity
  have hlog := log_le_sub_one_of_pos (div_pos hp hnpos)
  rw [log_div hp.ne' hnpos.ne'] at hlog
  have hratio : ((n : ℝ) + 1) / n - 1 = 1 / (n : ℝ) := by
    field_simp [hnpos.ne']
    ring
  rw [hratio] at hlog
  calc
    _ = log ((n : ℝ) + 1) - log n := by
      simp only [weilLogShiftRecoveryCutoff, Nat.cast_add, Nat.cast_one]
      ring
    _ ≤ _ := hlog

/-- Sharpened diagonal comparison: the recovery mesh loses an exponential
factor exp(4−4n) through its smooth cutoff edges. -/
theorem weilLogShiftRecoveryWeight_smooth_edge_bound (n : ℕ) (hn : 2 ≤ n) :
    sqrt n * weilLogShiftRecoveryWeight n n ≤
      2 * exp (4 - 4 * n) * pairedLogKernel (log 2) n := by
  have hr : 0 < sqrt (n : ℝ) := sqrt_pos.mpr (by exact_mod_cast (show 0 < n by omega))
  have hcut := truncatedRiemannAutocorr_le_exp_edge (weilLogShiftRecoveryCutoff n)
    (log n - log 2) n (by exact_mod_cast hn) (weilLogShiftRecoveryCutoff_margin_le n hn)
  have hK : riemannAutocorr (log n - log 2) ≤ pairedLogKernel (log 2) n := by
    rw [show log n - log 2 = -(log 2 - log n) by ring, riemannAutocorr_neg]
    dsimp only [pairedLogKernel]
    have h := riemannAutocorr_nonneg (log 2 + log n)
    linarith only [h]
  rw [weilLogShiftRecoveryWeight_diagonal n hn]
  calc
    _ = 2 * truncatedRiemannAutocorr (weilLogShiftRecoveryCutoff n) (log n - log 2) := by
      field_simp [hr.ne']
    _ ≤ 2 * (exp (4 - 4 * n) * riemannAutocorr (log n - log 2)) :=
      mul_le_mul_of_nonneg_left hcut (by norm_num)
    _ ≤ 2 * (exp (4 - 4 * n) * pairedLogKernel (log 2) n) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hK (exp_pos _).le) (by norm_num)
    _ = _ := by ring

end RHTower
