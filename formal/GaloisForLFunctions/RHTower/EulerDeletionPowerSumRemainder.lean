import GaloisForLFunctions.RHTower.EulerDeletionMixedRefinementCarry
import GaloisForLFunctions.RHTower.ZetaCentredSawtoothContinuation
import Mathlib.Analysis.PSeries

/-!
# The actual power-sum remainder for mixed Euler deletion

The centered continuation formula gives a uniform remainder bound, weighted decay,
conjugation, and absolute convergence of the retained arithmetic series. These are
analytic consequences of the ordinary partial sums, with no assumed decay input.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory Set Filter Topology
namespace RHTower.DeletionMixedRefinement

/-- Centered ordinary power-sum error after retaining its half endpoint. -/
def powerSumRemainder (s : ℂ) (N : ℕ) : ℂ :=
  rawPrefix s N - riemannZeta s - (N : ℂ) ^ (1 - s) / (1 - s) - kernel s N / 2

private theorem rawPrefix_eq_Icc (s : ℂ) (N : ℕ) :
    rawPrefix s N = ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s) := by
  induction N with
  | zero => simp [rawPrefix]
  | succ N ih =>
      simp only [rawPrefix, Finset.sum_range_succ] at ih ⊢
      rw [Finset.sum_Icc_succ_top (by omega), ← ih]
      rfl

/-- The centered remainder is the actual absolutely integrable Bernoulli tail. -/
theorem powerSumRemainder_eq_bernoulli {s : ℂ} (hs : -1 < s.re) (hs1 : s ≠ 1)
    {N : ℕ} (hN : 1 ≤ N) :
    powerSumRemainder s N = s * (s + 1) * RHTower.zetaBernoulliTail N s := by
  have h := RHTower.zeta_eq_centredTruncated_of_re_gt_neg_one hN hs hs1
  rw [RHTower.zetaCentredTruncated, ← rawPrefix_eq_Icc] at h
  have hden : s - 1 = -(1 - s) := by ring
  rw [hden, div_neg] at h
  simp only [powerSumRemainder, kernel]
  linear_combination -h

/-- A uniform power bound for the Bernoulli tail at positive integer cutoffs. -/
theorem norm_bernoulliTail_le {s : ℂ} (hs : -1 < s.re) {N : ℕ} (hN : 1 ≤ N) :
    ‖RHTower.zetaBernoulliTail N s‖ ≤ (N : ℝ) ^ (-s.re - 1) / (s.re + 1) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hi := integrableOn_Ioi_rpow_of_lt (by linarith : -s.re - 2 < -1) hNpos
  have hb : ‖RHTower.zetaBernoulliTail N s‖ ≤
      ∫ x in Ioi (N : ℝ), x ^ (-s.re - 2) := by
    apply norm_integral_le_of_norm_le hi
    rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with x hx
    have hxpos := lt_trans hNpos hx
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hxpos,
      Complex.norm_real, Real.norm_eq_abs]
    have he : (-s - 1 - 1).re = -s.re - 2 := by simp; ring
    rw [he]
    exact mul_le_of_le_one_left (Real.rpow_nonneg hxpos.le _)
      (RHTower.abs_bernoulliPeriodic_le_one x)
  refine hb.trans_eq ?_
  rw [integral_Ioi_rpow_of_lt (by linarith : -s.re - 2 < -1) hNpos]
  rw [show -s.re - 2 + 1 = -s.re - 1 by ring]
  have hden : -s.re - 1 = -(s.re + 1) := by ring
  rw [hden, neg_div_neg_eq]

/-- The ordinary power-sum remainder decays one order faster than its endpoint weight. -/
theorem norm_powerSumRemainder_le {s : ℂ} (hs : -1 < s.re) (hs1 : s ≠ 1)
    {N : ℕ} (hN : 1 ≤ N) :
    ‖powerSumRemainder s N‖ ≤
      (‖s * (s + 1)‖ / (s.re + 1)) * (N : ℝ) ^ (-s.re - 1) := by
  rw [powerSumRemainder_eq_bernoulli hs hs1 hN, norm_mul]
  exact (mul_le_mul_of_nonneg_left (norm_bernoulliTail_le hs hN) (norm_nonneg _)).trans_eq
    (by ring)

/-- Multiplication by any strictly smaller power still kills the centered remainder. -/
theorem tendsto_powerSumRemainder_mul_cpow {s z : ℂ}
    (hs : -1 < s.re) (hs1 : s ≠ 1) (hz : z.re < s.re + 1) :
    Tendsto (fun N : ℕ => powerSumRemainder s N * (N : ℂ) ^ z) atTop (𝓝 0) := by
  have hlim : Tendsto (fun N : ℕ =>
      (‖s * (s + 1)‖ / (s.re + 1)) * (N : ℝ) ^ (z.re - s.re - 1)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (by linarith : 0 < s.re + 1 - z.re)).comp
      tendsto_natCast_atTop_atTop
    have he : -(s.re + 1 - z.re) = z.re - s.re - 1 := by ring
    simpa only [Function.comp_apply, he, mul_zero] using h.const_mul (‖s * (s + 1)‖ / (s.re + 1))
  apply squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by omega)]
  calc
    _ ≤ ((‖s * (s + 1)‖ / (s.re + 1)) * (N : ℝ) ^ (-s.re - 1)) *
        (N : ℝ) ^ z.re := mul_le_mul_of_nonneg_right (norm_powerSumRemainder_le hs hs1 hN)
          (Real.rpow_nonneg hNpos.le _)
    _ = _ := by rw [mul_assoc, ← Real.rpow_add hNpos]; congr 2; ring

/-- The centered power-sum remainder tends to zero on its continuation half-plane. -/
theorem tendsto_powerSumRemainder {s : ℂ} (hs : -1 < s.re) (hs1 : s ≠ 1) :
    Tendsto (powerSumRemainder s) atTop (𝓝 0) := by
  simpa using tendsto_powerSumRemainder_mul_cpow (z := 0) hs hs1 (by simpa using (show 0 < s.re + 1 by linarith))

/-- Conjugation commutes with positive-real-base complex powers. -/
theorem star_nat_cpow (N : ℕ) (z : ℂ) :
    star ((N : ℂ) ^ z) = (N : ℂ) ^ star z := by
  simpa only [Complex.star_def, map_natCast] using
    (Complex.cpow_conj (N : ℂ) z (by simpa only [Complex.natCast_arg] using Real.pi_pos.ne)).symm

/-- Negative-real-part powers vanish along the positive integers. -/
theorem tendsto_nat_cpow_zero {z : ℂ} (hz : z.re < 0) :
    Tendsto (fun N : ℕ => (N : ℂ) ^ z) atTop (𝓝 0) := by
  apply squeeze_zero_norm' ?_ ((tendsto_rpow_neg_atTop (neg_pos.2 hz)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ)))
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [Complex.norm_natCast_cpow_of_pos (by omega)]
  simp

/-- The centered main-free partial sums converge, including exponent zero. -/
theorem tendsto_centeredPowerPrefix {s : ℂ} (hs : -1 < s.re) (hs1 : s ≠ 1) :
    Tendsto (fun N : ℕ => rawPrefix s N - (N : ℂ) ^ (1 - s) / (1 - s) -
      kernel s N / 2) atTop (𝓝 (riemannZeta s)) := by
  have h := (tendsto_powerSumRemainder hs hs1).add_const (riemannZeta s)
  simpa only [zero_add] using h.congr (fun N => by dsimp [powerSumRemainder]; ring)

/-- The ordinary Dirichlet partial sums converge in the absolute half-plane. -/
theorem tendsto_rawPrefix {s : ℂ} (hs : 1 < s.re) :
    Tendsto (rawPrefix s) atTop (𝓝 (riemannZeta s)) := by
  have hs1 : s ≠ 1 := by intro h; simp [h] at hs
  have h := ((tendsto_powerSumRemainder (by linarith) hs1).add_const (riemannZeta s)).add
    ((tendsto_nat_cpow_zero (z := 1 - s) (by simp; linarith)).div_const (1 - s))
  have h' := h.add ((tendsto_nat_cpow_zero (z := -s) (by simp; linarith)).div_const 2)
  simpa only [zero_add, zero_div, add_zero] using
    h'.congr (fun N => by dsimp [powerSumRemainder, kernel]; ring)

/-- Centered continuation commutes with conjugation, proved from the actual partial sums. -/
theorem powerSum_zeta_star {s : ℂ} (hs : -1 < s.re) (hs1 : s ≠ 1) :
    riemannZeta (star s) = star (riemannZeta s) := by
  have ht : -1 < (star s).re := by simpa using hs
  have ht1 : star s ≠ 1 := by
    intro h
    apply hs1
    simpa using congrArg star h
  have h : Tendsto (fun N : ℕ => star (rawPrefix s N -
      (N : ℂ) ^ (1 - s) / (1 - s) - kernel s N / 2)) atTop
      (𝓝 (star (riemannZeta s))) :=
    (tendsto_centeredPowerPrefix hs hs1).star
  apply tendsto_nhds_unique (tendsto_centeredPowerPrefix ht ht1)
  convert h using 1
  ext N
  simp only [star_sub, star_div₀, star_one, star_ofNat,
    rawPrefix, star_sum, kernel, star_nat_cpow, star_neg]

/-- The retained error at the conjugate exponent is exactly the conjugate error. -/
theorem powerSumRemainder_star {s : ℂ} (hs : -1 < s.re) (hs1 : s ≠ 1) (N : ℕ) :
    powerSumRemainder (star s) N = star (powerSumRemainder s N) := by
  simp only [powerSumRemainder, powerSum_zeta_star hs hs1, rawPrefix, kernel,
    star_sub, star_div₀, star_sum, star_nat_cpow, star_one, star_ofNat, star_neg]

/-- Literal partial sum of the absolutely convergent retained remainder. -/
def remainderPrefix (s : ℂ) (p N : ℕ) : ℂ :=
  amplitude s p * ∑ n ∈ Finset.range N,
    kernel s (n + 1) * star (powerSumRemainder s (p * (n + 1)))

/-- Retained arithmetic remainder, with the ordinary power-sum error unchanged. -/
def infiniteRemainder (s : ℂ) (p : ℕ) : ℂ :=
  amplitude s p * ∑' n : ℕ,
    kernel s (n + 1) * star (powerSumRemainder s (p * (n + 1)))

/-- Absolute convergence of the exact remainder series throughout the positive half-plane. -/
theorem summable_norm_remainder {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1)
    {p : ℕ} (hp : 0 < p) :
    Summable (fun n : ℕ =>
      ‖kernel s (n + 1) * star (powerSumRemainder s (p * (n + 1)))‖) := by
  let C := (‖s * (s + 1)‖ / (s.re + 1)) * (p : ℝ) ^ (-s.re - 1)
  have hsum : Summable (fun n : ℕ => C * ((n + 1 : ℕ) : ℝ) ^ (-2 * s.re - 1)) :=
    ((summable_nat_add_iff 1).2 (Real.summable_nat_rpow.2 (by linarith))).mul_left C
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ?_ hsum
  intro n
  have hn : (0 : ℝ) < n + 1 := by positivity
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  rw [norm_mul, norm_star, kernel, Complex.norm_natCast_cpow_of_pos (by omega)]
  calc
    _ ≤ ((n + 1 : ℕ) : ℝ) ^ (-s).re *
        ((‖s * (s + 1)‖ / (s.re + 1)) * ((p * (n + 1) : ℕ) : ℝ) ^ (-s.re - 1)) :=
      mul_le_mul_of_nonneg_left (norm_powerSumRemainder_le (by linarith) hs1
        (Nat.succ_le_iff.2 (Nat.mul_pos hp (by omega)))) (Real.rpow_nonneg (by positivity) _)
    _ = C * ((n + 1 : ℕ) : ℝ) ^ (-2 * s.re - 1) := by
      simp only [Nat.cast_mul, Complex.neg_re]
      rw [Real.mul_rpow hp'.le (by positivity)]
      dsimp [C]
      calc
        _ = (‖s * (s + 1)‖ / (s.re + 1)) * (p : ℝ) ^ (-s.re - 1) *
            (((n + 1 : ℕ) : ℝ) ^ (-s.re) * ((n + 1 : ℕ) : ℝ) ^ (-s.re - 1)) := by ring
        _ = _ := by rw [← Real.rpow_add (by positivity)]; congr 2; ring

/-- Ordered truncations converge to the absolutely convergent arithmetic remainder. -/
theorem tendsto_remainderPrefix {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1)
    {p : ℕ} (hp : 0 < p) :
    Tendsto (remainderPrefix s p) atTop (𝓝 (infiniteRemainder s p)) := by
  exact ((summable_norm_iff.1 (summable_norm_remainder hs hs1 hp)).hasSum.tendsto_sum_nat).const_mul _

end RHTower.DeletionMixedRefinement
