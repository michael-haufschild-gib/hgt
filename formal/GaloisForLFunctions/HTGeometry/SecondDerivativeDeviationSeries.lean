import GaloisForLFunctions.HTGeometry.MaximumTermProfileMoments

/-!
# The second derivative of an entire coefficient series

`z² f″(z)` is the series carrying the falling-factorial index weight `n(n−1)`.  This is the
order-two companion of `mul_deriv_coeffFun_eq`, and it is what an order-two Wiman--Valiron estimate
is stated against.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter

variable {a : ℕ → ℂ}

/-- The coefficient sequence of the derivative. -/
noncomputable def derivCoeffs (a : ℕ → ℂ) : ℕ → ℂ := fun m => ((m : ℂ) + 1) * a (m + 1)

/-- **The derivative coefficients are entire.** -/
theorem entireCoeffs_derivCoeffs (ha : EntireCoeffs a) : EntireCoeffs (derivCoeffs a) := by
  intro r hr
  have hmul : EntireCoeffs (fun n : ℕ => (n : ℂ) * a n) := entireCoeffs_mul_index ha
  have hshift : Tendsto (fun m : ℕ => ‖((m : ℂ) + 1) * a (m + 1)‖ * r ^ (m + 1))
      atTop (nhds 0) := by
    have h := (hmul r hr).comp (Filter.tendsto_add_atTop_nat 1)
    refine h.congr fun m => ?_
    simp only [Function.comp_apply]
    congr 2
    push_cast
    ring
  have hscale : Tendsto (fun m : ℕ => (1 / r) * (‖((m : ℂ) + 1) * a (m + 1)‖ * r ^ (m + 1)))
      atTop (nhds 0) := by simpa using hshift.const_mul (1 / r)
  refine hscale.congr fun m => ?_
  rw [derivCoeffs, pow_succ]
  field_simp

/-- The terms of an entire coefficient series are summable at every point.  (The corpus proves the
same statement in `GapSeriesEntireCarrier`; it is restated here so that this module stays off the
lacunary stack.) -/
theorem summable_entireCoeffs_term {b : ℕ → ℂ} (hb : EntireCoeffs b) (z : ℂ) :
    Summable fun m : ℕ => b m * z ^ m := by
  have hr : (0 : ℝ) < ‖z‖ + 1 := by positivity
  refine Summable.of_norm (Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    (summable_term hb hr))
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg z) (by linarith) n)
    (norm_nonneg _)

/-- **The derivative is the series of the shifted coefficients.** -/
theorem deriv_coeffFun_eq (ha : EntireCoeffs a) (z : ℂ) :
    deriv (coeffFun a) z = coeffFun (derivCoeffs a) z := by
  rw [(hasDerivAt_coeffFun ha z).deriv, coeffFun_eq_tsum]
  have hsum : Summable fun n : ℕ => (n : ℂ) * a n * z ^ (n - 1) := by
    rw [← summable_nat_add_iff 1]
    refine (summable_entireCoeffs_term (entireCoeffs_derivCoeffs ha) z).congr fun m => ?_
    rw [derivCoeffs]
    simp only [Nat.add_sub_cancel]
    push_cast
    ring
  rw [hsum.tsum_eq_zero_add]
  simp only [Nat.cast_zero, zero_mul, Nat.zero_sub, pow_zero, zero_add]
  refine tsum_congr fun m => ?_
  rw [derivCoeffs]
  simp only [Nat.add_sub_cancel]
  push_cast
  ring

/-- **The second derivative with the coordinate weight is the falling-factorial series.** -/
theorem mul_sq_deriv2_coeffFun_eq (ha : EntireCoeffs a) (z : ℂ) :
    z ^ (2 : ℕ) * deriv (deriv (coeffFun a)) z
      = ∑' n : ℕ, ((n : ℂ) * ((n : ℂ) - 1)) * a n * z ^ n := by
  have hfun : deriv (coeffFun a) = coeffFun (derivCoeffs a) := funext (deriv_coeffFun_eq ha)
  have hb : EntireCoeffs (derivCoeffs a) := entireCoeffs_derivCoeffs ha
  have h1 : z * deriv (coeffFun (derivCoeffs a)) z
      = ∑' m : ℕ, (m : ℂ) * derivCoeffs a m * z ^ m := mul_deriv_coeffFun_eq hb z
  have hsum : Summable fun m : ℕ => (m : ℂ) * derivCoeffs a m * z ^ m := by
    refine (summable_entireCoeffs_term (entireCoeffs_mul_index hb) z).congr fun m => ?_
    ring
  have hstep : z ^ (2 : ℕ) * deriv (deriv (coeffFun a)) z
      = z * ∑' m : ℕ, (m : ℂ) * derivCoeffs a m * z ^ m := by
    rw [hfun, ← h1]
    ring
  have hsum2 : Summable fun n : ℕ => ((n : ℂ) * ((n : ℂ) - 1)) * a n * z ^ n := by
    refine Summable.of_norm_bounded
      (g := fun n : ℕ => ‖((n : ℂ) * ((n : ℂ) * a n)) * z ^ n‖)
      ((summable_entireCoeffs_term (entireCoeffs_mul_index (entireCoeffs_mul_index ha)) z).norm)
      fun n => ?_
    have hkey : ‖(n : ℂ)‖ * ‖(n : ℂ) - 1‖ ≤ ‖(n : ℂ)‖ * ‖(n : ℂ)‖ := by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        have h1 : ((n : ℂ) - 1) = (((n : ℝ) - 1 : ℝ) : ℂ) := by push_cast; ring
        rw [h1, Complex.norm_real, Complex.norm_natCast, Real.norm_eq_abs]
        have hge : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        rw [abs_of_nonneg (by linarith)]
        linarith
    have hL : ‖((n : ℂ) * ((n : ℂ) - 1)) * a n * z ^ n‖
        = (‖(n : ℂ)‖ * ‖(n : ℂ) - 1‖) * (‖a n‖ * ‖z ^ n‖) := by
      simp only [norm_mul]
      ring
    have hR : ‖((n : ℂ) * ((n : ℂ) * a n)) * z ^ n‖
        = (‖(n : ℂ)‖ * ‖(n : ℂ)‖) * (‖a n‖ * ‖z ^ n‖) := by
      simp only [norm_mul]
      ring
    rw [hL, hR]
    exact mul_le_mul_of_nonneg_right hkey (by positivity)
  rw [hstep, ← Summable.tsum_mul_left _ hsum, hsum2.tsum_eq_zero_add]
  simp only [Nat.cast_zero, zero_mul, zero_sub, pow_zero, zero_add]
  refine tsum_congr fun m => ?_
  rw [derivCoeffs, pow_succ]
  push_cast
  ring

/-! ## The order-two deviation series -/

private theorem norm_deviation_sq_term (a : ℕ → ℂ) (z : ℂ) (n k : ℕ) :
    ‖((n : ℂ) - (k : ℂ)) ^ (2 : ℕ) * a n * z ^ n‖
      = ((n : ℝ) - (k : ℝ)) ^ (2 : ℕ) * (‖a n‖ * ‖z‖ ^ n) := by
  have hidx : ‖((n : ℂ) - (k : ℂ))‖ = |(n : ℝ) - (k : ℝ)| := by
    rw [show ((n : ℂ) - (k : ℂ)) = (((n : ℝ) - (k : ℝ) : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs]
  simp only [norm_mul, norm_pow, hidx, sq_abs]
  ring

theorem summable_deviation_sq_term (ha : EntireCoeffs a) {z : ℂ} (hz : 0 < ‖z‖) (k : ℕ) :
    Summable fun n : ℕ => ((n : ℂ) - (k : ℂ)) ^ (2 : ℕ) * a n * z ^ n :=
  Summable.of_norm ((summable_index_deviation_sq ha hz k).congr fun n =>
    (norm_deviation_sq_term a z n k).symm)

/-- **The order-two deviation series.**  `z² f″(z) − k(k−1) f(z)` splits into the squared-deviation
series and `(2k−1)` times the order-one deviation. -/
theorem mul_sq_deriv2_sub_eq_tsum (ha : EntireCoeffs a) {z : ℂ} (hz : 0 < ‖z‖) (k : ℕ) :
    z ^ (2 : ℕ) * deriv (deriv (coeffFun a)) z - ((k : ℂ) * ((k : ℂ) - 1)) * coeffFun a z
      = (∑' n : ℕ, ((n : ℂ) - (k : ℂ)) ^ (2 : ℕ) * a n * z ^ n)
        + (2 * (k : ℂ) - 1) * (z * deriv (coeffFun a) z - (k : ℂ) * coeffFun a z) := by
  have hfall : Summable fun n : ℕ => ((n : ℂ) * ((n : ℂ) - 1)) * a n * z ^ n := by
    refine Summable.of_norm_bounded
      (g := fun n : ℕ => ‖((n : ℂ) * ((n : ℂ) * a n)) * z ^ n‖)
      ((summable_entireCoeffs_term (entireCoeffs_mul_index (entireCoeffs_mul_index ha)) z).norm)
      fun n => ?_
    have hkey : ‖(n : ℂ)‖ * ‖(n : ℂ) - 1‖ ≤ ‖(n : ℂ)‖ * ‖(n : ℂ)‖ := by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        have h1 : ((n : ℂ) - 1) = (((n : ℝ) - 1 : ℝ) : ℂ) := by push_cast; ring
        rw [h1, Complex.norm_real, Complex.norm_natCast, Real.norm_eq_abs]
        have hge : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        rw [abs_of_nonneg (by linarith)]
        linarith
    have hL : ‖((n : ℂ) * ((n : ℂ) - 1)) * a n * z ^ n‖
        = (‖(n : ℂ)‖ * ‖(n : ℂ) - 1‖) * (‖a n‖ * ‖z ^ n‖) := by
      simp only [norm_mul]; ring
    have hR : ‖((n : ℂ) * ((n : ℂ) * a n)) * z ^ n‖
        = (‖(n : ℂ)‖ * ‖(n : ℂ)‖) * (‖a n‖ * ‖z ^ n‖) := by
      simp only [norm_mul]; ring
    rw [hL, hR]
    exact mul_le_mul_of_nonneg_right hkey (by positivity)
  have hidx : Summable fun n : ℕ => (n : ℂ) * a n * z ^ n := by
    refine (summable_entireCoeffs_term (entireCoeffs_mul_index ha) z).congr fun n => ?_
    ring
  have hc : Summable fun n : ℕ => a n * z ^ n := summable_entireCoeffs_term ha z
  have hdev : Summable fun n : ℕ => ((n : ℂ) - (k : ℂ)) ^ (2 : ℕ) * a n * z ^ n :=
    summable_deviation_sq_term ha hz k
  rw [mul_sq_deriv2_coeffFun_eq ha z, coeffFun_eq_tsum, mul_deriv_coeffFun_eq ha z,
    ← tsum_mul_left, ← tsum_mul_left, ← Summable.tsum_sub hidx (hc.mul_left (k : ℂ)),
    ← Summable.tsum_mul_left, ← Summable.tsum_add hdev,
    ← Summable.tsum_sub hfall (hc.mul_left ((k : ℂ) * ((k : ℂ) - 1)))]
  · exact tsum_congr fun n => by ring
  · exact (hidx.sub (hc.mul_left (k : ℂ))).mul_left _
  · exact hidx.sub (hc.mul_left (k : ℂ))

/-- **The order-two deviation estimate.** -/
theorem norm_mul_sq_deriv2_sub_le (ha : EntireCoeffs a) {z : ℂ} (hz : 0 < ‖z‖) (k : ℕ) :
    ‖z ^ (2 : ℕ) * deriv (deriv (coeffFun a)) z - ((k : ℂ) * ((k : ℂ) - 1)) * coeffFun a z‖
      ≤ (∑' n : ℕ, ((n : ℝ) - (k : ℝ)) ^ (2 : ℕ) * (‖a n‖ * ‖z‖ ^ n))
        + (2 * (k : ℝ) + 1) * ‖z * deriv (coeffFun a) z - (k : ℂ) * coeffFun a z‖ := by
  rw [mul_sq_deriv2_sub_eq_tsum ha hz k]
  have hdev : Summable fun n : ℕ => ((n : ℂ) - (k : ℂ)) ^ (2 : ℕ) * a n * z ^ n :=
    summable_deviation_sq_term ha hz k
  have h1 : ‖∑' n : ℕ, ((n : ℂ) - (k : ℂ)) ^ (2 : ℕ) * a n * z ^ n‖
      ≤ ∑' n : ℕ, ((n : ℝ) - (k : ℝ)) ^ (2 : ℕ) * (‖a n‖ * ‖z‖ ^ n) := by
    refine le_trans (norm_tsum_le_tsum_norm ?_) (le_of_eq (tsum_congr fun n => ?_))
    · exact (summable_index_deviation_sq ha hz k).congr fun n =>
        (norm_deviation_sq_term a z n k).symm
    · exact norm_deviation_sq_term a z n k
  have h2 : ‖(2 * (k : ℂ) - 1) * (z * deriv (coeffFun a) z - (k : ℂ) * coeffFun a z)‖
      ≤ (2 * (k : ℝ) + 1) * ‖z * deriv (coeffFun a) z - (k : ℂ) * coeffFun a z‖ := by
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    have hcast : (2 * (k : ℂ) - 1) = (((2 * (k : ℝ) - 1 : ℝ)) : ℂ) := by push_cast; ring
    rw [hcast, Complex.norm_real, Real.norm_eq_abs]
    rcases le_total (1 : ℝ) (2 * (k : ℝ)) with h | h
    · rw [abs_of_nonneg (by linarith)]; linarith
    · rw [abs_of_nonpos (by linarith)]
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
  exact le_trans (norm_add_le _ _) (add_le_add h1 h2)

end GaloisForLFunctions.HTGeometry
