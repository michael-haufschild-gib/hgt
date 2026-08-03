import GaloisForLFunctions.HTGeometry.MaximumTermCentralIndex
import GaloisForLFunctions.HTGeometry.TriangleInequalityDefect

/-!
# The entire function of a coefficient sequence, and its logarithmic derivative

The maximum-term theory is about the coefficients.  This file attaches the function: an entire
coefficient sequence has infinite radius of convergence, so its sum is entire, it is differentiated
term by term, and `z f'(z) - k f(z)` is exactly the series of index deviations.  Dividing by `f(z)`
at a point where the function is at least as large as the maximum term turns the coefficient-side
deviation estimate into the Wiman–Valiron bound on the logarithmic derivative.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter

variable {a : ℕ → ℂ} {r s : ℝ}

/-! ## The entire function of a coefficient sequence

Everything above is about the coefficients.  This section attaches the function: an entire
coefficient sequence has infinite radius of convergence, so its sum is an entire function whose
values are dominated by the majorant. -/

/-- An entire coefficient sequence has infinite radius of convergence. -/
theorem ofScalars_radius_eq_top (ha : EntireCoeffs a) :
    (FormalMultilinearSeries.ofScalars ℂ a).radius = ⊤ := by
  refine FormalMultilinearSeries.radius_eq_top_of_summable_norm _ fun r' => ?_
  rcases eq_or_ne r' 0 with hz | hz
  · subst hz
    refine Summable.comp_nat_add (k := 1) ?_
    simp
  · have hpos : 0 < r' := pos_iff_ne_zero.mpr hz
    have hr : (0 : ℝ) < (r' : ℝ) := by exact_mod_cast hpos
    rw [← summable_nat_add_iff 1]
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      ((summable_nat_add_iff 1).mpr (summable_term ha hr))
    exact mul_le_mul_of_nonneg_right
      (FormalMultilinearSeries.ofScalars_norm_le ℂ a (n + 1) (Nat.succ_pos n)) (by positivity)

/-- The entire function determined by an entire coefficient sequence. -/
noncomputable def coeffFun (a : ℕ → ℂ) : ℂ → ℂ := (FormalMultilinearSeries.ofScalars ℂ a).sum

theorem coeffFun_eq_tsum (a : ℕ → ℂ) (z : ℂ) : coeffFun a z = ∑' n : ℕ, a n * z ^ n := by
  have h : coeffFun a z = FormalMultilinearSeries.ofScalarsSum a z := rfl
  rw [h, FormalMultilinearSeries.ofScalars_sum_eq]
  exact tsum_congr fun n => by rw [smul_eq_mul]

/-- **The coefficient sum is entire.** -/
theorem differentiable_coeffFun (ha : EntireCoeffs a) : Differentiable ℂ (coeffFun a) := by
  have hrad := ofScalars_radius_eq_top ha
  have hpos : 0 < (FormalMultilinearSeries.ofScalars ℂ a).radius := by
    rw [hrad]
    simp
  have hball := (FormalMultilinearSeries.ofScalars ℂ a).hasFPowerSeriesOnBall hpos
  intro z
  refine (hball.analyticAt_of_mem ?_).differentiableAt
  rw [hrad]
  simp

/-- The values of the entire function are dominated by the majorant. -/
theorem norm_coeffFun_le (ha : EntireCoeffs a) {z : ℂ} (hz : 0 < ‖z‖) :
    ‖coeffFun a z‖ ≤ coeffSum a ‖z‖ := by
  rw [coeffFun_eq_tsum, coeffSum]
  have hsum : Summable fun n : ℕ => ‖a n * z ^ n‖ := by
    refine (summable_term ha hz).congr fun n => ?_
    rw [norm_mul, norm_pow]
  refine le_trans (norm_tsum_le_tsum_norm hsum) (le_of_eq ?_)
  exact tsum_congr fun n => by rw [norm_mul, norm_pow]


/-- **Termwise differentiation.**  The entire function of a coefficient sequence is differentiated
term by term.  The partial sums are polynomials, and both they and their derivatives converge
uniformly on every ball, so the Weierstrass limit theorem applies. -/
theorem hasDerivAt_coeffFun (ha : EntireCoeffs a) (z : ℂ) :
    HasDerivAt (coeffFun a) (∑' n : ℕ, (n : ℂ) * a n * z ^ (n - 1)) z := by
  classical
  set R : ℝ := ‖z‖ + 1 with hRdef
  have hR0 : (0 : ℝ) < R := by rw [hRdef]; positivity
  have hpow : ∀ n : ℕ, (n : ℝ) * R ^ (n - 1) = (1 / R) * ((n : ℝ) * R ^ n) := by
    intro n
    cases n with
    | zero => simp
    | succ m =>
        simp only [Nat.add_sub_cancel]
        field_simp
        ring
  have hidx : Summable fun n : ℕ => (n : ℝ) * (‖a n‖ * R ^ n) := by
    refine (summable_term (entireCoeffs_mul_index ha) hR0).congr fun n => ?_
    rw [norm_mul, Complex.norm_natCast, mul_assoc]
  have hu' : Summable fun n : ℕ => (1 / R) * ((n : ℝ) * (‖a n‖ * R ^ n)) := hidx.mul_left _
  have hu : Summable fun n : ℕ => ‖a n‖ * R ^ n := summable_term ha hR0
  refine hasDerivAt_of_tendstoLocallyUniformlyOn (l := (atTop : Filter (Finset ℕ)))
    (f := fun t (w : ℂ) => ∑ n ∈ t, a n * w ^ n)
    (f' := fun t (w : ℂ) => ∑ n ∈ t, (n : ℂ) * a n * w ^ (n - 1))
    (g := coeffFun a)
    (g' := fun w : ℂ => ∑' n : ℕ, (n : ℂ) * a n * w ^ (n - 1))
    (s := Metric.ball (0 : ℂ) R) Metric.isOpen_ball ?_ ?_ ?_ (by simp [hRdef])
  · refine TendstoUniformlyOn.tendstoLocallyUniformlyOn ?_
    refine tendstoUniformlyOn_tsum hu' fun n w hw => ?_
    have hwR : ‖w‖ ≤ R := le_of_lt (by simpa using hw)
    calc ‖(n : ℂ) * a n * w ^ (n - 1)‖ = (n : ℝ) * ‖a n‖ * ‖w‖ ^ (n - 1) := by
          rw [norm_mul, norm_mul, Complex.norm_natCast, norm_pow]
      _ ≤ (n : ℝ) * ‖a n‖ * R ^ (n - 1) := by gcongr
      _ = (1 / R) * ((n : ℝ) * (‖a n‖ * R ^ n)) := by
          rw [show (n : ℝ) * ‖a n‖ * R ^ (n - 1) = ‖a n‖ * ((n : ℝ) * R ^ (n - 1)) by ring,
            hpow n]
          ring
  · refine Filter.Eventually.of_forall fun t w _ => ?_
    have hterm : ∀ n : ℕ, HasDerivAt (fun u : ℂ => a n * u ^ n)
        ((n : ℂ) * a n * w ^ (n - 1)) w := by
      intro n
      have h := (hasDerivAt_pow n w).const_mul (a n)
      simpa [mul_comm, mul_left_comm, mul_assoc] using h
    exact HasDerivAt.fun_sum fun n _ => hterm n
  · intro w hw
    have hwR : ‖w‖ ≤ R := le_of_lt (by simpa using hw)
    have hsummable : Summable fun n : ℕ => a n * w ^ n := by
      refine Summable.of_norm (Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hu)
      rw [norm_mul, norm_pow]
      gcongr
    rw [coeffFun_eq_tsum]
    exact hsummable.hasSum

/-! ## The logarithmic derivative

`z f'(z) - k f(z)` is exactly the series of index deviations, so the deviation estimate is a bound on
how far `f'/f` is from `k/z`. -/

private theorem norm_index_sub (n k : ℕ) : ‖(n : ℂ) - (k : ℂ)‖ = |(n : ℝ) - (k : ℝ)| := by
  rw [show ((n : ℂ) - (k : ℂ)) = (((n : ℝ) - (k : ℝ) : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_real, Real.norm_eq_abs]

private theorem norm_deviation_term (a : ℕ → ℂ) (z : ℂ) (n k : ℕ) :
    ‖((n : ℂ) - (k : ℂ)) * a n * z ^ n‖ = |(n : ℝ) - (k : ℝ)| * (‖a n‖ * ‖z‖ ^ n) := by
  rw [norm_mul, norm_mul, norm_pow, norm_index_sub, mul_assoc]

/-- Multiplying the derivative by the coordinate restores the index weight. -/
theorem mul_deriv_coeffFun_eq (ha : EntireCoeffs a) (z : ℂ) :
    z * deriv (coeffFun a) z = ∑' n : ℕ, (n : ℂ) * a n * z ^ n := by
  rw [(hasDerivAt_coeffFun ha z).deriv, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  cases n with
  | zero => simp
  | succ m =>
      simp only [Nat.add_sub_cancel]
      rw [pow_succ]
      ring

/-- **The index-deviation series.**  `z f'(z) - k f(z)` is the series whose terms carry the
deviation of the index from `k`. -/
theorem mul_deriv_sub_eq_tsum (ha : EntireCoeffs a) {z : ℂ} (hz : 0 < ‖z‖) (k : ℕ) :
    z * deriv (coeffFun a) z - (k : ℂ) * coeffFun a z
      = ∑' n : ℕ, ((n : ℂ) - (k : ℂ)) * a n * z ^ n := by
  have hidx : Summable fun n : ℕ => (n : ℂ) * a n * z ^ n := by
    refine Summable.of_norm ((summable_term (entireCoeffs_mul_index ha) hz).congr fun n => ?_)
    rw [norm_mul ((n : ℂ) * a n) (z ^ n), norm_pow]
  have hc : Summable fun n : ℕ => a n * z ^ n := by
    refine Summable.of_norm ((summable_term ha hz).congr fun n => ?_)
    rw [norm_mul, norm_pow]
  rw [mul_deriv_coeffFun_eq ha z, coeffFun_eq_tsum, ← tsum_mul_left,
    ← Summable.tsum_sub hidx (hc.mul_left (k : ℂ))]
  exact tsum_congr fun n => by ring

/-- **The logarithmic-derivative bound.**  The distance from `z f'(z)` to `k f(z)` is at most the
deviation series, which the window decomposition bounds. -/
theorem norm_mul_deriv_sub_le (ha : EntireCoeffs a) {z : ℂ} (hz : 0 < ‖z‖) (k : ℕ) :
    ‖z * deriv (coeffFun a) z - (k : ℂ) * coeffFun a z‖
      ≤ ∑' n : ℕ, |(n : ℝ) - (k : ℝ)| * (‖a n‖ * ‖z‖ ^ n) := by
  rw [mul_deriv_sub_eq_tsum ha hz k]
  have hsum : Summable fun n : ℕ => ‖((n : ℂ) - (k : ℂ)) * a n * z ^ n‖ :=
    (summable_index_deviation ha hz k).congr fun n => (norm_deviation_term a z n k).symm
  refine le_trans (norm_tsum_le_tsum_norm hsum) (le_of_eq (tsum_congr fun n => ?_))
  exact norm_deviation_term a z n k


/-- Each window term is at most the maximum term, so the window sum is at most the window count
times `mu(r)`. -/
theorem sum_window_le_card_mul_maxTerm (ha : EntireCoeffs a) (hr : 0 < r) (m k : ℕ) :
    ∑ n ∈ Finset.Ico m (k + 1), ‖a n‖ * r ^ n ≤ ((k + 1 - m : ℕ) : ℝ) * maxTerm a r := by
  have hcard : (Finset.Ico m (k + 1)).card = k + 1 - m := Nat.card_Ico m (k + 1)
  have hbd : ∀ n ∈ Finset.Ico m (k + 1), ‖a n‖ * r ^ n ≤ maxTerm a r :=
    fun n _ => term_le_maxTerm ha hr n
  have h := Finset.sum_le_card_nsmul _ _ _ hbd
  rw [hcard, nsmul_eq_mul] at h
  exact h

/-- **The deviation estimate as a multiple of the maximum term.**  Bounding the window by its term
count makes every remainder proportional to `mu(r)`, so the constant depends only on the central
indices and the radius ratios. -/
theorem tsum_index_deviation_le_maxTerm
    (ha : EntireCoeffs a) (ht : 0 < t) (htr : t < r) (hrs : r < s)
    {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) :
    ∑' n : ℕ, |(n : ℝ) - (centralIndex a r : ℝ)| * (‖a n‖ * r ^ n)
      ≤ maxTerm a r * (((centralIndex a s : ℝ) - (centralIndex a t : ℝ))
            * ((centralIndex a s + 1 - centralIndex a t : ℕ) : ℝ)
          + (centralIndex a r : ℝ) * ((t / r) / (1 - t / r))
          + ((centralIndex a s : ℝ) + 1)
              * ∑' j : ℕ, ((1 : ℝ) + j) * (r / s) ^ (j + 1)) := by
  have hr : 0 < r := lt_trans ht htr
  refine le_trans (tsum_index_deviation_le_of_window_le ha ht htr hrs hn₀
    (sum_window_le_card_mul_maxTerm ha hr (centralIndex a t) (centralIndex a s))) (le_of_eq ?_)
  ring

/-- **The Wiman--Valiron estimate with a coefficient-free remainder.**  If the deviation series is at
most `mu(r)` times `B`, then at any point of the circle where the function is at least the maximum
term the logarithmic derivative differs from `nu(r)/z` by at most `B`. -/
theorem norm_mul_logDeriv_sub_le_of_deviation_le
    (ha : EntireCoeffs a) (hr : 0 < r) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) {z : ℂ} (hzr : ‖z‖ = r)
    (hf : maxTerm a r ≤ ‖coeffFun a z‖) {B : ℝ}
    (hB : ∑' n : ℕ, |(n : ℝ) - (centralIndex a r : ℝ)| * (‖a n‖ * r ^ n) ≤ maxTerm a r * B) :
    ‖z * deriv (coeffFun a) z / coeffFun a z - (centralIndex a r : ℂ)‖ ≤ B := by
  have hz : 0 < ‖z‖ := by rw [hzr]; exact hr
  obtain ⟨-, -, hμpos⟩ := exists_maxTerm_eq ha hr hn₀
  have hfpos : 0 < ‖coeffFun a z‖ := lt_of_lt_of_le hμpos hf
  have hfne : coeffFun a z ≠ 0 := norm_pos_iff.mp hfpos
  have hdev := norm_mul_deriv_sub_le ha hz (centralIndex a r)
  rw [hzr] at hdev
  have hchain := le_trans hdev hB
  have hBnn : (0 : ℝ) ≤ maxTerm a r * B := le_trans (norm_nonneg _) hchain
  have hsplit : z * deriv (coeffFun a) z / coeffFun a z - (centralIndex a r : ℂ)
      = (z * deriv (coeffFun a) z - (centralIndex a r : ℂ) * coeffFun a z) / coeffFun a z := by
    field_simp
  rw [hsplit, norm_div]
  calc ‖z * deriv (coeffFun a) z - (centralIndex a r : ℂ) * coeffFun a z‖ / ‖coeffFun a z‖
      ≤ (maxTerm a r * B) / ‖coeffFun a z‖ := div_le_div_of_nonneg_right hchain hfpos.le
    _ ≤ (maxTerm a r * B) / maxTerm a r := div_le_div_of_nonneg_left hBnn hμpos hf
    _ = B := by field_simp

/-- **The Wiman--Valiron logarithmic-derivative estimate.**  At a point of the circle of radius `r`
where the function is at least as large as the maximum term, `z f'(z)/f(z)` differs from the central
index by at most the deviation bound divided by the maximum term. -/
theorem norm_mul_logDeriv_sub_centralIndex_le
    (ha : EntireCoeffs a) (ht : 0 < t) (htr : t < r) (hrs : r < s)
    {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) {z : ℂ} (hzr : ‖z‖ = r)
    (hf : maxTerm a r ≤ ‖coeffFun a z‖) :
    ‖z * deriv (coeffFun a) z / coeffFun a z - (centralIndex a r : ℂ)‖
      ≤ (((centralIndex a s : ℝ) - (centralIndex a t : ℝ)) * coeffSum a r
          + (centralIndex a r : ℝ) * (maxTerm a r * (t / r) / (1 - t / r))
          + maxTerm a r * ((centralIndex a s : ℝ) + 1)
              * ∑' j : ℕ, ((1 : ℝ) + j) * (r / s) ^ (j + 1)) / maxTerm a r := by
  have hr : 0 < r := lt_trans ht htr
  have hz : 0 < ‖z‖ := by rw [hzr]; exact hr
  obtain ⟨-, -, hμpos⟩ := exists_maxTerm_eq ha hr hn₀
  have hfpos : 0 < ‖coeffFun a z‖ := lt_of_lt_of_le hμpos hf
  have hfne : coeffFun a z ≠ 0 := norm_pos_iff.mp hfpos
  -- the deviation series, bounded twice
  have hdev := norm_mul_deriv_sub_le ha hz (centralIndex a r)
  rw [hzr] at hdev
  have hbound := tsum_index_deviation_le ha ht htr hrs hn₀
  have hchain : ‖z * deriv (coeffFun a) z - (centralIndex a r : ℂ) * coeffFun a z‖
      ≤ ((centralIndex a s : ℝ) - (centralIndex a t : ℝ)) * coeffSum a r
        + (centralIndex a r : ℝ) * (maxTerm a r * (t / r) / (1 - t / r))
        + maxTerm a r * ((centralIndex a s : ℝ) + 1)
            * ∑' j : ℕ, ((1 : ℝ) + j) * (r / s) ^ (j + 1) := le_trans hdev hbound
  have hBnonneg : (0 : ℝ) ≤ ((centralIndex a s : ℝ) - (centralIndex a t : ℝ)) * coeffSum a r
      + (centralIndex a r : ℝ) * (maxTerm a r * (t / r) / (1 - t / r))
      + maxTerm a r * ((centralIndex a s : ℝ) + 1)
          * ∑' j : ℕ, ((1 : ℝ) + j) * (r / s) ^ (j + 1) :=
    le_trans (norm_nonneg _) hchain
  -- divide
  have hsplit : z * deriv (coeffFun a) z / coeffFun a z - (centralIndex a r : ℂ)
      = (z * deriv (coeffFun a) z - (centralIndex a r : ℂ) * coeffFun a z) / coeffFun a z := by
    field_simp
  rw [hsplit, norm_div]
  calc ‖z * deriv (coeffFun a) z - (centralIndex a r : ℂ) * coeffFun a z‖ / ‖coeffFun a z‖
      ≤ (((centralIndex a s : ℝ) - (centralIndex a t : ℝ)) * coeffSum a r
          + (centralIndex a r : ℝ) * (maxTerm a r * (t / r) / (1 - t / r))
          + maxTerm a r * ((centralIndex a s : ℝ) + 1)
              * ∑' j : ℕ, ((1 : ℝ) + j) * (r / s) ^ (j + 1)) / ‖coeffFun a z‖ := by
        exact div_le_div_of_nonneg_right hchain hfpos.le
    _ ≤ (((centralIndex a s : ℝ) - (centralIndex a t : ℝ)) * coeffSum a r
          + (centralIndex a r : ℝ) * (maxTerm a r * (t / r) / (1 - t / r))
          + maxTerm a r * ((centralIndex a s : ℝ) + 1)
              * ∑' j : ℕ, ((1 : ℝ) + j) * (r / s) ^ (j + 1)) / maxTerm a r :=
        div_le_div_of_nonneg_left hBnonneg hμpos hf


/-! ## The central factorisation

On a circle of radius `r` the function is its central term times a series whose coefficients all
have modulus at most one.  This is the normalised form in which the local expansion is carried
out. -/

/-- **Central factorisation.**  `f(z) = a_nu z^nu * sum_n b_n` with `||b_n|| <= 1` and `b_nu = 1`. -/
theorem coeffFun_eq_central_term_mul_tsum
    (ha : EntireCoeffs a) (hr : 0 < r) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) {z : ℂ} (hz : ‖z‖ = r) :
    coeffFun a z
      = (a (centralIndex a r) * z ^ centralIndex a r)
        * ∑' n : ℕ, a n * z ^ n / (a (centralIndex a r) * z ^ centralIndex a r) := by
  have hc := central_term_ne_zero ha hr hn₀ hz
  rw [coeffFun_eq_tsum, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  have hcancel : a (centralIndex a r) * z ^ centralIndex a r
      * (a n * z ^ n / (a (centralIndex a r) * z ^ centralIndex a r)) = a n * z ^ n := by
    rw [mul_comm, div_mul_cancel₀ _ hc]
  exact hcancel.symm


/-! ## Scaling the normalised series

Moving off the circle multiplies the `n`-th normalised coefficient by `zeta^(n-k)`.  The local
expansion of Wiman--Valiron is exactly this series in the variable `zeta`, with all coefficients in
the closed unit disc and the `k`-th equal to one. -/

/-- Factorisation at an arbitrary index with a nonzero coefficient. -/
theorem coeffFun_eq_term_mul_tsum {k : ℕ} (hak : a k ≠ 0)
    {z : ℂ} (hz : z ≠ 0) :
    coeffFun a z = (a k * z ^ k) * ∑' n : ℕ, a n * z ^ n / (a k * z ^ k) := by
  have hc : a k * z ^ k ≠ 0 := mul_ne_zero hak (pow_ne_zero _ hz)
  rw [coeffFun_eq_tsum, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  have hcancel : a k * z ^ k * (a n * z ^ n / (a k * z ^ k)) = a n * z ^ n := by
    rw [mul_comm, div_mul_cancel₀ _ hc]
  exact hcancel.symm

/-- **The scaling law for normalised coefficients.**  Scaling the coordinate by `zeta` multiplies the
`n`-th normalised coefficient by `zeta^(n-k)`. -/
theorem normalised_coeff_scale (a : ℕ → ℂ) (k n : ℕ) {z ζ : ℂ} (hz : z ≠ 0) (hζ : ζ ≠ 0)
    (hak : a k ≠ 0) :
    a n * (ζ * z) ^ n / (a k * (ζ * z) ^ k)
      = (a n * z ^ n / (a k * z ^ k)) * ζ ^ ((n : ℤ) - (k : ℤ)) := by
  have hzn : (z : ℂ) ^ n ≠ 0 := pow_ne_zero _ hz
  have hzk : (z : ℂ) ^ k ≠ 0 := pow_ne_zero _ hz
  have hζn : (ζ : ℂ) ^ n ≠ 0 := pow_ne_zero _ hζ
  have hζk : (ζ : ℂ) ^ k ≠ 0 := pow_ne_zero _ hζ
  rw [mul_pow, mul_pow, zpow_sub₀ hζ, zpow_natCast, zpow_natCast]
  field_simp

/-- **The local expansion.**  Off the circle the function is the `k`-th term times the normalised
series in the scaling variable. -/
theorem coeffFun_scale_eq_tsum {k : ℕ} (hak : a k ≠ 0)
    {z ζ : ℂ} (hz : z ≠ 0) (hζ : ζ ≠ 0) :
    coeffFun a (ζ * z)
      = (a k * (ζ * z) ^ k)
        * ∑' n : ℕ, (a n * z ^ n / (a k * z ^ k)) * ζ ^ ((n : ℤ) - (k : ℤ)) := by
  have hzζ : ζ * z ≠ 0 := mul_ne_zero hζ hz
  rw [coeffFun_eq_term_mul_tsum hak hzζ]
  congr 1
  exact tsum_congr fun n => normalised_coeff_scale a k n hz hζ hak


/-! ## The defect of the normalised family

Applying the alignment identity to the normalised coefficients converts the gap between the majorant
and the actual value of the function into the total misalignment of the phases.  At a
maximum-modulus point that gap is as small as the circle allows. -/

/-- **The normalised defect.**  The total misalignment of the normalised coefficients is exactly the
gap between the majorant and the modulus of the value, measured in units of the maximum term. -/
theorem exists_unit_tsum_normalised_alignment_defect
    (ha : EntireCoeffs a) (hr : 0 < r) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) {z : ℂ} (hz : ‖z‖ = r)
    (hfz : coeffFun a z ≠ 0) :
    ∃ u : ℂ, ‖u‖ = 1 ∧
      ∑' n : ℕ,
          (‖a n * z ^ n / (a (centralIndex a r) * z ^ centralIndex a r)‖
            - ((starRingEnd ℂ) u
                * (a n * z ^ n / (a (centralIndex a r) * z ^ centralIndex a r))).re)
        = (coeffSum a r - ‖coeffFun a z‖) / maxTerm a r := by
  have hzne : z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hz
    exact absurd hz.symm (ne_of_gt hr)
  set C : ℂ := a (centralIndex a r) * z ^ centralIndex a r with hC
  have hCne : C ≠ 0 := central_term_ne_zero ha hr hn₀ hz
  have hCnorm : ‖C‖ = maxTerm a r := by
    rw [hC, norm_mul, norm_pow, hz]
    exact term_centralIndex_eq ha hr hn₀
  set c : ℕ → ℂ := fun n => a n * z ^ n / C with hc
  have hcnorm : ∀ n, ‖c n‖ = (‖a n‖ * r ^ n) / maxTerm a r := by
    intro n
    rw [hc, norm_div, hCnorm, norm_mul, norm_pow, hz]
  have hnsum : Summable fun n => ‖c n‖ := by
    refine ((summable_term ha hr).div_const (maxTerm a r)).congr fun n => ?_
    rw [hcnorm n]
  have hcsum : Summable c := Summable.of_norm hnsum
  have htsum_norm : ∑' n : ℕ, ‖c n‖ = coeffSum a r / maxTerm a r := by
    rw [coeffSum, ← tsum_div_const]
    exact tsum_congr fun n => hcnorm n
  have hfac : coeffFun a z = C * ∑' n : ℕ, c n := coeffFun_eq_term_mul_tsum
    (coeff_centralIndex_ne_zero ha hr hn₀) hzne
  set W : ℂ := ∑' n : ℕ, c n with hW
  have hWne : W ≠ 0 := by
    intro h
    rw [h, mul_zero] at hfac
    exact hfz hfac
  obtain ⟨-, -, hμpos⟩ := exists_maxTerm_eq ha hr hn₀
  have hWnorm : ‖W‖ = ‖coeffFun a z‖ / maxTerm a r := by
    rw [hfac, norm_mul, hCnorm]
    field_simp [ne_of_gt hμpos]
  refine ⟨W / (‖W‖ : ℂ), ?_, ?_⟩
  · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg W)]
    exact div_self (norm_ne_zero_iff.mpr hWne)
  · have hunit : ‖W / (‖W‖ : ℂ)‖ = 1 := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg W)]
      exact div_self (norm_ne_zero_iff.mpr hWne)
    have hWn : ((‖W‖ : ℝ) : ℂ) ≠ 0 := by
      simpa using norm_ne_zero_iff.mpr hWne
    have hsplit : W = ((‖W‖ : ℝ) : ℂ) * (W / (‖W‖ : ℂ)) := by
      rw [mul_comm, div_mul_cancel₀ _ hWn]
    have hdef := tsum_alignment_defect c hcsum hnsum hunit hsplit
    rw [hdef, htsum_norm, hWnorm]
    ring


/-- **The defect is bounded by the central index.**  At a point where the function is at least the
maximum term, the total misalignment is at most `nu(s)` plus a constant fixed by the radius ratio. -/
theorem exists_unit_tsum_normalised_defect_le
    (ha : EntireCoeffs a) (hr : 0 < r) (hrs : r < s) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0)
    {z : ℂ} (hz : ‖z‖ = r) (hfz : maxTerm a r ≤ ‖coeffFun a z‖) :
    ∃ u : ℂ, ‖u‖ = 1 ∧
      ∑' n : ℕ,
          (‖a n * z ^ n / (a (centralIndex a r) * z ^ centralIndex a r)‖
            - ((starRingEnd ℂ) u
                * (a n * z ^ n / (a (centralIndex a r) * z ^ centralIndex a r))).re)
        ≤ (centralIndex a s : ℝ) + (r / s) / (1 - r / s) := by
  obtain ⟨-, -, hμpos⟩ := exists_maxTerm_eq ha hr hn₀
  have hfzne : coeffFun a z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hfz
    exact absurd (lt_of_lt_of_le hμpos hfz) (lt_irrefl 0)
  obtain ⟨u, hu, hdef⟩ :=
    exists_unit_tsum_normalised_alignment_defect ha hr hn₀ hz hfzne
  refine ⟨u, hu, ?_⟩
  rw [hdef, div_le_iff₀ hμpos]
  have hS := coeffSum_le_maxTerm_mul_centralIndex ha hr hrs hn₀
  nlinarith [hS, hfz, hμpos]

/-- **The transverse component at a maximum-modulus point.**  Every normalised coefficient lies
within `sqrt(2 D)` of a nonnegative multiple of the common direction, where `D` bounds the total
misalignment. -/
theorem norm_normalised_transverse_sq_le
    (ha : EntireCoeffs a) (hr : 0 < r) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) {z : ℂ} (hz : ‖z‖ = r)
    {u : ℂ} (hu : ‖u‖ = 1) {D : ℝ}
    (hD : ∑' n : ℕ,
        (‖a n * z ^ n / (a (centralIndex a r) * z ^ centralIndex a r)‖
          - ((starRingEnd ℂ) u
              * (a n * z ^ n / (a (centralIndex a r) * z ^ centralIndex a r))).re) ≤ D)
    (n : ℕ) :
    ‖a n * z ^ n / (a (centralIndex a r) * z ^ centralIndex a r)
        - (((((starRingEnd ℂ) u
              * (a n * z ^ n / (a (centralIndex a r) * z ^ centralIndex a r))).re) : ℝ) : ℂ) * u‖ ^ 2
      ≤ 2 * D := by
  set C : ℂ := a (centralIndex a r) * z ^ centralIndex a r with hC
  have hCne : C ≠ 0 := central_term_ne_zero ha hr hn₀ hz
  have hCnorm : ‖C‖ = maxTerm a r := by
    rw [hC, norm_mul, norm_pow, hz]
    exact term_centralIndex_eq ha hr hn₀
  set c : ℕ → ℂ := fun n => a n * z ^ n / C with hc
  have hcnorm : ∀ m, ‖c m‖ = (‖a m‖ * r ^ m) / maxTerm a r := by
    intro m
    rw [hc, norm_div, hCnorm, norm_mul, norm_pow, hz]
  have hnsum : Summable fun m => ‖c m‖ := by
    refine ((summable_term ha hr).div_const (maxTerm a r)).congr fun m => ?_
    rw [hcnorm m]
  have hcsum : Summable c := Summable.of_norm hnsum
  have hd : Summable fun m => ‖c m‖ - ((starRingEnd ℂ) u * c m).re :=
    hnsum.sub (Complex.reCLM.summable (hcsum.mul_left _))
  have hterm : ‖c n‖ - ((starRingEnd ℂ) u * c n).re ≤ D :=
    le_trans (hd.le_tsum n fun m _ => alignment_defect_nonneg (c m) hu) hD
  have hle1 : ‖c n‖ ≤ 1 := norm_normalised_coeff_le_one ha hr hn₀ hz n
  have hsq := norm_sub_re_mul_sq_le (c n) hu
  have hnn : (0 : ℝ) ≤ ‖c n‖ - ((starRingEnd ℂ) u * c n).re := alignment_defect_nonneg (c n) hu
  nlinarith [hsq, hterm, hle1, hnn]


/-- The coefficients normalised by the central term. -/
noncomputable def normalisedCoeff (a : ℕ → ℂ) (r : ℝ) (z : ℂ) (n : ℕ) : ℂ :=
  a n * z ^ n / (a (centralIndex a r) * z ^ centralIndex a r)

theorem normalisedCoeff_def (a : ℕ → ℂ) (r : ℝ) (z : ℂ) (n : ℕ) :
    normalisedCoeff a r z n
      = a n * z ^ n / (a (centralIndex a r) * z ^ centralIndex a r) := rfl

/-- **The weighted window sum.**  Over any finite window the weighted sum of the normalised
coefficients differs from a real multiple of the common direction by at most
`sqrt 2 * sqrt (sum of squared weights) * sqrt (total misalignment)`.  The weights enter only through
their `l^2` norm, which is the gain over bounding each term by its modulus. -/
theorem norm_weighted_window_sub_le
    (ha : EntireCoeffs a) (hr : 0 < r) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) {z : ℂ} (hz : ‖z‖ = r)
    {u : ℂ} (hu : ‖u‖ = 1) {D : ℝ}
    (hD : ∑' n : ℕ,
        (‖normalisedCoeff a r z n‖
          - ((starRingEnd ℂ) u * normalisedCoeff a r z n).re) ≤ D)
    (F : Finset ℕ) (w : ℕ → ℝ) :
    ‖(∑ n ∈ F, (w n : ℂ) * normalisedCoeff a r z n)
        - ((∑ n ∈ F, w n * ((starRingEnd ℂ) u * normalisedCoeff a r z n).re : ℝ) : ℂ) * u‖
      ≤ Real.sqrt 2 * Real.sqrt (∑ n ∈ F, w n ^ 2) * Real.sqrt D := by
  set c : ℕ → ℂ := normalisedCoeff a r z with hc
  set d : ℕ → ℝ := fun n => ‖c n‖ - ((starRingEnd ℂ) u * c n).re with hd
  have hdnn : ∀ n, 0 ≤ d n := fun n => alignment_defect_nonneg (c n) hu
  -- the per-term transverse bound
  have hpt : ∀ n : ℕ,
      ‖c n - ((((starRingEnd ℂ) u * c n).re : ℝ) : ℂ) * u‖ ≤ Real.sqrt 2 * Real.sqrt (d n) := by
    intro n
    have hsq := norm_sub_re_mul_sq_le (c n) hu
    have hle1 : ‖c n‖ ≤ 1 := norm_normalised_coeff_le_one ha hr hn₀ hz n
    have hbound : ‖c n - ((((starRingEnd ℂ) u * c n).re : ℝ) : ℂ) * u‖ ^ 2 ≤ 2 * d n := by
      have := hdnn n
      nlinarith [hsq, hle1, this]
    have hsqrt : Real.sqrt 2 * Real.sqrt (d n) = Real.sqrt (2 * d n) :=
      (Real.sqrt_mul (by norm_num) _).symm
    rw [hsqrt]
    exact Real.le_sqrt_of_sq_le hbound
  -- aggregate
  have hstep := norm_weighted_sum_sub_le F c w u
  have hsum : ∑ n ∈ F, |w n| * ‖c n - ((((starRingEnd ℂ) u * c n).re : ℝ) : ℂ) * u‖
      ≤ ∑ n ∈ F, |w n| * (Real.sqrt 2 * Real.sqrt (d n)) :=
    Finset.sum_le_sum fun n _ => mul_le_mul_of_nonneg_left (hpt n) (abs_nonneg _)
  have hfactor : ∑ n ∈ F, |w n| * (Real.sqrt 2 * Real.sqrt (d n))
      = Real.sqrt 2 * ∑ n ∈ F, |w n| * Real.sqrt (d n) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => by ring
  -- Cauchy--Schwarz
  have hcs := sum_weighted_sqrt_sq_le F (fun n => |w n|) d (fun n _ => hdnn n)
  have hdF : ∑ n ∈ F, d n ≤ D := by
    have hdsum : Summable d := by
      have hnsum : Summable fun m => ‖c m‖ := by
        have hCnorm : ‖a (centralIndex a r) * z ^ centralIndex a r‖ = maxTerm a r := by
          rw [norm_mul, norm_pow, hz]
          exact term_centralIndex_eq ha hr hn₀
        refine ((summable_term ha hr).div_const (maxTerm a r)).congr fun m => ?_
        rw [hc, normalisedCoeff_def, norm_div, hCnorm, norm_mul, norm_pow, hz]
      exact hnsum.sub (Complex.reCLM.summable ((Summable.of_norm hnsum).mul_left _))
    exact le_trans (hdsum.sum_le_tsum F fun n _ => hdnn n) hD
  have hCS : ∑ n ∈ F, |w n| * Real.sqrt (d n)
      ≤ Real.sqrt (∑ n ∈ F, w n ^ 2) * Real.sqrt D := by
    have habs : ∑ n ∈ F, |w n| ^ 2 = ∑ n ∈ F, w n ^ 2 :=
      Finset.sum_congr rfl fun n _ => sq_abs (w n)
    rw [habs] at hcs
    have hnn : (0 : ℝ) ≤ ∑ n ∈ F, |w n| * Real.sqrt (d n) :=
      Finset.sum_nonneg fun n _ => mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
    have hprod : (∑ n ∈ F, |w n| * Real.sqrt (d n)) ^ 2
        ≤ (∑ n ∈ F, w n ^ 2) * D := by
      refine le_trans hcs (mul_le_mul_of_nonneg_left hdF ?_)
      exact Finset.sum_nonneg fun n _ => sq_nonneg (w n)
    have hsqrt : Real.sqrt ((∑ n ∈ F, w n ^ 2) * D)
        = Real.sqrt (∑ n ∈ F, w n ^ 2) * Real.sqrt D :=
      Real.sqrt_mul (Finset.sum_nonneg fun n _ => sq_nonneg (w n)) D
    rw [← hsqrt]
    exact Real.le_sqrt_of_sq_le hprod
  calc ‖(∑ n ∈ F, (w n : ℂ) * c n)
        - ((∑ n ∈ F, w n * ((starRingEnd ℂ) u * c n).re : ℝ) : ℂ) * u‖
      ≤ ∑ n ∈ F, |w n| * ‖c n - ((((starRingEnd ℂ) u * c n).re : ℝ) : ℂ) * u‖ := hstep
    _ ≤ Real.sqrt 2 * ∑ n ∈ F, |w n| * Real.sqrt (d n) := by
        rw [← hfactor]; exact hsum
    _ ≤ Real.sqrt 2 * (Real.sqrt (∑ n ∈ F, w n ^ 2) * Real.sqrt D) :=
        mul_le_mul_of_nonneg_left hCS (Real.sqrt_nonneg 2)
    _ = Real.sqrt 2 * Real.sqrt (∑ n ∈ F, w n ^ 2) * Real.sqrt D := by ring


end GaloisForLFunctions.HTGeometry
