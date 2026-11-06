import GaloisForLFunctions.SquareRootThreshold.EffectiveHorizons.HausdorffSaddle

/-!
# Decay of the real Hausdorff saddle profile

The normalized atom is bounded by `exp (-p Φ(t))`, where
`Φ(t) = 2 log t + t⁻² - 1`. The inequality `log t ≥ 1 - 1/t`
gives Gaussian decay on bounded relative intervals. Beyond four times
the saddle height, the same profile has a power tail.
-/

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold.HausdorffSaddle

/-- The real rate function for the reciprocal-square saddle. -/
def decayRate (t : ℝ) : ℝ := 2 * Real.log t + t⁻¹ ^ 2 - 1

/-- Convexity of the logarithm after inversion bounds the rate from below. -/
theorem quadratic_le_decayRate {t : ℝ} (ht : 0 < t) :
    (t - 1) ^ 2 / t ^ 2 ≤ decayRate t := by
  have heq : (t - 1) ^ 2 / t ^ 2 = (1 - t⁻¹) ^ 2 := by
    field_simp [ht.ne']
  rw [heq, decayRate]
  nlinarith only [Real.one_sub_inv_le_log_of_pos ht]

/-- On a bounded relative interval the rate is Gaussian. -/
theorem quadratic_sixteenth_le_decayRate {t : ℝ} (ht : 0 < t) (ht4 : t ≤ 4) :
    (t - 1) ^ 2 / 16 ≤ decayRate t := by
  have ht2 : t ^ 2 ≤ 16 := by nlinarith only [ht, ht4]
  exact (div_le_div_of_nonneg_left (sq_nonneg _) (sq_pos_of_pos ht) ht2).trans
    (quadratic_le_decayRate ht)

/-- The far tail has at least one logarithmic power of decay per order. -/
theorem log_le_decayRate {t : ℝ} (ht : 4 ≤ t) : Real.log t ≤ decayRate t := by
  have hlog2 := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  have hlog4 : 1 ≤ Real.log 4 := by
    have heq : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    rw [heq]
    norm_num at hlog2
    linarith only [hlog2]
  have hlog : 1 ≤ Real.log t := hlog4.trans (Real.log_le_log (by norm_num) ht)
  unfold decayRate
  linarith only [hlog, sq_nonneg t⁻¹]

/-- The saddle's real atom is strictly positive. -/
theorem realKernel_saddle_pos {R s : ℝ} {p r : ℕ} (hs : 0 < s) (hp : 0 < p)
    (hr : 0 < r) (hbalance : (p : ℝ) * (R * s ^ 2 - 1) = r) :
    0 < realKernel R p r s := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  have hfac : R - s⁻¹ ^ 2 = (r : ℝ) / ((p : ℝ) * s ^ 2) := by
    field_simp [hs.ne', hpR.ne']
    nlinarith only [hbalance]
  unfold realKernel
  rw [hfac]
  positivity

/-- The algebraic normalization remains valid on the whole real axis. -/
theorem realKernel_normalization {R s : ℝ} {p r : ℕ} (hs : s ≠ 0) (hr : 0 < r)
    (hbalance : (p : ℝ) * (R * s ^ 2 - 1) = r) (t : ℝ) :
    realKernel R p r (s * t) = realKernel R p r s *
      ((t⁻¹ ^ 2) ^ p * (1 + ((p : ℝ) / (r : ℝ)) * (1 - t⁻¹ ^ 2)) ^ r) := by
  have h := kernel_normalization hs hr hbalance ((t : ℂ) - 1)
  have heq : 1 + ((t : ℂ) - 1) = (t : ℂ) := by ring
  simp only [reciprocalDisplacement, heq] at h
  apply Complex.ofReal_inj.mp
  simpa only [kernel, realKernel, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_inv, Complex.ofReal_one] using h

/-- The complementary factor is positive throughout the tail interval. -/
theorem profile_complement_pos {p r : ℕ} (hr : 0 < r) (hpr : 200 * (p : ℝ) ≤ r)
    {t : ℝ} (ht : 1 / 4 ≤ t) :
    0 < 1 + ((p : ℝ) / (r : ℝ)) * (1 - t⁻¹ ^ 2) := by
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  have ht0 : 0 < t := by linarith only [ht]
  have ha0 : 0 ≤ (p : ℝ) / (r : ℝ) := by positivity
  have ha : (p : ℝ) / (r : ℝ) ≤ 1 / 200 := by
    rw [div_le_iff₀ hrR]
    linarith only [hpr]
  have hinv : t⁻¹ ≤ 4 := by
    rw [inv_le_comm₀ ht0 (by norm_num)]
    norm_num
    exact ht
  have hinv0 : 0 ≤ t⁻¹ := (inv_pos.mpr ht0).le
  have hsquare : t⁻¹ ^ 2 - 1 ≤ 15 := by nlinarith only [hinv, hinv0]
  have h := mul_le_mul_of_nonneg_left hsquare ha0
  nlinarith only [h, ha]

/-- The scalar product is bounded by the exponential rate without a remainder. -/
theorem normalized_profile_le {p r : ℕ} (hr : 0 < r) {t : ℝ} (ht : 0 < t)
    (hcomp : 0 < 1 + ((p : ℝ) / (r : ℝ)) * (1 - t⁻¹ ^ 2)) :
    (t⁻¹ ^ 2) ^ p * (1 + ((p : ℝ) / (r : ℝ)) * (1 - t⁻¹ ^ 2)) ^ r ≤
      Real.exp (-(p : ℝ) * decayRate t) := by
  let q := 1 + ((p : ℝ) / (r : ℝ)) * (1 - t⁻¹ ^ 2)
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  have hexp : Real.exp (-2 * (p : ℝ) * Real.log t + (r : ℝ) * Real.log q) =
      (t⁻¹ ^ 2) ^ p * q ^ r := by
    have heq : -2 * (p : ℝ) * Real.log t = -(((2 * p : ℕ) : ℝ) * Real.log t) := by
      push_cast
      ring
    rw [Real.exp_add, heq, Real.exp_neg, Real.exp_nat_mul, Real.exp_log ht,
      Real.exp_nat_mul, Real.exp_log hcomp, ← inv_pow, pow_mul]
  have hlog := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hcomp) hrR.le
  have hlinear : (r : ℝ) * (q - 1) = (p : ℝ) * (1 - t⁻¹ ^ 2) := by
    dsimp [q]
    field_simp [hrR.ne']
    ring
  change (r : ℝ) * Real.log q ≤ (r : ℝ) * (q - 1) at hlog
  rw [hlinear] at hlog
  change (t⁻¹ ^ 2) ^ p * q ^ r ≤ _
  rw [← hexp]
  apply Real.exp_le_exp.mpr
  unfold decayRate
  linarith only [hlog]

/-- The whole real atom is controlled by its saddle value and the rate function. -/
theorem realKernel_mul_le_saddle_exp {R s : ℝ} {p r : ℕ} (hs : 0 < s) (hp : 0 < p)
    (hr : 0 < r) (hbalance : (p : ℝ) * (R * s ^ 2 - 1) = r)
    (hpr : 200 * (p : ℝ) ≤ r) {t : ℝ} (ht : 1 / 4 ≤ t) :
    realKernel R p r (s * t) ≤ realKernel R p r s * Real.exp (-(p : ℝ) * decayRate t) := by
  rw [realKernel_normalization hs.ne' hr hbalance]
  exact mul_le_mul_of_nonneg_left
    (normalized_profile_le hr (by linarith only [ht]) (profile_complement_pos hr hpr ht))
    (realKernel_saddle_pos hs hp hr hbalance).le

/-- Gaussian domination through four times the saddle height. -/
theorem realKernel_mul_le_saddle_gaussian {R s : ℝ} {p r : ℕ} (hs : 0 < s) (hp : 0 < p)
    (hr : 0 < r) (hbalance : (p : ℝ) * (R * s ^ 2 - 1) = r)
    (hpr : 200 * (p : ℝ) ≤ r) {t : ℝ} (ht : 1 / 4 ≤ t) (ht4 : t ≤ 4) :
    realKernel R p r (s * t) ≤
      realKernel R p r s * Real.exp (-(p : ℝ) * (t - 1) ^ 2 / 16) := by
  refine (realKernel_mul_le_saddle_exp hs hp hr hbalance hpr ht).trans ?_
  apply mul_le_mul_of_nonneg_left _ (realKernel_saddle_pos hs hp hr hbalance).le
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left
    (quadratic_sixteenth_le_decayRate (by linarith only [ht]) ht4) (Nat.cast_nonneg p)
  linarith only [h]

/-- Beyond four saddle heights the profile has an integrable power tail. -/
theorem realKernel_mul_le_saddle_inv_pow {R s : ℝ} {p r : ℕ} (hs : 0 < s) (hp : 0 < p)
    (hr : 0 < r) (hbalance : (p : ℝ) * (R * s ^ 2 - 1) = r)
    (hpr : 200 * (p : ℝ) ≤ r) {t : ℝ} (ht : 4 ≤ t) :
    realKernel R p r (s * t) ≤ realKernel R p r s * t⁻¹ ^ p := by
  have ht0 : 0 < t := by linarith only [ht]
  refine (realKernel_mul_le_saddle_exp hs hp hr hbalance hpr (by linarith only [ht])).trans ?_
  have heq : Real.exp (-(p : ℝ) * Real.log t) = t⁻¹ ^ p := by
    rw [neg_mul, Real.exp_neg, Real.exp_nat_mul, Real.exp_log ht0, inv_pow]
  rw [← heq]
  apply mul_le_mul_of_nonneg_left _ (realKernel_saddle_pos hs hp hr hbalance).le
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left (log_le_decayRate ht) (Nat.cast_nonneg p)
  linarith only [h]

end GaloisForLFunctions.SquareRootThreshold.HausdorffSaddle
