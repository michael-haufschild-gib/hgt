import GaloisForLFunctions.RHTower.XiReciprocalSquareSecondMomentRadius
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# A uniform remainder bound for the actual LI Euler mass series

The reciprocal-square source radius bounds all centered moments without a sign
assumption. Two discrete quadratic envelopes turn the tail beyond the first two
mass terms into one geometric series. The estimate retains the complete tail and
is uniform in the Euler-jet order through the scale `3^k v`.
-/

namespace RHTower

noncomputable section

/-- The normalized mass-series tail beyond the first two actual source moments. -/
def liEvenCrossEulerNormalizedMassTail (v : ℝ) (k : ℕ) : ℝ :=
  ∑' n : ℕ, (-1 : ℝ) ^ (n + 2) * ((n + 3 : ℕ) : ℝ) ^ (2 * k + 2) *
    normalizedPrimeArchMoment (n + 2) * v ^ (n + 2)

private theorem eulerTail_quadratic_three_envelope (n : ℕ) :
    ((n + 3 : ℕ) : ℝ) ^ 2 ≤ (3 : ℝ) ^ (n + 2) := by
  induction n with
  | zero => norm_num
  | succ n hn =>
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hstep : ((n : ℝ) + 4) ^ 2 ≤ 3 * ((n : ℝ) + 3) ^ 2 := by
      nlinarith [sq_nonneg (n : ℝ)]
    calc
      (((n + 1) + 3 : ℕ) : ℝ) ^ 2 = ((n : ℝ) + 4) ^ 2 := by push_cast; ring
      _ ≤ 3 * ((n : ℝ) + 3) ^ 2 := hstep
      _ ≤ 3 * (3 : ℝ) ^ (n + 2) := by
        simpa only [Nat.cast_add, Nat.cast_ofNat] using
          (mul_le_mul_of_nonneg_left hn (by norm_num : (0 : ℝ) ≤ 3))
      _ = (3 : ℝ) ^ ((n + 1) + 2) := by rw [show (n + 1) + 2 = (n + 2) + 1 by omega, pow_succ]; ring

private theorem eulerTail_quadratic_four_envelope (n : ℕ) :
    ((n + 3 : ℕ) : ℝ) ^ 2 ≤ 9 * (4 : ℝ) ^ n := by
  induction n with
  | zero => norm_num
  | succ n hn =>
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hstep : ((n : ℝ) + 4) ^ 2 ≤ 4 * ((n : ℝ) + 3) ^ 2 := by
      nlinarith [sq_nonneg (n : ℝ)]
    calc
      (((n + 1) + 3 : ℕ) : ℝ) ^ 2 = ((n : ℝ) + 4) ^ 2 := by push_cast; ring
      _ ≤ 4 * ((n : ℝ) + 3) ^ 2 := hstep
      _ ≤ 4 * (9 * (4 : ℝ) ^ n) := by
        simpa only [Nat.cast_add, Nat.cast_ofNat] using
          (mul_le_mul_of_nonneg_left hn (by norm_num : (0 : ℝ) ≤ 4))
      _ = 9 * (4 : ℝ) ^ (n + 1) := by rw [pow_succ]; ring

private theorem eulerTail_term_geometric_bound {v : ℝ} (hv : 0 ≤ v)
    (k n : ℕ) :
    |(-1 : ℝ) ^ (n + 2) * ((n + 3 : ℕ) : ℝ) ^ (2 * k + 2) *
        normalizedPrimeArchMoment (n + 2) * v ^ (n + 2)| ≤
      9 * xiShiftAbsoluteMass 0 * ((3 : ℝ) ^ k * v / 150) ^ 2 *
        (4 * ((3 : ℝ) ^ k * v / 150)) ^ n := by
  let r : ℝ := (n + 3 : ℕ)
  let q : ℝ := (3 : ℝ) ^ k * v / 150
  have hr : 0 ≤ r := by positivity
  have hq : 0 ≤ q := by positivity
  have hm := abs_normalizedPrimeArchMoment_add_le_secondMomentRadius 0 (n + 2)
  simp only [zero_add] at hm
  have hk : (r ^ 2) ^ k ≤ ((3 : ℝ) ^ (n + 2)) ^ k :=
    pow_le_pow_left₀ (sq_nonneg r) (eulerTail_quadratic_three_envelope n) k
  have hA : 0 ≤ xiShiftAbsoluteMass 0 := xiShiftAbsoluteMass_nonneg 0
  have hterm : |(-1 : ℝ) ^ (n + 2) * r ^ (2 * k + 2) *
      normalizedPrimeArchMoment (n + 2) * v ^ (n + 2)| =
      r ^ (2 * k + 2) * |normalizedPrimeArchMoment (n + 2)| * v ^ (n + 2) := by
    simp [abs_mul, abs_pow, abs_of_nonneg hr, abs_of_nonneg hv]
  rw [hterm]
  calc
    r ^ (2 * k + 2) * |normalizedPrimeArchMoment (n + 2)| * v ^ (n + 2) ≤
        r ^ (2 * k + 2) * ((1 / 150 : ℝ) ^ (n + 2) * xiShiftAbsoluteMass 0) *
          v ^ (n + 2) := by gcongr
    _ = r ^ 2 * (r ^ 2) ^ k * ((1 / 150 : ℝ) ^ (n + 2) * xiShiftAbsoluteMass 0) *
          v ^ (n + 2) := by rw [pow_add, pow_mul]; ring
    _ ≤ r ^ 2 * ((3 : ℝ) ^ (n + 2)) ^ k *
          ((1 / 150 : ℝ) ^ (n + 2) * xiShiftAbsoluteMass 0) * v ^ (n + 2) := by gcongr
    _ = r ^ 2 * xiShiftAbsoluteMass 0 * q ^ (n + 2) := by
      dsimp [q]
      rw [← pow_mul, Nat.mul_comm (n + 2) k, pow_mul]
      simp only [div_eq_mul_inv, mul_pow, one_pow]
      ring
    _ ≤ (9 * (4 : ℝ) ^ n) * xiShiftAbsoluteMass 0 * q ^ (n + 2) := by
      gcongr
      exact eulerTail_quadratic_four_envelope n
    _ = 9 * xiShiftAbsoluteMass 0 * q ^ 2 * (4 * q) ^ n := by
      rw [pow_add, mul_pow]
      ring

/-- All higher source moments are controlled uniformly through the scale `3^k v`. -/
theorem abs_liEvenCrossEulerNormalizedMassTail_le
    {v : ℝ} (hv : 0 ≤ v) (k : ℕ)
    (hq : (3 : ℝ) ^ k * v / 150 ≤ 1 / 8) :
    |liEvenCrossEulerNormalizedMassTail v k| ≤
      18 * xiShiftAbsoluteMass 0 * ((3 : ℝ) ^ k * v / 150) ^ 2 := by
  let q : ℝ := (3 : ℝ) ^ k * v / 150
  let B : ℝ := 9 * xiShiftAbsoluteMass 0 * q ^ 2
  let f : ℕ → ℝ := fun n => (-1 : ℝ) ^ (n + 2) *
    ((n + 3 : ℕ) : ℝ) ^ (2 * k + 2) * normalizedPrimeArchMoment (n + 2) * v ^ (n + 2)
  have hq0 : 0 ≤ q := by positivity
  have hq8 : q ≤ 1 / 8 := hq
  have hA : 0 ≤ xiShiftAbsoluteMass 0 := xiShiftAbsoluteMass_nonneg 0
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hratio : 4 * q < 1 := by linarith
  have hg : Summable (fun n : ℕ => B * (4 * q) ^ n) :=
    (summable_geometric_of_lt_one (by positivity) hratio).mul_left B
  have hbound : ∀ n, ‖f n‖ ≤ B * (4 * q) ^ n := by
    intro n
    simpa only [f, B, q, Real.norm_eq_abs] using eulerTail_term_geometric_bound hv k n
  have hf : Summable f := hg.of_norm_bounded hbound
  calc
    |liEvenCrossEulerNormalizedMassTail v k| = ‖∑' n, f n‖ := by
      simp only [liEvenCrossEulerNormalizedMassTail, f, Real.norm_eq_abs]
    _ ≤ ∑' n, ‖f n‖ := norm_tsum_le_tsum_norm hf.norm
    _ ≤ ∑' n, B * (4 * q) ^ n := hf.norm.tsum_le_tsum hbound hg
    _ = B / (1 - 4 * q) := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one (by positivity) hratio, div_eq_mul_inv]
    _ ≤ 2 * B := by
      apply (div_le_iff₀ (by linarith : 0 < 1 - 4 * q)).2
      nlinarith
    _ = 18 * xiShiftAbsoluteMass 0 * ((3 : ℝ) ^ k * v / 150) ^ 2 := by dsimp [B, q]; ring

/-- The positive exponent controlling the square root of the uniform remainder. -/
def liEvenCrossEulerSmallMassHalfExponent : ℝ := 1 - Real.log 3 / Real.log 4

theorem liEvenCrossEulerSmallMassHalfExponent_pos :
    0 < liEvenCrossEulerSmallMassHalfExponent := by
  have hlog : Real.log 3 < Real.log 4 := Real.log_lt_log (by norm_num) (by norm_num)
  have hfour : 0 < Real.log 4 := Real.log_pos (by norm_num)
  dsimp [liEvenCrossEulerSmallMassHalfExponent]
  have hquot : Real.log 3 / Real.log 4 < 1 := (div_lt_iff₀ hfour).2 (by simpa using hlog)
  linarith

/-- The uniform source remainder has exponent `2 - log₂ 3`. -/
theorem two_mul_liEvenCrossEulerSmallMassHalfExponent :
    2 * liEvenCrossEulerSmallMassHalfExponent = 2 - Real.log 3 / Real.log 2 := by
  have hlogfour : Real.log 4 = 2 * Real.log 2 := by
    simpa only [show (2 : ℝ) ^ (2 : ℕ) = 4 by norm_num, Nat.cast_ofNat] using
      Real.log_pow (2 : ℝ) 2
  have hlogtwo : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  dsimp [liEvenCrossEulerSmallMassHalfExponent]
  rw [hlogfour]
  field_simp

/-- The growing jet order is absorbed into one vanishing positive mass power. -/
theorem liEvenCrossEulerTailScale_log_window_le
    {v : ℝ} (hv : 0 < v) (C : ℝ) (k : ℕ)
    (hk : (k : ℝ) ≤ -Real.log v / Real.log 4 + C) :
    (3 : ℝ) ^ k * v / 150 ≤
      (3 : ℝ) ^ C / 150 * v ^ liEvenCrossEulerSmallMassHalfExponent := by
  have hthree : (0 : ℝ) < 3 := by norm_num
  have hscale : (3 : ℝ) ^ k * v ≤
      (3 : ℝ) ^ C * v ^ liEvenCrossEulerSmallMassHalfExponent := by
    apply (Real.log_le_log_iff (by positivity) (by positivity)).1
    rw [Real.log_mul (pow_pos hthree k).ne' hv.ne', Real.log_pow,
      Real.log_mul (Real.rpow_pos_of_pos hthree C).ne'
        (Real.rpow_pos_of_pos hv _).ne', Real.log_rpow hthree, Real.log_rpow hv]
    calc
      (k : ℝ) * Real.log 3 + Real.log v ≤
          (-Real.log v / Real.log 4 + C) * Real.log 3 + Real.log v :=
        add_le_add (mul_le_mul_of_nonneg_right hk
          (Real.log_pos (by norm_num : (1 : ℝ) < 3)).le) le_rfl
      _ = C * Real.log 3 + liEvenCrossEulerSmallMassHalfExponent * Real.log v := by
        dsimp [liEvenCrossEulerSmallMassHalfExponent]
        ring
  calc
    (3 : ℝ) ^ k * v / 150 ≤
        ((3 : ℝ) ^ C * v ^ liEvenCrossEulerSmallMassHalfExponent) / 150 := by gcongr
    _ = (3 : ℝ) ^ C / 150 * v ^ liEvenCrossEulerSmallMassHalfExponent := by ring

/-- An explicit uniform remainder estimate for every order below a logarithmic window. -/
theorem abs_liEvenCrossEulerNormalizedMassTail_log_window_le
    {v : ℝ} (hv : 0 < v) (C : ℝ) (k : ℕ)
    (hk : (k : ℝ) ≤ -Real.log v / Real.log 4 + C)
    (hsmall : (3 : ℝ) ^ C / 150 * v ^ liEvenCrossEulerSmallMassHalfExponent ≤ 1 / 8) :
    |liEvenCrossEulerNormalizedMassTail v k| ≤
      18 * xiShiftAbsoluteMass 0 * ((3 : ℝ) ^ C / 150) ^ 2 *
        v ^ (2 * liEvenCrossEulerSmallMassHalfExponent) := by
  have hscale := liEvenCrossEulerTailScale_log_window_le hv C k hk
  have hq := hscale.trans hsmall
  calc
    |liEvenCrossEulerNormalizedMassTail v k| ≤
        18 * xiShiftAbsoluteMass 0 * ((3 : ℝ) ^ k * v / 150) ^ 2 :=
      abs_liEvenCrossEulerNormalizedMassTail_le hv.le k hq
    _ ≤ 18 * xiShiftAbsoluteMass 0 *
        ((3 : ℝ) ^ C / 150 * v ^ liEvenCrossEulerSmallMassHalfExponent) ^ 2 := by
      have hA := xiShiftAbsoluteMass_nonneg 0
      gcongr
    _ = 18 * xiShiftAbsoluteMass 0 * ((3 : ℝ) ^ C / 150) ^ 2 *
        v ^ (2 * liEvenCrossEulerSmallMassHalfExponent) := by
      rw [mul_pow, show 2 * liEvenCrossEulerSmallMassHalfExponent =
        liEvenCrossEulerSmallMassHalfExponent * (2 : ℕ) by norm_num; ring,
        Real.rpow_mul_natCast hv.le]
      ring

/-- The complete remainder tends uniformly to zero over every earlier jet order. -/
theorem liEvenCrossEulerNormalizedMassTail_uniform_log_window
    (C : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ v : ℝ in nhdsWithin 0 (Set.Ioi 0), ∀ k : ℕ,
      (k : ℝ) ≤ -Real.log v / Real.log 4 + C →
        |liEvenCrossEulerNormalizedMassTail v k| < ε := by
  have hδ := liEvenCrossEulerSmallMassHalfExponent_pos
  have hp : Filter.Tendsto
      (fun v : ℝ => v ^ liEvenCrossEulerSmallMassHalfExponent)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa [Real.zero_rpow hδ.ne'] using
      ((Real.continuousAt_rpow_const 0 liEvenCrossEulerSmallMassHalfExponent
        (Or.inr hδ.le)).tendsto.mono_left nhdsWithin_le_nhds)
  have hs : Filter.Tendsto
      (fun v : ℝ => (3 : ℝ) ^ C / 150 * v ^ liEvenCrossEulerSmallMassHalfExponent)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa using tendsto_const_nhds.mul hp
  have hb : Filter.Tendsto
      (fun v : ℝ => 18 * xiShiftAbsoluteMass 0 * ((3 : ℝ) ^ C / 150) ^ 2 *
        v ^ (2 * liEvenCrossEulerSmallMassHalfExponent))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have hp2 : Filter.Tendsto
        (fun v : ℝ => v ^ (2 * liEvenCrossEulerSmallMassHalfExponent))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (0 ^ (2 * liEvenCrossEulerSmallMassHalfExponent))) :=
      (Real.continuousAt_rpow_const 0
      (2 * liEvenCrossEulerSmallMassHalfExponent) (Or.inr (by linarith :
        0 ≤ 2 * liEvenCrossEulerSmallMassHalfExponent))).tendsto.mono_left
          nhdsWithin_le_nhds
    simpa [Real.zero_rpow (by linarith : 2 * liEvenCrossEulerSmallMassHalfExponent ≠ 0)]
      using tendsto_const_nhds.mul hp2
  filter_upwards [self_mem_nhdsWithin,
    hs.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 8)),
    hb.eventually (Iio_mem_nhds hε)] with v hv hsmall hbound
  intro k hk
  exact (abs_liEvenCrossEulerNormalizedMassTail_log_window_le hv C k hk hsmall.le).trans_lt hbound

end

end RHTower
