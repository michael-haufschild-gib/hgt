import GaloisForLFunctions.RHTower.LiEvenCrossEulerMassJetSeries
import GaloisForLFunctions.RHTower.XiReciprocalSquareSecondMomentRadius

/-!
# The third actual source term and complete later mass tail

The actual normalized Euler jet retains its first positive source correction.
Two discrete quadratic envelopes bound every subsequent moment through a
geometric series at scale `2^k v / 150`, without a later-moment sign assumption.
-/

namespace RHTower

noncomputable section

/-- Complete normalized mass tail after the first three source moments. -/
def liEvenCrossEulerThirdMassTail (v : ℝ) (k : ℕ) : ℝ :=
  ∑' n : ℕ, (-1 : ℝ) ^ (n + 3) * ((n + 4 : ℕ) : ℝ) ^ (2 * k + 2) *
    normalizedPrimeArchMoment (n + 3) * v ^ (n + 3)

private theorem thirdMassTail_quadratic_two_envelope (n : ℕ) :
    ((n + 4 : ℕ) : ℝ) ^ 2 ≤ 16 * (2 : ℝ) ^ n := by
  induction n with
  | zero => norm_num
  | succ n hn =>
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hstep : ((n : ℝ) + 5) ^ 2 ≤ 2 * ((n : ℝ) + 4) ^ 2 := by
      nlinarith [sq_nonneg (n : ℝ)]
    calc
      (((n + 1) + 4 : ℕ) : ℝ) ^ 2 = ((n : ℝ) + 5) ^ 2 := by push_cast; ring
      _ ≤ 2 * ((n : ℝ) + 4) ^ 2 := hstep
      _ ≤ 2 * (16 * (2 : ℝ) ^ n) := by
        simpa only [Nat.cast_add, Nat.cast_ofNat] using
          mul_le_mul_of_nonneg_left hn (by norm_num : (0 : ℝ) ≤ 2)
      _ = 16 * (2 : ℝ) ^ (n + 1) := by rw [pow_succ]; ring

private theorem thirdMassTail_quadratic_four_envelope (n : ℕ) :
    ((n + 4 : ℕ) : ℝ) ^ 2 ≤ 16 * (4 : ℝ) ^ n := by
  induction n with
  | zero => norm_num
  | succ n hn =>
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hstep : ((n : ℝ) + 5) ^ 2 ≤ 4 * ((n : ℝ) + 4) ^ 2 := by
      nlinarith [sq_nonneg (n : ℝ)]
    calc
      (((n + 1) + 4 : ℕ) : ℝ) ^ 2 = ((n : ℝ) + 5) ^ 2 := by push_cast; ring
      _ ≤ 4 * ((n : ℝ) + 4) ^ 2 := hstep
      _ ≤ 4 * (16 * (4 : ℝ) ^ n) := by
        simpa only [Nat.cast_add, Nat.cast_ofNat] using
          mul_le_mul_of_nonneg_left hn (by norm_num : (0 : ℝ) ≤ 4)
      _ = 16 * (4 : ℝ) ^ (n + 1) := by rw [pow_succ]; ring

private theorem thirdMassTail_term_geometric_bound
    {v : ℝ} (hv : 0 ≤ v) (k n : ℕ) :
    |(-1 : ℝ) ^ (n + 3) * ((n + 4 : ℕ) : ℝ) ^ (2 * k + 2) *
        normalizedPrimeArchMoment (n + 3) * v ^ (n + 3)| ≤
      (16 * xiShiftAbsoluteMass 0 * (16 : ℝ) ^ k * v ^ 3 / 150 ^ 3) *
        (4 * ((2 : ℝ) ^ k * v / 150)) ^ n := by
  let r : ℝ := (n + 4 : ℕ)
  let p : ℝ := (2 : ℝ) ^ k * v / 150
  have hr : 0 ≤ r := by positivity
  have hA : 0 ≤ xiShiftAbsoluteMass 0 := xiShiftAbsoluteMass_nonneg 0
  have hm := abs_normalizedPrimeArchMoment_add_le_secondMomentRadius 0 (n + 3)
  simp only [zero_add] at hm
  have hk : (r ^ 2) ^ k ≤ (16 * (2 : ℝ) ^ n) ^ k :=
    pow_le_pow_left₀ (sq_nonneg r) (thirdMassTail_quadratic_two_envelope n) k
  have hswap : ((2 : ℝ) ^ n) ^ k = ((2 : ℝ) ^ k) ^ n := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm n k]
  have hterm : |(-1 : ℝ) ^ (n + 3) * r ^ (2 * k + 2) *
      normalizedPrimeArchMoment (n + 3) * v ^ (n + 3)| =
      r ^ (2 * k + 2) * |normalizedPrimeArchMoment (n + 3)| * v ^ (n + 3) := by
    simp [abs_mul, abs_pow, abs_of_nonneg hr, abs_of_nonneg hv]
  rw [hterm]
  calc
    r ^ (2 * k + 2) * |normalizedPrimeArchMoment (n + 3)| * v ^ (n + 3) ≤
        r ^ (2 * k + 2) * ((1 / 150 : ℝ) ^ (n + 3) * xiShiftAbsoluteMass 0) *
          v ^ (n + 3) := by gcongr
    _ = r ^ 2 * (r ^ 2) ^ k * ((1 / 150 : ℝ) ^ (n + 3) * xiShiftAbsoluteMass 0) *
          v ^ (n + 3) := by rw [pow_add, pow_mul]; ring
    _ ≤ r ^ 2 * (16 * (2 : ℝ) ^ n) ^ k *
          ((1 / 150 : ℝ) ^ (n + 3) * xiShiftAbsoluteMass 0) * v ^ (n + 3) := by gcongr
    _ ≤ (16 * (4 : ℝ) ^ n) * (16 * (2 : ℝ) ^ n) ^ k *
          ((1 / 150 : ℝ) ^ (n + 3) * xiShiftAbsoluteMass 0) * v ^ (n + 3) := by
      gcongr
      exact thirdMassTail_quadratic_four_envelope n
    _ = (16 * xiShiftAbsoluteMass 0 * (16 : ℝ) ^ k * v ^ 3 / 150 ^ 3) *
          (4 * p) ^ n := by
      rw [mul_pow, hswap]
      dsimp [p]
      simp only [div_eq_mul_inv, mul_pow, pow_add, one_pow, ← inv_pow]
      ring

/-- The complete later source tail is absolutely summable throughout its geometric window. -/
theorem summable_liEvenCrossEulerThirdMassTail
    {v : ℝ} (hv : 0 ≤ v) (k : ℕ)
    (hp : (2 : ℝ) ^ k * v / 150 ≤ 1 / 8) :
    Summable (fun n : ℕ => (-1 : ℝ) ^ (n + 3) *
      ((n + 4 : ℕ) : ℝ) ^ (2 * k + 2) * normalizedPrimeArchMoment (n + 3) * v ^ (n + 3)) := by
  let p : ℝ := (2 : ℝ) ^ k * v / 150
  let B : ℝ := 16 * xiShiftAbsoluteMass 0 * (16 : ℝ) ^ k * v ^ 3 / 150 ^ 3
  have hp0 : 0 ≤ p := by positivity
  have hratio : 4 * p < 1 := by dsimp [p] at *; linarith
  have hg : Summable (fun n : ℕ => B * (4 * p) ^ n) :=
    (summable_geometric_of_lt_one (by positivity) hratio).mul_left B
  apply hg.of_norm_bounded
  intro n
  simpa only [B, p, Real.norm_eq_abs] using thirdMassTail_term_geometric_bound hv k n

/-- Sharp third-tail scale, retaining every later source moment and allowing mass zero. -/
theorem abs_liEvenCrossEulerThirdMassTail_le
    {v : ℝ} (hv : 0 ≤ v) (k : ℕ)
    (hp : (2 : ℝ) ^ k * v / 150 ≤ 1 / 8) :
    |liEvenCrossEulerThirdMassTail v k| ≤
      32 * xiShiftAbsoluteMass 0 * ((4 : ℝ) ^ k * v) ^ 2 * v / 150 ^ 3 := by
  let p : ℝ := (2 : ℝ) ^ k * v / 150
  let B : ℝ := 16 * xiShiftAbsoluteMass 0 * (16 : ℝ) ^ k * v ^ 3 / 150 ^ 3
  let f : ℕ → ℝ := fun n => (-1 : ℝ) ^ (n + 3) *
    ((n + 4 : ℕ) : ℝ) ^ (2 * k + 2) * normalizedPrimeArchMoment (n + 3) * v ^ (n + 3)
  have hp0 : 0 ≤ p := by positivity
  have hp8 : p ≤ 1 / 8 := hp
  have hA : 0 ≤ xiShiftAbsoluteMass 0 := xiShiftAbsoluteMass_nonneg 0
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hratio : 4 * p < 1 := by linarith
  have hg : Summable (fun n : ℕ => B * (4 * p) ^ n) :=
    (summable_geometric_of_lt_one (by positivity) hratio).mul_left B
  have hbound : ∀ n, ‖f n‖ ≤ B * (4 * p) ^ n := by
    intro n
    simpa only [f, B, p, Real.norm_eq_abs] using thirdMassTail_term_geometric_bound hv k n
  have hf : Summable f := summable_liEvenCrossEulerThirdMassTail hv k hp
  have hpow : (16 : ℝ) ^ k = ((4 : ℝ) ^ k) ^ 2 := by
    rw [← pow_mul, Nat.mul_comm k 2, pow_mul]
    norm_num
  calc
    |liEvenCrossEulerThirdMassTail v k| = ‖∑' n, f n‖ := by
      simp only [liEvenCrossEulerThirdMassTail, f, Real.norm_eq_abs]
    _ ≤ ∑' n, ‖f n‖ := norm_tsum_le_tsum_norm hf.norm
    _ ≤ ∑' n, B * (4 * p) ^ n := hf.norm.tsum_le_tsum hbound hg
    _ = B / (1 - 4 * p) := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one (by positivity) hratio, div_eq_mul_inv]
    _ ≤ 2 * B := by
      apply (div_le_iff₀ (by linarith : 0 < 1 - 4 * p)).2
      nlinarith
    _ = 32 * xiShiftAbsoluteMass 0 * ((4 : ℝ) ^ k * v) ^ 2 * v / 150 ^ 3 := by
      dsimp [B]
      rw [hpow]
      ring

/-- Exact first three source terms of the actual normalized even Euler jet. -/
theorem liEvenCrossFirstCurrentEvenEulerJet_div_two_mul_mass_eq_three_terms
    {v : ℝ} (hv : 0 < v) (hvquarter : v ≤ 1 / 4) (k : ℕ) :
    liEvenCrossFirstCurrentEvenEulerJet v k / (2 * v) =
      normalizedPrimeArchMoment 0 - (4 : ℝ) ^ (k + 1) * normalizedPrimeArchMoment 1 * v +
        (9 : ℝ) ^ (k + 1) * normalizedPrimeArchMoment 2 * v ^ 2 +
        liEvenCrossEulerThirdMassTail v k := by
  let f : ℕ → ℝ := fun n => (-1 : ℝ) ^ n * ((n + 1 : ℕ) : ℝ) ^ (2 * k + 2) *
    normalizedPrimeArchMoment n * v ^ n
  have hf : Summable f := by
    refine ((summable_liEvenCrossFirstCurrentEvenEulerJet_massSeries hv hvquarter k).mul_right
      (1 / v)).congr fun n => ?_
    dsimp [f]
    rw [pow_succ]
    field_simp
    rw [pow_succ]
    ring
  have hjet : liEvenCrossFirstCurrentEvenEulerJet v k = 2 * v * ∑' n, f n := by
    rw [liEvenCrossFirstCurrentEvenEulerJet_eq_massSeries hv hvquarter, ← tsum_mul_left]
    apply tsum_congr
    intro n
    dsimp [f]
    rw [pow_succ]
    ring
  have hnormalized : liEvenCrossFirstCurrentEvenEulerJet v k / (2 * v) = ∑' n, f n := by
    rw [hjet]
    field_simp
  have htwo : (2 : ℝ) ^ (2 * k + 2) = (4 : ℝ) ^ (k + 1) := by
    rw [show 2 * k + 2 = 2 * (k + 1) by omega, pow_mul]
    norm_num
  have hthree : (3 : ℝ) ^ (2 * k + 2) = (9 : ℝ) ^ (k + 1) := by
    rw [show 2 * k + 2 = 2 * (k + 1) by omega, pow_mul]
    norm_num
  have hhead : ∑ n ∈ Finset.range 3, f n =
      normalizedPrimeArchMoment 0 - (4 : ℝ) ^ (k + 1) * normalizedPrimeArchMoment 1 * v +
        (9 : ℝ) ^ (k + 1) * normalizedPrimeArchMoment 2 * v ^ 2 := by
    norm_num [Finset.sum_range_succ, f]
    rw [htwo, hthree]
    ring
  have htail : (∑' n, f (n + 3)) = liEvenCrossEulerThirdMassTail v k := rfl
  rw [hnormalized]
  simpa only [hhead, htail] using (hf.sum_add_tsum_nat_add 3).symm

end

end RHTower
