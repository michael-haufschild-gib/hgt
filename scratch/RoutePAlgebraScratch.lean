import Mathlib

private theorem routeP_algebra_linear_floor
    {t m E e μ q credit B C D F R : ℝ}
    (ht : 1 ≤ t) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hF : 0 ≤ F) (hR : 0 ≤ R)
    (hmlo : t ^ (4 : ℕ) / 2 ≤ m) (hmup : m ≤ R * t ^ (4 : ℕ))
    (hE : |E| ≤ C * t ^ (5 : ℕ)) (he0 : 0 ≤ e) (he : e ≤ F)
    (hμ : |μ| ≤ D * t) (hq : 0 ≤ q)
    (hcredit : -2 * B * t ^ (8 : ℕ) ≤ credit) :
    -(2 * B + 2 * F + 2 * (2 * C + F + D) ^ (2 : ℕ) +
        (4 + R) * D ^ (2 : ℕ) / 12) * t ^ (8 : ℕ) ≤
      credit - 2 * t ^ (4 : ℕ) * e -
        (2 * E + e - t ^ (4 : ℕ) * μ) ^ (2 : ℕ) / m -
        (4 * t ^ (4 : ℕ) + m) / 12 * μ ^ (2 : ℕ) + 4 * q / 3 := by
  let A : ℝ := 2 * C + F + D
  have ht0 : 0 ≤ t := by linarith
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have ht4 : 1 ≤ t ^ (4 : ℕ) := one_le_pow₀ ht
  have ht5 : 1 ≤ t ^ (5 : ℕ) := one_le_pow₀ ht
  have ht6le8 : t ^ (6 : ℕ) ≤ t ^ (8 : ℕ) := by
    calc
      t ^ (6 : ℕ) = t ^ (6 : ℕ) * 1 := by ring
      _ ≤ t ^ (6 : ℕ) * t ^ (2 : ℕ) := by
        exact mul_le_mul_of_nonneg_left (one_le_pow₀ ht) (pow_nonneg ht0 _)
      _ = t ^ (8 : ℕ) := by ring
  have ht4le8 : t ^ (4 : ℕ) ≤ t ^ (8 : ℕ) := by
    calc
      t ^ (4 : ℕ) = t ^ (4 : ℕ) * 1 := by ring
      _ ≤ t ^ (4 : ℕ) * t ^ (4 : ℕ) := by
        exact mul_le_mul_of_nonneg_left ht4 (pow_nonneg ht0 _)
      _ = t ^ (8 : ℕ) := by ring
  have hmpos : 0 < m := by
    have hp : 0 < t ^ (4 : ℕ) := pow_pos (by linarith) _
    linarith
  have hμmul : |t ^ (4 : ℕ) * μ| ≤ D * t ^ (5 : ℕ) := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg ht0 _)]
    calc
      t ^ (4 : ℕ) * |μ| ≤ t ^ (4 : ℕ) * (D * t) :=
        mul_le_mul_of_nonneg_left hμ (pow_nonneg ht0 _)
      _ = D * t ^ (5 : ℕ) := by ring
  have harg : |2 * E + e - t ^ (4 : ℕ) * μ| ≤ A * t ^ (5 : ℕ) := by
    have hEbounds := abs_le.mp hE
    have hμbounds := abs_le.mp hμmul
    have hFpower : F ≤ F * t ^ (5 : ℕ) := by
      calc F = F * 1 := by ring
        _ ≤ F * t ^ (5 : ℕ) := mul_le_mul_of_nonneg_left ht5 hF
    rw [abs_le]
    constructor <;> dsimp only [A] <;> linarith
  have hargSq : (2 * E + e - t ^ (4 : ℕ) * μ) ^ (2 : ℕ) ≤
      (A * t ^ (5 : ℕ)) ^ (2 : ℕ) := by
    have hmul : 0 ≤
        (A * t ^ (5 : ℕ) - |2 * E + e - t ^ (4 : ℕ) * μ|) *
          (A * t ^ (5 : ℕ) + |2 * E + e - t ^ (4 : ℕ) * μ|) :=
      mul_nonneg (sub_nonneg.mpr harg)
        (add_nonneg (by positivity) (abs_nonneg _))
    nlinarith only [hmul, sq_abs (2 * E + e - t ^ (4 : ℕ) * μ)]
  have hfirst :
      (2 * E + e - t ^ (4 : ℕ) * μ) ^ (2 : ℕ) / m ≤
        2 * A ^ (2 : ℕ) * t ^ (8 : ℕ) := by
    have hmul := mul_le_mul_of_nonneg_left hmlo
      (by positivity : 0 ≤ 2 * A ^ (2 : ℕ) * t ^ (6 : ℕ))
    have hnum : (2 * E + e - t ^ (4 : ℕ) * μ) ^ (2 : ℕ) ≤
        2 * A ^ (2 : ℕ) * t ^ (6 : ℕ) * m := by
      nlinarith [hargSq, hmul]
    have hdiv : (2 * E + e - t ^ (4 : ℕ) * μ) ^ (2 : ℕ) / m ≤
        2 * A ^ (2 : ℕ) * t ^ (6 : ℕ) :=
      (div_le_iff₀ hmpos).mpr hnum
    exact hdiv.trans (mul_le_mul_of_nonneg_left ht6le8 (by positivity))
  have hμSq : μ ^ (2 : ℕ) ≤ (D * t) ^ (2 : ℕ) := by
    have hmul : 0 ≤ (D * t - |μ|) * (D * t + |μ|) :=
      mul_nonneg (sub_nonneg.mpr hμ)
        (add_nonneg (by positivity) (abs_nonneg μ))
    nlinarith only [hmul, sq_abs μ]
  have hcoeff : (4 * t ^ (4 : ℕ) + m) / 12 ≤
      ((4 + R) * t ^ (4 : ℕ)) / 12 := by linarith
  have hcoeff0 : 0 ≤ (4 * t ^ (4 : ℕ) + m) / 12 := by positivity
  have huppercoeff0 : 0 ≤ ((4 + R) * t ^ (4 : ℕ)) / 12 := by positivity
  have hsecond :
      (4 * t ^ (4 : ℕ) + m) / 12 * μ ^ (2 : ℕ) ≤
        ((4 + R) * D ^ (2 : ℕ) / 12) * t ^ (8 : ℕ) := by
    calc
      _ ≤ ((4 + R) * t ^ (4 : ℕ) / 12) * μ ^ (2 : ℕ) :=
        mul_le_mul_of_nonneg_right hcoeff (sq_nonneg μ)
      _ ≤ ((4 + R) * t ^ (4 : ℕ) / 12) * (D * t) ^ (2 : ℕ) :=
        mul_le_mul_of_nonneg_left hμSq huppercoeff0
      _ = ((4 + R) * D ^ (2 : ℕ) / 12) * t ^ (6 : ℕ) := by ring
      _ ≤ ((4 + R) * D ^ (2 : ℕ) / 12) * t ^ (8 : ℕ) :=
        mul_le_mul_of_nonneg_left ht6le8 (by positivity)
  have heterm : 2 * t ^ (4 : ℕ) * e ≤ 2 * F * t ^ (8 : ℕ) := by
    calc
      _ ≤ 2 * t ^ (4 : ℕ) * F :=
        mul_le_mul_of_nonneg_left he (by positivity)
      _ = 2 * F * t ^ (4 : ℕ) := by ring
      _ ≤ 2 * F * t ^ (8 : ℕ) :=
        mul_le_mul_of_nonneg_left ht4le8 (by positivity)
  dsimp only [A] at hfirst
  linarith
