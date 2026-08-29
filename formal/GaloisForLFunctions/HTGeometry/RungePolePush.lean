import Mathlib

/-!
# Moving a simple pole by a truncated geometric series

`(z − a)⁻¹` expands around a nearby centre `b` as `∑ₙ (a−b)ⁿ (z−b)⁻⁽ⁿ⁺¹⁾`, with truncation error
`((a−b)(z−b)⁻¹)^N (z−a)⁻¹`.  Expanding instead in powers of `z` moves the pole to infinity and
leaves a polynomial.  These are the two pole-pushing steps of Runge approximation.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex

noncomputable section

/-- Truncated expansion of `(z − a)⁻¹` in powers of `(z − b)⁻¹`. -/
def polePushSum (a b : ℂ) (N : ℕ) (z : ℂ) : ℂ :=
  ∑ n ∈ Finset.range N, (a - b) ^ n * ((z - b)⁻¹) ^ (n + 1)

/-- Truncated expansion of `(z − a)⁻¹` in powers of `z`: a polynomial. -/
def infPushSum (a : ℂ) (N : ℕ) (z : ℂ) : ℂ :=
  -∑ n ∈ Finset.range N, z ^ n * (a⁻¹) ^ (n + 1)

theorem polePush_identity {a b z : ℂ} (hza : z ≠ a) (hzb : z ≠ b) (N : ℕ) :
    (z - a)⁻¹ - polePushSum a b N z = ((a - b) * (z - b)⁻¹) ^ N * (z - a)⁻¹ := by
  have hza' : z - a ≠ 0 := sub_ne_zero.2 hza
  have hzb' : z - b ≠ 0 := sub_ne_zero.2 hzb
  induction N with
  | zero => simp [polePushSum]
  | succ N ih =>
      rw [polePushSum, Finset.sum_range_succ, ← polePushSum]
      have hstep : (z - a)⁻¹ - (polePushSum a b N z + (a - b) ^ N * ((z - b)⁻¹) ^ (N + 1))
          = ((z - a)⁻¹ - polePushSum a b N z) - (a - b) ^ N * ((z - b)⁻¹) ^ (N + 1) := by
        ring
      rw [hstep, ih]
      have hkey : (z - a)⁻¹ - (z - b)⁻¹ = (a - b) * ((z - b)⁻¹ * (z - a)⁻¹) := by
        field_simp
        ring
      have hL : (a - b) ^ N * ((z - b)⁻¹) ^ (N + 1) = ((a - b) * (z - b)⁻¹) ^ N * (z - b)⁻¹ := by
        rw [mul_pow]
        ring
      have hR : ((a - b) * (z - b)⁻¹) ^ (N + 1) * (z - a)⁻¹
          = ((a - b) * (z - b)⁻¹) ^ N * ((a - b) * ((z - b)⁻¹ * (z - a)⁻¹)) := by ring
      rw [hL, hR, ← hkey]
      ring

theorem infPush_identity {a z : ℂ} (ha : a ≠ 0) (hza : z ≠ a) (N : ℕ) :
    (z - a)⁻¹ - infPushSum a N z = (z * a⁻¹) ^ N * (z - a)⁻¹ := by
  have hza' : z - a ≠ 0 := sub_ne_zero.2 hza
  induction N with
  | zero => simp [infPushSum]
  | succ N ih =>
      have hexpand : infPushSum a (N + 1) z = infPushSum a N z - z ^ N * (a⁻¹) ^ (N + 1) := by
        rw [infPushSum, infPushSum, Finset.sum_range_succ]
        ring
      rw [hexpand]
      have hstep : (z - a)⁻¹ - (infPushSum a N z - z ^ N * (a⁻¹) ^ (N + 1))
          = ((z - a)⁻¹ - infPushSum a N z) + z ^ N * (a⁻¹) ^ (N + 1) := by
        ring
      rw [hstep, ih]
      have hkey : (z - a)⁻¹ + a⁻¹ = z * a⁻¹ * (z - a)⁻¹ := by
        field_simp
        ring
      have hL : z ^ N * (a⁻¹) ^ (N + 1) = (z * a⁻¹) ^ N * a⁻¹ := by
        rw [mul_pow]
        ring
      have hR : (z * a⁻¹) ^ (N + 1) * (z - a)⁻¹
          = (z * a⁻¹) ^ N * (z * a⁻¹ * (z - a)⁻¹) := by ring
      rw [hL, hR, ← hkey]
      ring

theorem norm_polePush_error {a b z : ℂ} (hza : z ≠ a) (hzb : z ≠ b) (N : ℕ) :
    ‖(z - a)⁻¹ - polePushSum a b N z‖ = (‖a - b‖ / ‖z - b‖) ^ N / ‖z - a‖ := by
  rw [polePush_identity hza hzb N, norm_mul, norm_pow, norm_mul, norm_inv, norm_inv,
    div_eq_mul_inv, div_eq_mul_inv]

theorem norm_infPush_error {a z : ℂ} (ha : a ≠ 0) (hza : z ≠ a) (N : ℕ) :
    ‖(z - a)⁻¹ - infPushSum a N z‖ = (‖z‖ / ‖a‖) ^ N / ‖z - a‖ := by
  rw [infPush_identity ha hza N, norm_mul, norm_pow, norm_mul, norm_inv, norm_inv,
    div_eq_mul_inv, div_eq_mul_inv]


/-- **Pushing a simple pole to a nearby point.**  If `b` is closer to `a` than to `K`, the kernel
`(· − a)⁻¹` is uniformly approximated on `K` by rational functions with a single pole at `b`. -/
theorem exists_polePush_small {K : Set ℂ} {a b : ℂ} {r d : ℝ}
    (hr0 : 0 ≤ r) (hrd : r < d) (hab : ‖a - b‖ ≤ r) (hzb : ∀ z ∈ K, d ≤ ‖z - b‖)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ z ∈ K, ‖(z - a)⁻¹ - polePushSum a b N z‖ ≤ ε := by
  have hd : 0 < d := lt_of_le_of_lt hr0 hrd
  have hdr : 0 < d - r := by linarith
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (x := ε * (d - r)) (y := r / d) (mul_pos hε hdr)
    (by rw [div_lt_one hd]; exact hrd)
  refine ⟨N, fun z hz => ?_⟩
  have hzbd : d ≤ ‖z - b‖ := hzb z hz
  have hzbpos : 0 < ‖z - b‖ := lt_of_lt_of_le hd hzbd
  have hzbne : z ≠ b := by
    intro hcon
    rw [hcon] at hzbpos
    simp at hzbpos
  have hzab : d - r ≤ ‖z - a‖ := by
    have h1 : ‖z - b‖ - ‖a - b‖ ≤ ‖(z - b) - (a - b)‖ := norm_sub_norm_le _ _
    have h2 : (z - b) - (a - b) = z - a := by ring
    rw [h2] at h1
    linarith
  have hzapos : 0 < ‖z - a‖ := lt_of_lt_of_le hdr hzab
  have hzane : z ≠ a := by
    intro hcon
    rw [hcon] at hzapos
    simp at hzapos
  rw [norm_polePush_error hzane hzbne]
  have hratio : ‖a - b‖ / ‖z - b‖ ≤ r / d := by
    rw [div_le_div_iff₀ hzbpos hd]
    nlinarith [norm_nonneg (a - b)]
  have hpow : (‖a - b‖ / ‖z - b‖) ^ N ≤ (r / d) ^ N :=
    pow_le_pow_left₀ (by positivity) hratio N
  have hstep1 : (‖a - b‖ / ‖z - b‖) ^ N / ‖z - a‖ ≤ (r / d) ^ N / ‖z - a‖ :=
    (div_le_div_iff_of_pos_right hzapos).mpr hpow
  have hstep2 : (r / d) ^ N / ‖z - a‖ ≤ (r / d) ^ N / (d - r) :=
    div_le_div_of_nonneg_left (by positivity) hdr hzab
  have hstep3 : (r / d) ^ N / (d - r) ≤ ε := by
    rw [div_le_iff₀ hdr]
    linarith [hN]
  linarith

/-- **Pushing a simple pole to infinity.**  A pole far outside `K` can be replaced by a polynomial
approximation, uniformly on `K`. -/
theorem exists_infPush_small {K : Set ℂ} {a : ℂ} {R : ℝ} (hR : 0 < R)
    (hKR : ∀ z ∈ K, ‖z‖ ≤ R) (haR : 2 * R ≤ ‖a‖) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ z ∈ K, ‖(z - a)⁻¹ - infPushSum a N z‖ ≤ ε := by
  have hapos : 0 < ‖a‖ := lt_of_lt_of_le (by linarith) haR
  have ha : a ≠ 0 := by
    intro hcon
    rw [hcon] at hapos
    simp at hapos
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (x := ε * R) (y := (1:ℝ)/2) (mul_pos hε hR)
    (by norm_num)
  refine ⟨N, fun z hz => ?_⟩
  have hzR : ‖z‖ ≤ R := hKR z hz
  have hza : R ≤ ‖z - a‖ := by
    have h1 : ‖a‖ - ‖z‖ ≤ ‖a - z‖ := norm_sub_norm_le _ _
    have h2 : ‖a - z‖ = ‖z - a‖ := norm_sub_rev a z
    rw [h2] at h1
    linarith
  have hzapos : 0 < ‖z - a‖ := lt_of_lt_of_le hR hza
  have hzane : z ≠ a := by
    intro hcon
    rw [hcon] at hzapos
    simp at hzapos
  rw [norm_infPush_error ha hzane]
  have hratio : ‖z‖ / ‖a‖ ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hapos (by norm_num : (0:ℝ) < 2)]
    linarith
  have hpow : (‖z‖ / ‖a‖) ^ N ≤ ((1:ℝ) / 2) ^ N :=
    pow_le_pow_left₀ (by positivity) hratio N
  have hstep1 : (‖z‖ / ‖a‖) ^ N / ‖z - a‖ ≤ ((1:ℝ) / 2) ^ N / ‖z - a‖ :=
    (div_le_div_iff_of_pos_right hzapos).mpr hpow
  have hstep2 : ((1:ℝ) / 2) ^ N / ‖z - a‖ ≤ ((1:ℝ) / 2) ^ N / R :=
    div_le_div_of_nonneg_left (by positivity) hR hza
  have hstep3 : ((1:ℝ) / 2) ^ N / R ≤ ε := by
    rw [div_le_iff₀ hR]
    linarith [hN]
  linarith

end

end GaloisForLFunctions.HTGeometry
