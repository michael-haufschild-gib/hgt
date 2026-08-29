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

end

end GaloisForLFunctions.HTGeometry
