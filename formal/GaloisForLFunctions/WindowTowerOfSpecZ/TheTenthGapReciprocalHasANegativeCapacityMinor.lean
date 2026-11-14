import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import GaloisForLFunctions.WindowTowerOfSpecZ.TheEvenFirstOverlapHasPolynomialReciprocalBounds

/-!
# A reciprocal bound with a negative capacity minor

A degree-sixteen polynomial majorizes the reciprocal of
`111/100 − log(1−x²)/2` on `[0,1)`. Five homogeneous
polynomial certificates prove the comparison against a finite logarithmic
sum. Reflected pairs stay uniformly away from the inverse determinant pole.
The associated polynomial capacity has a negative second principal minor,
even with the exact low-mode charges retained.
-/

noncomputable section
open Real
namespace GaloisForLFunctions.WindowTowerOfSpecZ

private def v32 (z : ℝ) : ℝ :=
  111 / 100 + ∑ j ∈ Finset.range 32, z ^ (j + 1) / (2 * ((j : ℝ) + 1))

private def q8 (z : ℝ) : ℝ :=
  100 / 111 - (2029 / 5000) * z - (201 / 10000) * z ^ 2 -
    (87 / 2500) * z ^ 3 - (203 / 10000) * z ^ 4 - (17 / 200) * z ^ 8

private def vHom (l u v t : ℝ) : ℝ :=
  (111 / 100 : ℝ) * (v + t) ^ 32 +
    ∑ j ∈ Finset.range 32,
      (l * v + u * t) ^ (j + 1) * (v + t) ^ (31 - j) / (2 * ((j : ℝ) + 1))

private def qHom (l u v t : ℝ) : ℝ :=
  (100 / 111 : ℝ) * (v + t) ^ 8 -
    (2029 / 5000) * (l * v + u * t) * (v + t) ^ 7 -
    (201 / 10000) * (l * v + u * t) ^ 2 * (v + t) ^ 6 -
    (87 / 2500) * (l * v + u * t) ^ 3 * (v + t) ^ 5 -
    (203 / 10000) * (l * v + u * t) ^ 4 * (v + t) ^ 4 -
    (17 / 200) * (l * v + u * t) ^ 8

private def residual (l u v t : ℝ) : ℝ :=
  vHom l u v t * qHom l u v t - (v + t) ^ 40

private theorem cell_one {v t : ℝ} (hv : 0 ≤ v) (ht : 0 ≤ t) :
    0 ≤ residual 0 (1 / 4) v t := by
  unfold residual vHom qHom
  norm_num [Finset.sum_range_succ]
  apply sub_nonneg.mp
  ring_nf
  positivity

private theorem cell_two {v t : ℝ} (hv : 0 ≤ v) (ht : 0 ≤ t) :
    0 ≤ residual (1 / 4) (1 / 2) v t := by
  unfold residual vHom qHom
  norm_num [Finset.sum_range_succ]
  apply sub_nonneg.mp
  ring_nf
  positivity

private theorem cell_three {v t : ℝ} (hv : 0 ≤ v) (ht : 0 ≤ t) :
    0 ≤ residual (1 / 2) (3 / 4) v t := by
  unfold residual vHom qHom
  norm_num [Finset.sum_range_succ]
  apply sub_nonneg.mp
  ring_nf
  positivity

private theorem cell_four {v t : ℝ} (hv : 0 ≤ v) (ht : 0 ≤ t) :
    0 ≤ residual (3 / 4) (7 / 8) v t := by
  unfold residual vHom qHom
  norm_num [Finset.sum_range_succ]
  apply sub_nonneg.mp
  ring_nf
  positivity

private theorem cell_five {v t : ℝ} (hv : 0 ≤ v) (ht : 0 ≤ t) :
    0 ≤ residual (7 / 8) 1 v t := by
  unfold residual vHom qHom
  norm_num [Finset.sum_range_succ]
  apply sub_nonneg.mp
  ring_nf
  positivity

private theorem residual_identity (l u z : ℝ) :
    (u - l) ^ 40 * (v32 z * q8 z - 1) = residual l u (u - z) (z - l) := by
  unfold residual vHom qHom
  rw [show (u - z) + (z - l) = u - l by ring,
    show l * (u - z) + u * (z - l) = z * (u - l) by ring]
  unfold v32 q8
  generalize u - l = s
  norm_num [Finset.sum_range_succ]
  ring

private theorem interval_bound {l u z : ℝ} (hlu : l < u) (hl : l ≤ z) (hu : z ≤ u)
    (h : ∀ v t : ℝ, 0 ≤ v → 0 ≤ t → 0 ≤ residual l u v t) :
    1 ≤ v32 z * q8 z := by
  have hp := h (u - z) (z - l) (sub_nonneg.mpr hu) (sub_nonneg.mpr hl)
  rw [← residual_identity] at hp
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right hp (pow_pos (sub_pos.mpr hlu) 40))

private theorem product_bound {z : ℝ} (h0 : 0 ≤ z) (h1 : z ≤ 1) :
    1 ≤ v32 z * q8 z := by
  by_cases hq : z ≤ 1 / 4
  · exact interval_bound (by norm_num) h0 hq (fun _ _ hv ht => cell_one hv ht)
  by_cases hh : z ≤ 1 / 2
  · exact interval_bound (by norm_num) (le_of_not_ge hq) hh
      (fun _ _ hv ht => cell_two hv ht)
  by_cases ht : z ≤ 3 / 4
  · exact interval_bound (by norm_num) (le_of_not_ge hh) ht
      (fun _ _ hv ht => cell_three hv ht)
  by_cases he : z ≤ 7 / 8
  · exact interval_bound (by norm_num) (le_of_not_ge ht) he
      (fun _ _ hv ht => cell_four hv ht)
  exact interval_bound (by norm_num) (le_of_not_ge he) h1
    (fun _ _ hv ht => cell_five hv ht)

private theorem v32_pos {z : ℝ} (h0 : 0 ≤ z) : 0 < v32 z := by
  have hs : 0 ≤ ∑ j ∈ Finset.range 32, z ^ (j + 1) / (2 * ((j : ℝ) + 1)) :=
    Finset.sum_nonneg (fun j _ => by positivity)
  dsimp only [v32]
  linarith only [hs]

/-- The finite logarithmic potential for the tenth harmonic gap. -/
def primeThreeTenEvenPotential (x : ℝ) : ℝ := v32 (x ^ 2)

/-- Polynomial reciprocal majorant for the logarithmic potential on `[0,1)`. -/
def primeThreeTenEvenReciprocal (x : ℝ) : ℝ := q8 (x ^ 2)

/-- The finite potential times the reciprocal polynomial is at least one. -/
theorem primeThreeTenEvenReciprocal_bound {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    0 < primeThreeTenEvenReciprocal x ∧
      1 ≤ primeThreeTenEvenPotential x * primeThreeTenEvenReciprocal x := by
  have hx : x ^ 2 ≤ 1 := by nlinarith only [h0, h1]
  have hp := product_bound (sq_nonneg x) hx
  refine ⟨?_, hp⟩
  by_contra hn
  have hq : q8 (x ^ 2) ≤ 0 := le_of_not_gt hn
  have hz := mul_nonpos_of_nonneg_of_nonpos (v32_pos (sq_nonneg x)).le hq
  linarith only [hp, hz]

/-- The finite potential lies below the logarithmic boundary term. -/
theorem primeThreeTenEvenPotential_le_log {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) :
    primeThreeTenEvenPotential x ≤ 111 / 100 - Real.log (1 - x ^ 2) / 2 := by
  have h := firstOverlapEvenPotential_le_log h0 h1
  have he : primeThreeTenEvenPotential x = firstOverlapEvenPotential x - 3029 / 3000 +
      111 / 100 := by
    unfold primeThreeTenEvenPotential v32 firstOverlapEvenPotential
    simp_rw [← pow_mul]
    ring
  rw [he]
  linarith only [h]

private theorem reciprocal_quadratic_upper (x : ℝ) :
    primeThreeTenEvenReciprocal x ≤ 100 / 111 - (2029 / 5000) * x ^ 2 := by
  unfold primeThreeTenEvenReciprocal q8
  nlinarith only [pow_nonneg (sq_nonneg x) 2, pow_nonneg (sq_nonneg x) 3,
    pow_nonneg (sq_nonneg x) 4, pow_nonneg (sq_nonneg x) 8]

/-- Reflected reciprocal products are at most `11/20` near the prime-three boundary. -/
theorem primeThreeTenEvenReciprocal_pair_bound {x y : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hlo : 63 / 50 ≤ x + y) (hhi : x + y ≤ 127 / 100) :
    primeThreeTenEvenReciprocal x * primeThreeTenEvenReciprocal y ≤ 11 / 20 := by
  have hqx := reciprocal_quadratic_upper x
  have hqy := reciprocal_quadratic_upper y
  have hxp := (primeThreeTenEvenReciprocal_bound hx0 hx1).1
  have hyp := (primeThreeTenEvenReciprocal_bound hy0 hy1).1
  have hp := mul_le_mul hqx hqy hyp.le (hxp.le.trans hqx)
  have hsumlo := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 63 / 50) hlo 2
  have hsumhi := pow_le_pow_left₀ (add_nonneg hx0 hy0) hhi 2
  have hsum : (63 / 50 : ℝ) ^ 2 / 2 ≤ x ^ 2 + y ^ 2 := by
    nlinarith only [hsumlo, sq_nonneg (x - y)]
  have hxy : x * y ≤ (127 / 100 : ℝ) ^ 2 / 4 := by
    nlinarith only [hsumhi, sq_nonneg (x - y)]
  have hxy2 := pow_le_pow_left₀ (mul_nonneg hx0 hy0) hxy 2
  have hu : (100 / 111 - (2029 / 5000) * x ^ 2) *
      (100 / 111 - (2029 / 5000) * y ^ 2) ≤ (11 / 20 : ℝ) := by
    nlinarith only [hsum, hxy2]
  exact hp.trans hu

namespace TenthGapCapacity

open MeasureTheory

/-- A cubic geometric majorant for the reflected-pair determinant reciprocal. -/
theorem inverse_pair_ratio_upper {z : ℝ} (h0 : 0 ≤ z) (h1 : z ≤ 2 / 15) :
    1 / (1 - z) ≤ 1 + z + z ^ 2 + (15 / 13) * z ^ 3 := by
  have hd : 0 < 1 - z := by linarith only [h1]
  have hp := mul_nonneg (pow_nonneg h0 3)
    (show 0 ≤ 2 - 15 * z by linarith only [h1])
  apply (div_le_iff₀ hd).mpr
  nlinarith only [hp]

private def b : ℝ := 523719 / 2000000
private def w : ℝ := 49013 / 100000
private def mid : ℝ := (b + 1) / 2
private def halfwidth : ℝ := (1 - b) / 2
private def xp (t : ℝ) : ℝ := mid + halfwidth * t
private def xm (t : ℝ) : ℝ := mid - halfwidth * t
private def q (x : ℝ) : ℝ := primeThreeTenEvenReciprocal x
private def p (i : ℕ) (x : ℝ) : ℝ :=
  if i = 0 then 1 else (3 * x ^ 2 - 1) / 2
private def z (t : ℝ) : ℝ := w ^ 2 * q (xp t) * q (xm t)
private def geom (t : ℝ) : ℝ :=
  1 + z t + z t ^ 2 + (15 / 13) * z t ^ 3
private def pair (i j : ℕ) (t : ℝ) : ℝ :=
  q (xp t) * p i (xp t) * p j (xp t) +
    q (xm t) * p i (xm t) * p j (xm t) +
    w * q (xp t) * q (xm t) *
      (p i (xp t) * p j (xm t) + p i (xm t) * p j (xp t))
private def cap (i j : ℕ) : ℝ :=
  (∫ x in (0 : ℝ)..b, q x * p i x * p j x) +
    halfwidth * ∫ t in (0 : ℝ)..1, pair i j t * geom t

private def aRef : ℝ := 5493 / 10000
private def gap : ℝ := 7381 / 2520
private def primitiveConstant : ℝ := 507 / 5000
private def charge0 : ℝ := gap - 7 * aRef / 2 -
  (1 / 36 + primitiveConstant / 24) * aRef ^ 2 - 3 * aRef ^ 3 / 8 -
    aRef ^ 5 / 198 - aRef ^ 7 / 5760 - aRef ^ 9 / 921600
private def charge2 : ℝ := 5 * (gap - 3 / 2) +
  (5 / 252 - 5 * primitiveConstant / 24) * aRef ^ 2 -
    5 * aRef ^ 5 / 396 - aRef ^ 7 / 1008 - aRef ^ 9 / 112896
private def cross02 : ℝ := aRef ^ 2 / 72 + 3 * aRef ^ 3 / 8 +
  25 * aRef ^ 5 / 2772 + 17 * aRef ^ 7 / 40320 + aRef ^ 9 / 322560
private def chargeDet : ℝ := charge0 * charge2 - cross02 ^ 2

private def b00 : ℝ := charge2 - chargeDet * (cap 0 0 + 1 / 100000)
private def b02 : ℝ := cross02 - chargeDet * cap 0 1
private def b22 : ℝ := charge0 - chargeDet * (cap 1 1 + 1 / 100000)

/-- First principal minor of the scaled inverse-charge minus capacity matrix. -/
def firstCapacityMinor : ℝ := b00

/-- Second principal minor of the scaled inverse-charge minus capacity matrix. -/
def secondCapacityMinor : ℝ := b00 * b22 - b02 ^ 2

private def capacity00 : {c : ℝ // cap 0 0 = c} := by
  have h : cap 0 0 = (∫ x in (0 : ℝ)..b, q x * p 0 x * p 0 x) +
      halfwidth * ∫ t in (0 : ℝ)..1, pair 0 0 t * geom t := rfl
  conv at h =>
    rhs; lhs; arg 1; ext x
    norm_num [q, primeThreeTenEvenReciprocal, q8, p]
    ring_nf
  conv at h =>
    rhs; rhs; rhs; arg 1; ext t
    norm_num [pair, geom, z, q, primeThreeTenEvenReciprocal, q8, p, xp, xm, mid, halfwidth, b, w]
    ring_nf
  simp (disch := (apply Continuous.intervalIntegrable; fun_prop)) only
    [intervalIntegral.integral_add, intervalIntegral.integral_mul_const,
      intervalIntegral.integral_const, integral_pow] at h
  norm_num [halfwidth, b] at h
  exact ⟨_, h⟩

private def capacity02 : {c : ℝ // cap 0 1 = c} := by
  have h : cap 0 1 = (∫ x in (0 : ℝ)..b, q x * p 0 x * p 1 x) +
      halfwidth * ∫ t in (0 : ℝ)..1, pair 0 1 t * geom t := rfl
  conv at h =>
    rhs; lhs; arg 1; ext x
    norm_num [q, primeThreeTenEvenReciprocal, q8, p]
    ring_nf
  conv at h =>
    rhs; rhs; rhs; arg 1; ext t
    norm_num [pair, geom, z, q, primeThreeTenEvenReciprocal, q8, p, xp, xm, mid, halfwidth, b, w]
    ring_nf
  simp (disch := (apply Continuous.intervalIntegrable; fun_prop)) only
    [intervalIntegral.integral_add, intervalIntegral.integral_mul_const,
      intervalIntegral.integral_const, integral_pow] at h
  norm_num [halfwidth, b] at h
  exact ⟨_, h⟩

private def capacity22 : {c : ℝ // cap 1 1 = c} := by
  have h : cap 1 1 = (∫ x in (0 : ℝ)..b, q x * p 1 x * p 1 x) +
      halfwidth * ∫ t in (0 : ℝ)..1, pair 1 1 t * geom t := rfl
  conv at h =>
    rhs; lhs; arg 1; ext x
    norm_num [q, primeThreeTenEvenReciprocal, q8, p]
    ring_nf
  conv at h =>
    rhs; rhs; rhs; arg 1; ext t
    norm_num [pair, geom, z, q, primeThreeTenEvenReciprocal, q8, p, xp, xm, mid, halfwidth, b, w]
    ring_nf
  simp (disch := (apply Continuous.intervalIntegrable; fun_prop)) only
    [intervalIntegral.integral_add, intervalIntegral.integral_mul_const,
      intervalIntegral.integral_const, integral_pow] at h
  norm_num [halfwidth, b] at h
  exact ⟨_, h⟩

/-- The first principal minor of the weighted moment capacity is positive. -/
theorem first_capacity_minor : 0 < firstCapacityMinor := by
  unfold firstCapacityMinor b00
  rw [capacity00.property]
  norm_num [capacity00, chargeDet, charge0, charge2, cross02, aRef, gap, primitiveConstant]

/-- The second principal minor is negative, so this polynomial bound cannot certify the floor. -/
theorem second_capacity_minor_neg : secondCapacityMinor < 0 := by
  unfold secondCapacityMinor b02 b00 b22
  rw [capacity00.property, capacity02.property, capacity22.property]
  norm_num [capacity00, capacity02, capacity22, chargeDet, charge0, charge2, cross02, aRef, gap, primitiveConstant]


end TenthGapCapacity

end GaloisForLFunctions.WindowTowerOfSpecZ

#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.primeThreeTenEvenReciprocal_bound
#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.primeThreeTenEvenPotential_le_log
#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.primeThreeTenEvenReciprocal_pair_bound
#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.TenthGapCapacity.inverse_pair_ratio_upper
#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.TenthGapCapacity.first_capacity_minor
#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.TenthGapCapacity.second_capacity_minor_neg
