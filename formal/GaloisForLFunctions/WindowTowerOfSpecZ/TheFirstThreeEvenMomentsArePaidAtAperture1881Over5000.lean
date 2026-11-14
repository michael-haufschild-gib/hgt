import GaloisForLFunctions.WindowTowerOfSpecZ.TheEvenFirstOverlapHasPolynomialReciprocalBounds
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Capacity of the first three even moments

A reciprocal bound retains the full reflected-pair inverse. Its three moment
capacities form a positive rational certificate. Parameter estimates control
the displacement from the reference aperture to the logarithmic aperture.
-/

noncomputable section
open Real MeasureTheory Set Filter
namespace GaloisForLFunctions.WindowTowerOfSpecZ

private def bRef : ℝ := 1684993 / 2000000
private def wRef : ℝ := 49013 / 100000
private def pairMidpoint : ℝ := (bRef + 1) / 2
private def halfwidth : ℝ := (1 - bRef) / 2
private def xp (t : ℝ) : ℝ := pairMidpoint + halfwidth * t
private def xm (t : ℝ) : ℝ := pairMidpoint - halfwidth * t
private def qStrip (x : ℝ) : ℝ := firstOverlapEvenStripReciprocal x
private def p2 (x : ℝ) : ℝ := (3 * x ^ 2 - 1) / 2
private def p4 (x : ℝ) : ℝ := (35 * x ^ 4 - 30 * x ^ 2 + 3) / 8
private def pairZ (t : ℝ) : ℝ := wRef ^ 2 * qStrip (xp t) * qStrip (xm t)
private def pairS (t : ℝ) : ℝ := 1 + pairZ t + pairZ t ^ 2 + 1 / 900
private def pair00 (t : ℝ) : ℝ :=
  qStrip (xp t) + qStrip (xm t) + 2 * wRef * qStrip (xp t) * qStrip (xm t)
private def pair02 (t : ℝ) : ℝ :=
  qStrip (xp t) * p2 (xp t) + qStrip (xm t) * p2 (xm t) +
    wRef * qStrip (xp t) * qStrip (xm t) * (p2 (xp t) + p2 (xm t))
private def pair22 (t : ℝ) : ℝ :=
  qStrip (xp t) * p2 (xp t) ^ 2 + qStrip (xm t) * p2 (xm t) ^ 2 +
    2 * wRef * qStrip (xp t) * qStrip (xm t) * p2 (xp t) * p2 (xm t)
private def pair04 (t : ℝ) : ℝ :=
  qStrip (xp t) * p4 (xp t) + qStrip (xm t) * p4 (xm t) +
    wRef * qStrip (xp t) * qStrip (xm t) * (p4 (xp t) + p4 (xm t))
private def pair24 (t : ℝ) : ℝ :=
  qStrip (xp t) * p2 (xp t) * p4 (xp t) + qStrip (xm t) * p2 (xm t) * p4 (xm t) +
    wRef * qStrip (xp t) * qStrip (xm t) * (p2 (xp t) * p4 (xm t) + p2 (xm t) * p4 (xp t))
private def pair44 (t : ℝ) : ℝ :=
  qStrip (xp t) * p4 (xp t) ^ 2 + qStrip (xm t) * p4 (xm t) ^ 2 +
    2 * wRef * qStrip (xp t) * qStrip (xm t) * p4 (xp t) * p4 (xm t)
private def outsideMomentRaw (k : ℕ) : ℝ :=
  bRef ^ (2 * k + 1) * ((3000 / 3029 : ℝ) / (2 * (k : ℝ) + 1) -
    (2449 / 5000) * bRef ^ 2 / (2 * (k : ℝ) + 3) -
    (1 / 20) * bRef ^ 6 / (2 * (k : ℝ) + 7) -
    (3 / 100) * bRef ^ 8 / (2 * (k : ℝ) + 9))
private def outsideSquareMoment (k : ℕ) : ℝ :=
  bRef ^ (2 * k + 1) *
    ((3000 / 3029 : ℝ) ^ 2 / (2 * (k : ℝ) + 1) -
      2 * (3000 / 3029) * (2449 / 5000) * bRef ^ 2 / (2 * (k : ℝ) + 3) +
      (2449 / 5000) ^ 2 * bRef ^ 4 / (2 * (k : ℝ) + 5) -
      2 * (3000 / 3029) * (1 / 20) * bRef ^ 6 / (2 * (k : ℝ) + 7) +
      (2 * (2449 / 5000) * (1 / 20) - 2 * (3000 / 3029) * (3 / 100)) *
        bRef ^ 8 / (2 * (k : ℝ) + 9) +
      2 * (2449 / 5000) * (3 / 100) * bRef ^ 10 / (2 * (k : ℝ) + 11) +
      (1 / 20) ^ 2 * bRef ^ 12 / (2 * (k : ℝ) + 13) +
      2 * (1 / 20) * (3 / 100) * bRef ^ 14 / (2 * (k : ℝ) + 15) +
      (3 / 100) ^ 2 * bRef ^ 16 / (2 * (k : ℝ) + 17))
private def outsideMoment (k : ℕ) : ℝ :=
  (201 * outsideMomentRaw k - 100 * (3029 / 3000) * outsideSquareMoment k -
    100 * ∑ j ∈ Finset.range 16, outsideSquareMoment (k + j + 1) / (2 * ((j : ℝ) + 1))) / 101
private def cap00 : ℝ := outsideMoment 0 + halfwidth * ∫ t in (0 : ℝ)..1, pair00 t * pairS t
private def cap02 : ℝ := (3 * outsideMoment 1 - outsideMoment 0) / 2 +
  halfwidth * ∫ t in (0 : ℝ)..1, pair02 t * pairS t
private def cap22 : ℝ := (9 * outsideMoment 2 - 6 * outsideMoment 1 + outsideMoment 0) / 4 +
  halfwidth * ∫ t in (0 : ℝ)..1, pair22 t * pairS t
private def cap04 : ℝ := (35 * outsideMoment 2 - 30 * outsideMoment 1 + 3 * outsideMoment 0) / 8 +
  halfwidth * ∫ t in (0 : ℝ)..1, pair04 t * pairS t
private def cap24 : ℝ := (105 * outsideMoment 3 - 125 * outsideMoment 2 +
  39 * outsideMoment 1 - 3 * outsideMoment 0) / 16 +
  halfwidth * ∫ t in (0 : ℝ)..1, pair24 t * pairS t
private def cap44 : ℝ := (1225 * outsideMoment 4 - 2100 * outsideMoment 3 +
  1110 * outsideMoment 2 - 180 * outsideMoment 1 + 9 * outsideMoment 0) / 64 +
  halfwidth * ∫ t in (0 : ℝ)..1, pair44 t * pairS t
private def poleMixedCharge : ℝ :=
  let a : ℝ := 1881 / 5000
  4 * a * (1 + a ^ 2 / 24 + a ^ 4 / 1920) * (a ^ 2 / 12 + a ^ 4 / 672) + a ^ 3 / 24 + a ^ 2 / 72
private def charge0 : ℝ :=
  let a : ℝ := 1881 / 5000
  49 / 20 - 97 / 50000 + a ^ 2 / 24 * (1 / 3 - 5 / 49) + a / 2 - a ^ 2 / 24 - a ^ 3 / 24 - 4 * a * (1 + a ^ 2 / 24 + a ^ 4 / 1920) ^ 2
private def charge2 : ℝ :=
  let a : ℝ := 1881 / 5000
  19 / 4 - 5 * (97 / 50000) - 4 * a * (a ^ 2 / 12 + a ^ 4 / 672) ^ 2
private def chargeDet : ℝ := charge0 * charge2 - poleMixedCharge ^ 2

private def b00 : ℝ := charge2 - chargeDet * (cap00 + 1 / 1000000)
private def b02 : ℝ := poleMixedCharge - chargeDet * cap02
private def b22 : ℝ := charge0 - chargeDet * (cap22 + 1 / 1000000)
private def b04 : ℝ := -chargeDet * cap04
private def b24 : ℝ := -chargeDet * cap24
private def b44 : ℝ := chargeDet * (1 / (33 / 10 - 9 * (97 / 50000)) - cap44 - 1 / 1000000)

private theorem reference_capacity_minors : 0 < b00 ∧ b02 ^ 2 < b00 * b22 ∧
    0 < b00 * (b22 * b44 - b24 ^ 2) - b02 * (b02 * b44 - b24 * b04) +
      b04 * (b02 * b24 - b22 * b04) := by
  unfold b00 b02 b22 b04 b24 b44
  generalize h00 : cap00 = c00
  generalize h02 : cap02 = c02
  generalize h22 : cap22 = c22
  generalize h04 : cap04 = c04
  generalize h24 : cap24 = c24
  generalize h44 : cap44 = c44
  unfold cap00 at h00
  conv at h00 =>
    lhs; rhs; rhs; arg 1; ext t
    dsimp only [pair00, pairS, pairZ, qStrip, firstOverlapEvenStripReciprocal, xp, xm, p2, p4, pairMidpoint, halfwidth, bRef, wRef]
    ring_nf
  unfold cap02 at h02
  conv at h02 =>
    lhs; rhs; rhs; arg 1; ext t
    dsimp only [pair02, pairS, pairZ, qStrip, firstOverlapEvenStripReciprocal, xp, xm, p2, p4, pairMidpoint, halfwidth, bRef, wRef]
    ring_nf
  unfold cap22 at h22
  conv at h22 =>
    lhs; rhs; rhs; arg 1; ext t
    dsimp only [pair22, pairS, pairZ, qStrip, firstOverlapEvenStripReciprocal, xp, xm, p2, p4, pairMidpoint, halfwidth, bRef, wRef]
    ring_nf
  unfold cap04 at h04
  conv at h04 =>
    lhs; rhs; rhs; arg 1; ext t
    dsimp only [pair04, pairS, pairZ, qStrip, firstOverlapEvenStripReciprocal, xp, xm, p2, p4, pairMidpoint, halfwidth, bRef, wRef]
    ring_nf
  unfold cap24 at h24
  conv at h24 =>
    lhs; rhs; rhs; arg 1; ext t
    dsimp only [pair24, pairS, pairZ, qStrip, firstOverlapEvenStripReciprocal, xp, xm, p2, p4, pairMidpoint, halfwidth, bRef, wRef]
    ring_nf
  unfold cap44 at h44
  conv at h44 =>
    lhs; rhs; rhs; arg 1; ext t
    dsimp only [pair44, pairS, pairZ, qStrip, firstOverlapEvenStripReciprocal, xp, xm, p2, p4, pairMidpoint, halfwidth, bRef, wRef]
    ring_nf
  simp (disch := (apply Continuous.intervalIntegrable; fun_prop)) only
    [intervalIntegral.integral_add, intervalIntegral.integral_mul_const,
      intervalIntegral.integral_const, integral_pow] at h00 h02 h22 h04 h24 h44
  generalize hm0 : outsideMoment 0 = m0 at h00 h02 h22 h04 h24 h44
  generalize hm1 : outsideMoment 1 = m1 at h00 h02 h22 h04 h24 h44
  generalize hm2 : outsideMoment 2 = m2 at h00 h02 h22 h04 h24 h44
  generalize hm3 : outsideMoment 3 = m3 at h00 h02 h22 h04 h24 h44
  generalize hm4 : outsideMoment 4 = m4 at h00 h02 h22 h04 h24 h44
  norm_num [outsideMoment, outsideSquareMoment, outsideMomentRaw, Finset.sum_range_succ, bRef] at hm0 hm1 hm2 hm3 hm4
  simp only [← hm0, ← hm1, ← hm2, ← hm3, ← hm4] at h00 h02 h22 h04 h24 h44
  norm_num [halfwidth, bRef] at h00 h02 h22 h04 h24 h44
  rw [← h00, ← h02, ← h22, ← h04, ← h24, ← h44]
  norm_num [chargeDet, charge0, charge2, poleMixedCharge]

private theorem aperture_reflection_bounds :
    (1684993 / 2000000 : ℝ) - 1 / 100000000 ≤ Real.log 2 / (1881 / 5000) - 1 ∧
      Real.log 2 / (1881 / 5000) - 1 ≤ (1684993 / 2000000 : ℝ) := by
  constructor <;> linarith only [Real.log_two_gt_d9, Real.log_two_lt_d9]

private theorem prime_weight_reference_bounds :
    (49013 / 100000 : ℝ) - 1 / 1000000 ≤ Real.log 2 / Real.sqrt 2 ∧
      Real.log 2 / Real.sqrt 2 ≤ (49013 / 100000 : ℝ) := by
  have hl : (141421356 / 100000000 : ℝ) ≤ Real.sqrt 2 := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hu : Real.sqrt 2 ≤ (141421357 / 100000000 : ℝ) := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  constructor
  · apply (le_div_iff₀ (by positivity : (0 : ℝ) < Real.sqrt 2)).mpr
    linarith only [hu, Real.log_two_gt_d9]
  · apply (div_le_iff₀ (by positivity : (0 : ℝ) < Real.sqrt 2)).mpr
    linarith only [hl, Real.log_two_lt_d9]

/-- Rounding leaves a mass floor after the prime-weight error and both analytic losses. -/
private theorem even_mass_budget :
    (3029 / 3000 : ℝ) + 97 / 50000 + 1 / 1000000 + 1 / 50000 ≤
      -14379 / 10000 + 49 / 20 - 5 * (1881 / 5000 : ℝ) ^ 2 / 1176 -
        1 / 50000 + 1 / 6250 := by
  norm_num

private theorem inverse_geometric_bound {z : ℝ} (hz : 0 ≤ z) (hu : z ≤ 1 / 10) :
    1 / (1 - z) ≤ 1 + z + z ^ 2 + 1 / 900 := by
  have hd : 0 < 1 - z := by linarith only [hu]
  have h3 : z ^ 3 ≤ (1 / 10 : ℝ) ^ 3 := pow_le_pow_left₀ hz hu 3
  have ht : z ^ 3 / (1 - z) ≤ 1 / 900 := by
    apply (div_le_iff₀ hd).mpr
    nlinarith only [h3, hu]
  have he : 1 / (1 - z) = 1 + z + z ^ 2 + z ^ 3 / (1 - z) := by
    field_simp [hd.ne']
    ring
  rw [he]
  linarith only [ht]

private theorem paired_numerator_nonneg {q r w p s : ℝ} (hq : 0 < q) (hr : 0 ≤ r)
    (hz : w ^ 2 * q * r ≤ 1) :
    0 ≤ q * p ^ 2 + 2 * w * q * r * p * s + r * s ^ 2 := by
  have he : q * (q * p ^ 2 + 2 * w * q * r * p * s + r * s ^ 2) =
      (q * p + w * q * r * s) ^ 2 + q * r * (1 - w ^ 2 * q * r) * s ^ 2 := by ring
  have hn : 0 ≤ q * (q * p ^ 2 + 2 * w * q * r * p * s + r * s ^ 2) := by
    rw [he]
    exact add_nonneg (sq_nonneg _) (mul_nonneg
      (mul_nonneg (mul_nonneg hq.le hr) (sub_nonneg.mpr hz)) (sq_nonneg _))
  exact nonneg_of_mul_nonneg_right hn hq

/-- A pair retains its mixed source term while its inverse denominator is bounded geometrically. -/
private theorem reflection_pair_young {q r w p s : ℝ} (hq : 0 < q) (hr : 0 < r)
    (hz : w ^ 2 * q * r ≤ 1 / 10) (u v : ℝ) :
    2 * (p * u + s * v) ≤ u ^ 2 / q - 2 * w * u * v + v ^ 2 / r +
      (1 + w ^ 2 * q * r + (w ^ 2 * q * r) ^ 2 + 1 / 900) *
        (q * p ^ 2 + 2 * w * q * r * p * s + r * s ^ 2) := by
  let z := w ^ 2 * q * r
  let N := q * p ^ 2 + 2 * w * q * r * p * s + r * s ^ 2
  have hz0 : 0 ≤ z := by dsimp [z]; positivity
  have hd : 0 < 1 - z := by dsimp [z]; linarith only [hz]
  have hN : 0 ≤ N := paired_numerator_nonneg hq hr.le (by linarith only [hz])
  have hid : q * r * (1 - z) *
      (u ^ 2 / q - 2 * w * u * v + v ^ 2 / r + N / (1 - z) - 2 * (p * u + s * v)) =
      r * (1 - z) * (u - w * q * v - q * p) ^ 2 +
        q * ((1 - z) * v - r * (s + w * q * p)) ^ 2 := by
    field_simp [hq.ne', hr.ne', hd.ne']
    dsimp only [z, N]
    ring
  have hnn : 0 ≤ q * r * (1 - z) *
      (u ^ 2 / q - 2 * w * u * v + v ^ 2 / r + N / (1 - z) - 2 * (p * u + s * v)) := by
    rw [hid]
    positivity
  have hbase := sub_nonneg.mp (nonneg_of_mul_nonneg_right hnn (mul_pos (mul_pos hq hr) hd))
  have hbound := mul_le_mul_of_nonneg_right (inverse_geometric_bound hz0 hz) hN
  change (1 / (1 - z)) * N ≤ (1 + z + z ^ 2 + 1 / 900) * N at hbound
  change 2 * (p * u + s * v) ≤ _ + (1 + z + z ^ 2 + 1 / 900) * N
  have hbound' : N / (1 - z) ≤ (1 + z + z ^ 2 + 1 / 900) * N := by
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using hbound
  exact hbase.trans (add_le_add le_rfl hbound')

/-- Three leading principal minors certify a ternary quadratic form by two square completions. -/
private theorem ternary_quad_nonneg {a b c d e f : ℝ}
    (ha : 0 < a) (hm : 0 < a * c - b ^ 2)
    (hd : 0 ≤ a * (c * f - e ^ 2) - b * (b * f - e * d) + d * (b * e - c * d))
    (x y z : ℝ) :
    0 ≤ a * x ^ 2 + 2 * b * x * y + c * y ^ 2 +
      2 * d * x * z + 2 * e * y * z + f * z ^ 2 := by
  have hid : a * (a * c - b ^ 2) *
      (a * x ^ 2 + 2 * b * x * y + c * y ^ 2 + 2 * d * x * z + 2 * e * y * z + f * z ^ 2) =
      (a * c - b ^ 2) * (a * x + b * y + d * z) ^ 2 +
        ((a * c - b ^ 2) * y + (a * e - b * d) * z) ^ 2 +
        a * (a * (c * f - e ^ 2) - b * (b * f - e * d) + d * (b * e - c * d)) * z ^ 2 := by
    ring
  have hn : 0 ≤ a * (a * c - b ^ 2) *
      (a * x ^ 2 + 2 * b * x * y + c * y ^ 2 + 2 * d * x * z + 2 * e * y * z + f * z ^ 2) := by
    rw [hid]
    positivity
  exact nonneg_of_mul_nonneg_right hn (mul_pos ha hm)

private def referenceCapacityQuad (u v w : ℝ) : ℝ :=
  cap00 * u ^ 2 + 2 * cap02 * u * v + cap22 * v ^ 2 +
    2 * cap04 * u * w + 2 * cap24 * v * w + cap44 * w ^ 2

private theorem chargeDet_pos : 0 < chargeDet := by
  norm_num [chargeDet, charge0, charge2, poleMixedCharge]

/-- The rational capacity lies strictly beneath the inverse charge form. -/
private theorem reference_capacity_quad_le (u v w : ℝ) :
    referenceCapacityQuad u v w + (1 / 1000000) * (u ^ 2 + v ^ 2 + w ^ 2) ≤
      (charge2 * u ^ 2 + 2 * poleMixedCharge * u * v + charge0 * v ^ 2) / chargeDet +
        w ^ 2 / (33 / 10 - 9 * (97 / 50000)) := by
  obtain ⟨h0, h2, h3⟩ := reference_capacity_minors
  have h := ternary_quad_nonneg h0 (sub_pos.mpr h2) h3.le u v w
  have he : b00 * u ^ 2 + 2 * b02 * u * v + b22 * v ^ 2 +
      2 * b04 * u * w + 2 * b24 * v * w + b44 * w ^ 2 =
      chargeDet * ((charge2 * u ^ 2 + 2 * poleMixedCharge * u * v + charge0 * v ^ 2) / chargeDet +
        w ^ 2 / (33 / 10 - 9 * (97 / 50000)) -
          (referenceCapacityQuad u v w + (1 / 1000000) * (u ^ 2 + v ^ 2 + w ^ 2))) := by
    unfold b00 b02 b22 b04 b24 b44 referenceCapacityQuad
    field_simp [chargeDet_pos.ne']
    ring
  rw [he] at h
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right h chargeDet_pos)

/-- Reference capacity of the constant, quadratic and quartic even moments.
The entries retain the rational reflected-pair polynomial integrals. -/
def firstOverlapEvenMomentCapacity (u v w : ℝ) : ℝ :=
  referenceCapacityQuad u v w

/-- The inverse charge form, including the mixed constant/quadratic pole charge. -/
def firstOverlapEvenMomentAllowance (u v w : ℝ) : ℝ :=
  (charge2 * u ^ 2 + 2 * poleMixedCharge * u * v + charge0 * v ^ 2) / chargeDet +
    w ^ 2 / (33 / 10 - 9 * (97 / 50000))

/-- A reusable exact Gram certificate: all three even moments retain a margin of `10⁻⁶`.
The principal minors and polynomial integrals are proved above; no numerical or
analytic certificate premise remains. -/
theorem firstOverlapEvenMomentCapacity_certificate (u v w : ℝ) :
    firstOverlapEvenMomentCapacity u v w + (1 / 1000000) * (u ^ 2 + v ^ 2 + w ^ 2) ≤
      firstOverlapEvenMomentAllowance u v w :=
  reference_capacity_quad_le u v w

/-- The reference capacity is strictly below its allowance for every nonzero moment triple. -/
theorem firstOverlapEvenMomentCapacity_lt_iff (u v w : ℝ) :
    firstOverlapEvenMomentCapacity u v w < firstOverlapEvenMomentAllowance u v w ↔
      u ≠ 0 ∨ v ≠ 0 ∨ w ≠ 0 := by
  constructor
  · intro h
    by_contra hz
    push Not at hz
    rcases hz with ⟨rfl, rfl, rfl⟩
    norm_num [firstOverlapEvenMomentCapacity, firstOverlapEvenMomentAllowance,
      referenceCapacityQuad] at h
  · intro h
    have hmass : 0 < u ^ 2 + v ^ 2 + w ^ 2 := by
      by_contra hm
      have hm' : u ^ 2 + v ^ 2 + w ^ 2 ≤ 0 := le_of_not_gt hm
      rcases h with hu | hv | hw
      · exact hu (by nlinarith only [hm', sq_nonneg v, sq_nonneg w])
      · exact hv (by nlinarith only [hm', sq_nonneg u, sq_nonneg w])
      · exact hw (by nlinarith only [hm', sq_nonneg u, sq_nonneg v])
    have hmargin : 0 < (1 / 1000000 : ℝ) * (u ^ 2 + v ^ 2 + w ^ 2) :=
      mul_pos (by norm_num) hmass
    linarith only [firstOverlapEvenMomentCapacity_certificate u v w, hmargin]

#print axioms firstOverlapEvenMomentCapacity_certificate
#print axioms firstOverlapEvenMomentCapacity_lt_iff

private def source (u v w x : ℝ) : ℝ :=
  u + v * ((3 * x ^ 2 - 1) / 2) + w * ((35 * x ^ 4 - 30 * x ^ 2 + 3) / 8)
private def sourceD (v w x : ℝ) : ℝ :=
  v * (3 * x) + w * ((35 * x ^ 3 - 15 * x) / 2)
private def qStripD (x : ℝ) : ℝ :=
  -21 / 20 - (36 / 5) * (x - 337 / 400) -
    300 * (x - 337 / 400) * (x - 23 / 25) ^ 2 -
    300 * (x - 337 / 400) ^ 2 * (x - 23 / 25)

private theorem source_sq_bound (u v w : ℝ) {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    source u v w x ^ 2 ≤ 3 * (u ^ 2 + v ^ 2 + w ^ 2) := by
  have hx2 : x ^ 2 ≤ 1 := by nlinarith only [hx, hx1]
  let P := (3 * x ^ 2 - 1) / 2
  let Q := (35 * x ^ 4 - 30 * x ^ 2 + 3) / 8
  have hP : P ^ 2 ≤ 1 := by
    have hl : -1 ≤ P := by dsimp [P]; nlinarith only [sq_nonneg x]
    have hu : P ≤ 1 := by dsimp [P]; linarith only [hx2]
    nlinarith only [hl, hu]
  have hQ : Q ^ 2 ≤ 1 := by
    have hl : -1 ≤ Q := by
      dsimp [Q]
      nlinarith only [sq_nonneg (x ^ 2 - 3 / 7)]
    have hu : Q ≤ 1 := by
      have hp := mul_nonneg (sub_nonneg.mpr hx2)
        (show 0 ≤ 7 * x ^ 2 + 1 by positivity)
      dsimp [Q]
      nlinarith only [hp]
    nlinarith only [hl, hu]
  have hv := mul_le_mul_of_nonneg_left hP (sq_nonneg v)
  have hw := mul_le_mul_of_nonneg_left hQ (sq_nonneg w)
  change (u + v * P + w * Q) ^ 2 ≤ _
  nlinarith only [hv, hw, sq_nonneg (u - v * P),
    sq_nonneg (u - w * Q), sq_nonneg (v * P - w * Q)]

private theorem sourceD_sq_bound (u v w : ℝ) {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    sourceD v w x ^ 2 ≤ 109 * (u ^ 2 + v ^ 2 + w ^ 2) := by
  have hx2 : x ^ 2 ≤ 1 := by nlinarith only [hx, hx1]
  have hx3 : x ^ 3 ≤ x := by
    have h := mul_le_mul_of_nonneg_right hx2 hx
    nlinarith only [h]
  let P := 3 * x
  let Q := (35 * x ^ 3 - 15 * x) / 2
  have hP : P ^ 2 ≤ 9 := by dsimp [P]; nlinarith only [hx2]
  have hQ : Q ^ 2 ≤ 100 := by
    have hl : -10 ≤ Q := by dsimp [Q]; nlinarith only [hx1, pow_nonneg hx 3]
    have hu : Q ≤ 10 := by dsimp [Q]; linarith only [hx3, hx1]
    nlinarith only [hl, hu]
  have hPQ : P ^ 2 + Q ^ 2 ≤ 109 := by linarith only [hP, hQ]
  have hprod := mul_le_mul_of_nonneg_left hPQ (add_nonneg (sq_nonneg v) (sq_nonneg w))
  change (v * P + w * Q) ^ 2 ≤ _
  nlinarith only [hprod, sq_nonneg (v * Q - w * P), sq_nonneg u]

private theorem qStrip_bounds {x : ℝ} (hx : 84249 / 100000 ≤ x) (hx1 : x ≤ 1) :
    (1 / 3 : ℝ) ≤ qStrip x ∧ qStrip x ≤ 31 / 50 :=
  firstOverlapEvenStripReciprocal_range hx hx1

private theorem qStripD_bound {x : ℝ} (hx : 84249 / 100000 ≤ x) (hx1 : x ≤ 1) :
    |qStripD x| ≤ 31 / 10 := by
  let d := x - 337 / 400
  let y := x - 23 / 25
  have hd : |d| ≤ 63 / 400 := by
    rw [abs_le]
    dsimp [d]
    constructor <;> linarith only [hx, hx1]
  have hy : |y| ≤ 2 / 25 := by
    rw [abs_le]
    dsimp [y]
    constructor <;> linarith only [hx, hx1]
  have hd2 := pow_le_pow_left₀ (abs_nonneg d) hd 2
  have hy2 := pow_le_pow_left₀ (abs_nonneg y) hy 2
  have hprod1 := mul_le_mul hd hy2 (sq_nonneg |y|) (by norm_num : (0 : ℝ) ≤ 63 / 400)
  have hprod2 := mul_le_mul hd2 hy (abs_nonneg y) (by norm_num : (0 : ℝ) ≤ (63 / 400 : ℝ) ^ 2)
  have htri : |qStripD x| ≤ 21 / 20 + (36 / 5) * |d| +
      300 * |d| * |y| ^ 2 + 300 * |d| ^ 2 * |y| := by
    change |-21 / 20 - (36 / 5) * d - 300 * d * y ^ 2 - 300 * d ^ 2 * y| ≤ _
    calc
      _ ≤ |(-21 / 20 : ℝ) - (36 / 5) * d - 300 * d * y ^ 2| + |300 * d ^ 2 * y| := abs_sub _ _
      _ ≤ (|(-21 / 20 : ℝ) - (36 / 5) * d| + |300 * d * y ^ 2|) + |300 * d ^ 2 * y| :=
        add_le_add (abs_sub _ _) le_rfl
      _ ≤ ((|(-21 / 20 : ℝ)| + |(36 / 5) * d|) + |300 * d * y ^ 2|) + |300 * d ^ 2 * y| :=
        add_le_add (add_le_add (abs_sub _ _) le_rfl) le_rfl
      _ = _ := by simp only [abs_mul, abs_pow]; norm_num
  nlinarith only [htri, hd, hprod1, hprod2]

private theorem hasDerivAt_source (u v w x : ℝ) :
    HasDerivAt (source u v w) (sourceD v w x) x := by
  have h2 := ((hasDerivAt_id x).pow 2).const_mul 3 |>.sub_const 1 |>.div_const 2
  have h4 := ((((hasDerivAt_id x).pow 4).const_mul 35).sub
    (((hasDerivAt_id x).pow 2).const_mul 30)).add_const 3 |>.div_const 8
  exact (((hasDerivAt_const x u).add (h2.const_mul v)).add (h4.const_mul w)).congr_deriv
    (by simp only [id_eq]; dsimp [sourceD]; ring)

private theorem hasDerivAt_qStrip (x : ℝ) : HasDerivAt qStrip (qStripD x) x := by
  have hd := (hasDerivAt_id x).sub_const (337 / 400)
  have hy := (hasDerivAt_id x).sub_const (23 / 25)
  exact ((((hasDerivAt_const x (309 / 500)).sub (hd.const_mul (21 / 20))).sub
    ((hd.pow 2).const_mul (18 / 5))).sub
      ((((hd.pow 2).const_mul 150).mul (hy.pow 2)))).congr_deriv
        (by simp only [Pi.pow_apply, id_eq]; dsimp [qStripD]; ring)

private theorem source_cross_bound (u v w : ℝ) {x y : ℝ}
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (hy : 0 ≤ y) (hy1 : y ≤ 1) :
    |source u v w x * source u v w y| ≤ 3 * (u ^ 2 + v ^ 2 + w ^ 2) := by
  have h1 := source_sq_bound u v w hx hx1
  have h2 := source_sq_bound u v w hy hy1
  rw [abs_le]
  constructor
  · nlinarith only [h1, h2, sq_nonneg (source u v w x + source u v w y)]
  · nlinarith only [h1, h2, sq_nonneg (source u v w x - source u v w y)]

private theorem source_deriv_cross_bound (u v w : ℝ) {x y : ℝ}
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (hy : 0 ≤ y) (hy1 : y ≤ 1) :
    |source u v w x * sourceD v w y| ≤ (217 / 12 : ℝ) * (u ^ 2 + v ^ 2 + w ^ 2) := by
  have h1 := source_sq_bound u v w hx hx1
  have h2 := sourceD_sq_bound u v w hy hy1
  rw [abs_le]
  constructor
  · nlinarith only [h1, h2, sq_nonneg (6 * source u v w x + sourceD v w y)]
  · nlinarith only [h1, h2, sq_nonneg (6 * source u v w x - sourceD v w y)]

private def pairNumerator (w q r p s : ℝ) : ℝ :=
  q * p ^ 2 + (2 * w * q * r) * (p * s) + r * s ^ 2
private def pairNumeratorD (w q r r' p s s' : ℝ) : ℝ :=
  2 * w * q * (r' * (p * s) + r * (p * s')) + r' * s ^ 2 + 2 * r * (s * s')

private theorem pairNumerator_abs_bound {w q r p s M : ℝ}
    (hM : 0 ≤ M) (hw0 : 0 ≤ w) (hw : w ≤ 1 / 2)
    (hq0 : 0 ≤ q) (hq : q ≤ 31 / 50) (hr0 : 0 ≤ r) (hr : r ≤ 31 / 50)
    (hp : p ^ 2 ≤ 3 * M) (hs : s ^ 2 ≤ 3 * M) (hps : |p * s| ≤ 3 * M) :
    |pairNumerator w q r p s| ≤ 5 * M := by
  have hqr0 : 0 ≤ 2 * w * q * r := by positivity
  have hqr : 2 * w * q * r ≤ (31 / 50 : ℝ) ^ 2 := by
    have h1 := mul_le_mul hq hr hr0 (by norm_num : (0 : ℝ) ≤ 31 / 50)
    have h2 := mul_le_mul (show 2 * w ≤ 1 by linarith only [hw]) h1
      (mul_nonneg hq0 hr0) zero_le_one
    nlinarith only [h2]
  have h1 := mul_le_mul hq hp (sq_nonneg p) (by norm_num : (0 : ℝ) ≤ 31 / 50)
  have h2 := mul_le_mul hr hs (sq_nonneg s) (by norm_num : (0 : ℝ) ≤ 31 / 50)
  have h3 := mul_le_mul hqr hps (abs_nonneg (p * s)) (by positivity : (0 : ℝ) ≤ (31 / 50 : ℝ) ^ 2)
  have ht : |pairNumerator w q r p s| ≤
      q * p ^ 2 + (2 * w * q * r) * |p * s| + r * s ^ 2 := by
    unfold pairNumerator
    calc
      _ ≤ |q * p ^ 2 + (2 * w * q * r) * (p * s)| + |r * s ^ 2| := abs_add_le _ _
      _ ≤ (|q * p ^ 2| + |(2 * w * q * r) * (p * s)|) + |r * s ^ 2| :=
        add_le_add (abs_add_le _ _) le_rfl
      _ = _ := by
        rw [abs_mul (2 * w * q * r), abs_of_nonneg hqr0,
          abs_of_nonneg (mul_nonneg hq0 (sq_nonneg p)),
          abs_of_nonneg (mul_nonneg hr0 (sq_nonneg s))]
  nlinarith only [ht, h1, h2, h3, hM]

private theorem pairNumeratorD_abs_bound {w q r r' p s s' M : ℝ}
    (hM : 0 ≤ M) (hw0 : 0 ≤ w) (hw : w ≤ 1 / 2)
    (hq0 : 0 ≤ q) (hq : q ≤ 31 / 50) (hr0 : 0 ≤ r) (hr : r ≤ 31 / 50)
    (hr' : |r'| ≤ 31 / 10) (hs : s ^ 2 ≤ 3 * M) (hps : |p * s| ≤ 3 * M)
    (hps' : |p * s'| ≤ (217 / 12) * M) (hss' : |s * s'| ≤ (217 / 12) * M) :
    |pairNumeratorD w q r r' p s s'| ≤ 45 * M := by
  have hc0 : 0 ≤ 2 * w * q := by positivity
  have hc : 2 * w * q ≤ 31 / 50 := by
    have h := mul_le_mul (show 2 * w ≤ 1 by linarith only [hw]) hq hq0 zero_le_one
    nlinarith only [h]
  have h1 : |r' * (p * s)| ≤ (31 / 10) * (3 * M) := by
    rw [abs_mul]
    exact mul_le_mul hr' hps (abs_nonneg _) (by norm_num)
  have h2 : |r * (p * s')| ≤ (31 / 50) * ((217 / 12) * M) := by
    rw [abs_mul, abs_of_nonneg hr0]
    exact mul_le_mul hr hps' (abs_nonneg _) (by norm_num)
  have h3 : |r' * s ^ 2| ≤ (31 / 10) * (3 * M) := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg s)]
    exact mul_le_mul hr' hs (sq_nonneg s) (by norm_num)
  have h4 : |2 * r * (s * s')| ≤ (2 * (31 / 50)) * ((217 / 12) * M) := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * r)]
    exact mul_le_mul (by linarith only [hr]) hss' (abs_nonneg _) (by norm_num)
  have hab : |r' * (p * s) + r * (p * s')| ≤
      (31 / 10) * (3 * M) + (31 / 50) * ((217 / 12) * M) :=
    (abs_add_le _ _).trans (add_le_add h1 h2)
  have h5 : |2 * w * q * (r' * (p * s) + r * (p * s'))| ≤
      (31 / 50) * ((31 / 10) * (3 * M) + (31 / 50) * ((217 / 12) * M)) := by
    rw [abs_mul, abs_of_nonneg hc0]
    exact mul_le_mul hc hab (abs_nonneg _) (by norm_num)
  have ht : |pairNumeratorD w q r r' p s s'| ≤
      |2 * w * q * (r' * (p * s) + r * (p * s'))| + |r' * s ^ 2| + |2 * r * (s * s')| := by
    unfold pairNumeratorD
    exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
  nlinarith only [ht, h3, h4, h5, hM]

private def pairGeom (w q r : ℝ) : ℝ :=
  1 + w ^ 2 * q * r + (w ^ 2 * q * r) ^ 2 + 1 / 900
private def pairGeomD (w q r r' : ℝ) : ℝ :=
  (1 + 2 * w ^ 2 * q * r) * (w ^ 2 * q * r')

private theorem pairGeom_bounds {w q r : ℝ}
    (hw0 : 0 ≤ w) (hw : w ≤ 1 / 2)
    (hq0 : 0 ≤ q) (hq : q ≤ 31 / 50) (hr0 : 0 ≤ r) (hr : r ≤ 31 / 50) :
    0 ≤ w ^ 2 * q * r ∧ w ^ 2 * q * r ≤ 1 / 10 ∧
      0 ≤ pairGeom w q r ∧ pairGeom w q r ≤ 10 / 9 := by
  have hw2 : w ^ 2 ≤ 1 / 4 := by nlinarith only [hw0, hw]
  have hqr := mul_le_mul hq hr hr0 (by norm_num : (0 : ℝ) ≤ 31 / 50)
  have hz := mul_le_mul hw2 hqr (mul_nonneg hq0 hr0) (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hz0 : 0 ≤ w ^ 2 * q * r := by positivity
  have hz1 : w ^ 2 * q * r ≤ 1 / 10 := by nlinarith only [hz]
  have hz2 := pow_le_pow_left₀ hz0 hz1 2
  refine ⟨hz0, hz1, ?_, ?_⟩
  · unfold pairGeom
    positivity
  · unfold pairGeom
    nlinarith only [hz1, hz2]

private theorem pairGeomD_abs_bound {w q r r' : ℝ}
    (hw0 : 0 ≤ w) (hw : w ≤ 1 / 2)
    (hq0 : 0 ≤ q) (hq : q ≤ 31 / 50) (hr0 : 0 ≤ r) (hr : r ≤ 31 / 50)
    (hr' : |r'| ≤ 31 / 10) : |pairGeomD w q r r'| ≤ 3 / 5 := by
  obtain ⟨hz0, hz1, _, _⟩ := pairGeom_bounds hw0 hw hq0 hq hr0 hr
  have hw2 : w ^ 2 ≤ 1 / 4 := by nlinarith only [hw0, hw]
  have hwq := mul_le_mul hw2 hq hq0 (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hprod := mul_le_mul hwq hr' (abs_nonneg r') (by norm_num : (0 : ℝ) ≤ (1 / 4) * (31 / 50))
  have hlead : 1 + 2 * w ^ 2 * q * r ≤ 6 / 5 := by linarith only [hz1]
  have hlead0 : 0 ≤ 1 + 2 * w ^ 2 * q * r := by nlinarith only [hz0]
  have h := mul_le_mul hlead hprod (by positivity : 0 ≤ w ^ 2 * q * |r'|)
    (by norm_num : (0 : ℝ) ≤ 6 / 5)
  unfold pairGeomD
  rw [abs_mul, abs_of_nonneg hlead0, abs_mul, abs_of_nonneg (by positivity : 0 ≤ w ^ 2 * q)]
  nlinarith only [h]

private def pairIntegrand (u v w x y : ℝ) : ℝ :=
  pairGeom wRef (qStrip x) (qStrip y) *
    pairNumerator wRef (qStrip x) (qStrip y) (source u v w x) (source u v w y)
private def pairIntegrandD (u v w x y : ℝ) : ℝ :=
  pairGeomD wRef (qStrip x) (qStrip y) (qStripD y) *
      pairNumerator wRef (qStrip x) (qStrip y) (source u v w x) (source u v w y) +
    pairGeom wRef (qStrip x) (qStrip y) *
      pairNumeratorD wRef (qStrip x) (qStrip y) (qStripD y)
        (source u v w x) (source u v w y) (sourceD v w y)

private theorem pairIntegrand_bounds (u v w : ℝ) {x y : ℝ}
    (hx : 84249 / 100000 ≤ x) (hx1 : x ≤ 1)
    (hy : 84249 / 100000 ≤ y) (hy1 : y ≤ 1) :
    |pairIntegrand u v w x y| ≤ 6 * (u ^ 2 + v ^ 2 + w ^ 2) ∧
      |pairIntegrandD u v w x y| ≤ 53 * (u ^ 2 + v ^ 2 + w ^ 2) := by
  let M := u ^ 2 + v ^ 2 + w ^ 2
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hx0 : 0 ≤ x := by linarith only [hx]
  have hy0 : 0 ≤ y := by linarith only [hy]
  obtain ⟨hqx, hqx1⟩ := qStrip_bounds hx hx1
  obtain ⟨hqy, hqy1⟩ := qStrip_bounds hy hy1
  have hqx0 : 0 ≤ qStrip x := by linarith only [hqx]
  have hqy0 : 0 ≤ qStrip y := by linarith only [hqy]
  have hw0 : 0 ≤ wRef := by norm_num [wRef]
  have hw1 : wRef ≤ 1 / 2 := by norm_num [wRef]
  have hN := pairNumerator_abs_bound hM hw0 hw1 hqx0 hqx1 hqy0 hqy1
    (source_sq_bound u v w hx0 hx1) (source_sq_bound u v w hy0 hy1)
    (source_cross_bound u v w hx0 hx1 hy0 hy1)
  have hND := pairNumeratorD_abs_bound hM hw0 hw1 hqx0 hqx1 hqy0 hqy1
    (qStripD_bound hy hy1) (source_sq_bound u v w hy0 hy1)
    (source_cross_bound u v w hx0 hx1 hy0 hy1)
    (source_deriv_cross_bound u v w hx0 hx1 hy0 hy1)
    (source_deriv_cross_bound u v w hy0 hy1 hy0 hy1)
  obtain ⟨_, _, hS0, hS⟩ := pairGeom_bounds hw0 hw1 hqx0 hqx1 hqy0 hqy1
  have hSD := pairGeomD_abs_bound hw0 hw1 hqx0 hqx1 hqy0 hqy1 (qStripD_bound hy hy1)
  have hSN := mul_le_mul hS hN (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 10 / 9)
  have hSDN := mul_le_mul hSD hN (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 3 / 5)
  have hSND := mul_le_mul hS hND (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 10 / 9)
  constructor
  · unfold pairIntegrand
    rw [abs_mul, abs_of_nonneg hS0]
    nlinarith only [hSN, hM]
  · have ht := abs_add_le
      (pairGeomD wRef (qStrip x) (qStrip y) (qStripD y) *
        pairNumerator wRef (qStrip x) (qStrip y) (source u v w x) (source u v w y))
      (pairGeom wRef (qStrip x) (qStrip y) *
        pairNumeratorD wRef (qStrip x) (qStrip y) (qStripD y)
          (source u v w x) (source u v w y) (sourceD v w y))
    rw [abs_mul, abs_mul, abs_of_nonneg hS0] at ht
    change |pairIntegrandD u v w x y| ≤ _ at ht
    nlinarith only [ht, hSDN, hSND]

private theorem hasDerivAt_pairIntegrand (u v w x y : ℝ) :
    HasDerivAt (pairIntegrand u v w x) (pairIntegrandD u v w x y) y := by
  have hr := hasDerivAt_qStrip y
  have hs := hasDerivAt_source u v w y
  have hz := hr.const_mul (wRef ^ 2 * qStrip x)
  have hS := (((hasDerivAt_const y 1).add hz).add (hz.pow 2)).add_const (1 / 900)
  have hN := (((hs.pow 2).mul hr).add
      ((hr.mul hs).const_mul (2 * wRef * qStrip x * source u v w x))).add_const
        (qStrip x * source u v w x ^ 2)
  have hS' : HasDerivAt (fun t => pairGeom wRef (qStrip x) (qStrip t))
      (pairGeomD wRef (qStrip x) (qStrip y) (qStripD y)) y := by
    refine (hS.congr_deriv ?_).congr_of_eventuallyEq ?_
    · dsimp only [pairGeomD]
      ring
    · exact Eventually.of_forall fun t => by
        simp only [pairGeom, Pi.add_apply, Pi.pow_apply]
  have hN' : HasDerivAt
      (fun t => pairNumerator wRef (qStrip x) (qStrip t) (source u v w x) (source u v w t))
      (pairNumeratorD wRef (qStrip x) (qStrip y) (qStripD y)
        (source u v w x) (source u v w y) (sourceD v w y)) y := by
    refine (hN.congr_deriv ?_).congr_of_eventuallyEq ?_
    · simp only [Pi.pow_apply]
      dsimp only [pairNumeratorD]
      ring
    · exact Eventually.of_forall fun t => by
        simp only [pairNumerator, Pi.add_apply, Pi.mul_apply, Pi.pow_apply]
        ring
  exact hS'.mul hN'

private theorem pairIntegrand_lipschitz (u v w : ℝ) {x y₁ y₂ : ℝ}
    (hx : 84249 / 100000 ≤ x) (hx1 : x ≤ 1)
    (hy₁ : y₁ ∈ Icc (84249 / 100000 : ℝ) 1)
    (hy₂ : y₂ ∈ Icc (84249 / 100000 : ℝ) 1) :
    |pairIntegrand u v w x y₂ - pairIntegrand u v w x y₁| ≤
      53 * (u ^ 2 + v ^ 2 + w ^ 2) * |y₂ - y₁| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := pairIntegrand u v w x) (f' := pairIntegrandD u v w x)
    (s := Icc (84249 / 100000 : ℝ) 1)
    (fun y _ => (hasDerivAt_pairIntegrand u v w x y).hasDerivWithinAt)
    (fun y hy => by
      rw [Real.norm_eq_abs]
      exact (pairIntegrand_bounds u v w hx hx1 hy.1 hy.2).2)
    (convex_Icc _ _) hy₁ hy₂
  simpa only [Real.norm_eq_abs] using h

private def capacity (b u v w : ℝ) : ℝ :=
  (∫ x in (0 : ℝ)..b, firstOverlapEvenOutsideReciprocal x * source u v w x ^ 2) +
    (1 / 2) * ∫ x in b..1, pairIntegrand u v w x (b + 1 - x)

private def capacityOutsidePotential (x : ℝ) : ℝ :=
  (3029 / 3000 : ℝ) +
    x ^ 1 / 2 +
    x ^ 2 / 4 +
    x ^ 3 / 6 +
    x ^ 4 / 8 +
    x ^ 5 / 10 +
    x ^ 6 / 12 +
    x ^ 7 / 14 +
    x ^ 8 / 16 +
    x ^ 9 / 18 +
    x ^ 10 / 20 +
    x ^ 11 / 22 +
    x ^ 12 / 24 +
    x ^ 13 / 26 +
    x ^ 14 / 28 +
    x ^ 15 / 30 +
    x ^ 16 / 32

private def capacityOutsideRaw (x : ℝ) : ℝ :=
  3000 / 3029 - (2449 / 5000) * x - x ^ 3 / 20 - 3 * x ^ 4 / 100


private theorem outsideReciprocal_expression (x : ℝ) :
    firstOverlapEvenOutsideReciprocal x =
      capacityOutsideRaw (x ^ 2) *
        (201 - 100 * capacityOutsidePotential (x ^ 2) * capacityOutsideRaw (x ^ 2)) / 101 := rfl

private theorem continuous_outsideReciprocal : Continuous firstOverlapEvenOutsideReciprocal := by
  rw [show firstOverlapEvenOutsideReciprocal = (fun x =>
    capacityOutsideRaw (x ^ 2) *
      (201 - 100 * capacityOutsidePotential (x ^ 2) * capacityOutsideRaw (x ^ 2)) / 101)
    from funext outsideReciprocal_expression]
  dsimp only [capacityOutsideRaw, capacityOutsidePotential]
  fun_prop

private theorem continuous_capacity_outside (u v w : ℝ) :
    Continuous (fun x => firstOverlapEvenOutsideReciprocal x * source u v w x ^ 2) := by
  exact continuous_outsideReciprocal.mul ((show Continuous (source u v w) from by
    unfold source
    fun_prop).pow 2)

private theorem continuous_capacity_pair (b u v w : ℝ) :
    Continuous (fun x => pairIntegrand u v w x (b + 1 - x)) := by
  unfold pairIntegrand pairGeom pairNumerator qStrip firstOverlapEvenStripReciprocal source
  fun_prop

/-- Only the finite moment capacities vary with the reflected strip endpoint. -/
private theorem capacity_le_reference {b : ℝ}
    (hb : bRef - 1 / 100000000 ≤ b) (hbRef : b ≤ bRef) (u v w : ℝ) :
    capacity b u v w ≤ capacity bRef u v w +
      (1 / 10000000) * (u ^ 2 + v ^ 2 + w ^ 2) := by
  let M := u ^ 2 + v ^ 2 + w ^ 2
  let O := fun x => firstOverlapEvenOutsideReciprocal x * source u v w x ^ 2
  let J := fun d x => pairIntegrand u v w x (d + 1 - x)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hbmin : 84249 / 100000 ≤ b := by dsimp [bRef] at hb; linarith only [hb]
  have hb0 : 0 ≤ b := by linarith only [hbmin]
  have hb1 : b ≤ 1 := by dsimp [bRef] at hbRef; linarith only [hbRef]
  have hr0 : 0 ≤ bRef := by norm_num [bRef]
  have hr1 : bRef ≤ 1 := by norm_num [bRef]
  have hδ : (bRef - b) * M ≤ (1 / 100000000) * M :=
    mul_le_mul_of_nonneg_right (by linarith only [hb]) hM
  have hO : Continuous O := continuous_capacity_outside u v w
  have hJ (d : ℝ) : Continuous (J d) := continuous_capacity_pair d u v w
  have hOs := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hO.intervalIntegrable 0 b) (hO.intervalIntegrable b bRef)
  have hOn : 0 ≤ ∫ x in b..bRef, O x := by
    apply intervalIntegral.integral_nonneg hbRef
    intro x hx
    have hx0 : 0 ≤ x := hb0.trans hx.1
    have hx1 : x ≤ 337 / 400 := hx.2.trans (by norm_num [bRef])
    exact mul_nonneg (firstOverlapEvenOutsideReciprocal_bound hx0 hx1).1.le (sq_nonneg _)
  have hshort : (∫ x in b..bRef, J b x) ≤ (bRef - b) * (6 * M) := by
    have h := intervalIntegral.integral_mono_on (μ := volume) hbRef
      ((hJ b).intervalIntegrable b bRef) (continuous_const.intervalIntegrable b bRef)
      (show ∀ x ∈ Icc b bRef, J b x ≤ 6 * M from by
        intro x hx
        have h := (pairIntegrand_bounds u v w (y := b + 1 - x) (hbmin.trans hx.1) (hx.2.trans hr1)
          (by linarith only [hbmin, hx.2, hr1]) (by linarith only [hx.1])).1
        exact (le_abs_self _).trans h)
    simpa only [intervalIntegral.integral_const, smul_eq_mul] using h
  have hlong : (∫ x in bRef..1, J b x) ≤ (∫ x in bRef..1, J bRef x) +
      (1 - bRef) * (53 * M * (bRef - b)) := by
    have h := intervalIntegral.integral_mono_on (μ := volume) hr1
      ((hJ b).intervalIntegrable bRef 1)
      (((hJ bRef).intervalIntegrable bRef 1).add (continuous_const.intervalIntegrable bRef 1))
      (show ∀ x ∈ Icc bRef 1, J b x ≤ J bRef x + 53 * M * (bRef - b) from by
        intro x hx
        have hy₁ : bRef + 1 - x ∈ Icc (84249 / 100000 : ℝ) 1 := by
          constructor
          · have hbr : (84249 / 100000 : ℝ) ≤ bRef := by norm_num [bRef]
            linarith only [hbr, hx.2]
          · linarith only [hx.1]
        have hy₂ : b + 1 - x ∈ Icc (84249 / 100000 : ℝ) 1 := by
          constructor <;> linarith only [hbmin, hbRef, hx.1, hx.2]
        have hl := pairIntegrand_lipschitz u v w
          (hbmin.trans (hbRef.trans hx.1)) hx.2 hy₁ hy₂
        rw [show (b + 1 - x) - (bRef + 1 - x) = -(bRef - b) by ring,
          abs_neg, abs_of_nonneg (sub_nonneg.mpr hbRef)] at hl
        have hu := (abs_le.mp hl).2
        change J b x - J bRef x ≤ 53 * M * (bRef - b) at hu
        linarith only [hu])
    rw [intervalIntegral.integral_add
      ((hJ bRef).intervalIntegrable bRef 1) (continuous_const.intervalIntegrable bRef 1),
      intervalIntegral.integral_const, smul_eq_mul] at h
    exact h
  have hJs := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    ((hJ b).intervalIntegrable b bRef) ((hJ b).intervalIntegrable bRef 1)
  change (∫ x in (0 : ℝ)..b, O x) + (1 / 2) * (∫ x in b..1, J b x) ≤
    (∫ x in (0 : ℝ)..bRef, O x) + (1 / 2) * (∫ x in bRef..1, J bRef x) + (1 / 10000000) * M
  have hlen : (1 - bRef) * 53 ≤ 9 := by norm_num [bRef]
  have hlenM := mul_le_mul_of_nonneg_right hlen
    (mul_nonneg hM (sub_nonneg.mpr hbRef))
  have hlong' : (∫ x in bRef..1, J b x) ≤ (∫ x in bRef..1, J bRef x) +
      9 * M * (bRef - b) := by nlinarith only [hlong, hlenM]
  nlinarith only [hOs, hOn, hshort, hlong', hJs, hδ, hM]

private theorem outsideMoment_integral (k : Fin 5) :
    (∫ x in (0 : ℝ)..bRef, firstOverlapEvenOutsideReciprocal x * x ^ (2 * (k : ℕ))) =
      outsideMoment k := by
  fin_cases k
  all_goals
    conv_lhs =>
      arg 1; ext x
      rw [outsideReciprocal_expression]
      dsimp only [capacityOutsideRaw, capacityOutsidePotential]
      ring_nf
    simp (disch := (apply Continuous.intervalIntegrable; fun_prop)) only
      [intervalIntegral.integral_add, intervalIntegral.integral_mul_const,
        intervalIntegral.integral_const, integral_pow]
    norm_num [outsideMoment, outsideMomentRaw, outsideSquareMoment, Finset.sum_range_succ, bRef]

private theorem outside_source_integral (u v w : ℝ) :
    (∫ x in (0 : ℝ)..bRef, firstOverlapEvenOutsideReciprocal x * source u v w x ^ 2) =
      outsideMoment 0 * u ^ 2 + (3 * outsideMoment 1 - outsideMoment 0) * u * v +
      ((9 * outsideMoment 2 - 6 * outsideMoment 1 + outsideMoment 0) / 4) * v ^ 2 +
      ((35 * outsideMoment 2 - 30 * outsideMoment 1 + 3 * outsideMoment 0) / 4) * u * w +
      ((105 * outsideMoment 3 - 125 * outsideMoment 2 + 39 * outsideMoment 1 - 3 * outsideMoment 0) / 8) * v * w +
      ((1225 * outsideMoment 4 - 2100 * outsideMoment 3 + 1110 * outsideMoment 2 -
        180 * outsideMoment 1 + 9 * outsideMoment 0) / 64) * w ^ 2 := by
  let q := firstOverlapEvenOutsideReciprocal
  have hq : Continuous q := continuous_outsideReciprocal
  have he : (fun x => q x * source u v w x ^ 2) = fun x =>
      u ^ 2 * q x + u * v * (3 * (q x * x ^ 2) - q x) +
      (v ^ 2 / 4) * (9 * (q x * x ^ 4) - 6 * (q x * x ^ 2) + q x) +
      (u * w / 4) * (35 * (q x * x ^ 4) - 30 * (q x * x ^ 2) + 3 * q x) +
      (v * w / 8) * (105 * (q x * x ^ 6) - 125 * (q x * x ^ 4) + 39 * (q x * x ^ 2) - 3 * q x) +
      (w ^ 2 / 64) * (1225 * (q x * x ^ 8) - 2100 * (q x * x ^ 6) +
        1110 * (q x * x ^ 4) - 180 * (q x * x ^ 2) + 9 * q x) := by
    funext x
    dsimp [source]
    ring
  have h0 : (∫ x in (0 : ℝ)..bRef, q x) = outsideMoment 0 := by
    simpa only [Fin.val_zero, mul_zero, pow_zero, mul_one] using outsideMoment_integral 0
  have h1 : (∫ x in (0 : ℝ)..bRef, q x * x ^ 2) = outsideMoment 1 := by
    simpa using outsideMoment_integral 1
  have h2 : (∫ x in (0 : ℝ)..bRef, q x * x ^ 4) = outsideMoment 2 := by
    simpa using outsideMoment_integral 2
  have h3 : (∫ x in (0 : ℝ)..bRef, q x * x ^ 6) = outsideMoment 3 := by
    simpa using outsideMoment_integral 3
  have h4 : (∫ x in (0 : ℝ)..bRef, q x * x ^ 8) = outsideMoment 4 := by
    simpa using outsideMoment_integral 4
  change (∫ x in (0 : ℝ)..bRef, q x * source u v w x ^ 2) = _
  rw [he]
  simp (disch := (apply Continuous.intervalIntegrable; fun_prop)) only
    [intervalIntegral.integral_add, intervalIntegral.integral_sub,
      intervalIntegral.integral_const_mul, h0, h1, h2, h3, h4]
  ring

private theorem pairIntegrand_symm (u v w x y : ℝ) :
    pairIntegrand u v w x y = pairIntegrand u v w y x := by
  unfold pairIntegrand pairGeom pairNumerator
  ring

private theorem reference_pair_integral (u v w : ℝ) :
    (1 / 2 : ℝ) * (∫ x in bRef..1, pairIntegrand u v w x (bRef + 1 - x)) =
      halfwidth * ∫ t in (0 : ℝ)..1, pairIntegrand u v w (xp t) (xm t) := by
  let J := fun x => pairIntegrand u v w x (bRef + 1 - x)
  have hc : Continuous J := continuous_capacity_pair bRef u v w
  have he (x : ℝ) : J (bRef + 1 - x) = J x := by
    dsimp only [J]
    rw [show bRef + 1 - (bRef + 1 - x) = x by ring, pairIntegrand_symm]
  have hR := intervalIntegral.integral_comp_sub_left (f := J) (a := bRef)
    (b := pairMidpoint) (d := bRef + 1)
  simp only [he, show bRef + 1 - pairMidpoint = pairMidpoint by dsimp [pairMidpoint]; ring,
    add_sub_cancel_left] at hR
  have hs := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable bRef pairMidpoint) (hc.intervalIntegrable pairMidpoint 1)
  have hmap := intervalIntegral.mul_integral_comp_add_mul (f := J) (a := (0 : ℝ))
    (b := 1) (c := halfwidth) (d := pairMidpoint)
  rw [mul_zero, add_zero, mul_one,
    show pairMidpoint + halfwidth = 1 by dsimp [pairMidpoint, halfwidth]; ring] at hmap
  have hp : (fun t => J (pairMidpoint + halfwidth * t)) =
      fun t => pairIntegrand u v w (xp t) (xm t) := by
    funext t
    dsimp only [J, xp]
    rw [show bRef + 1 - (pairMidpoint + halfwidth * t) = xm t by dsimp [xm, pairMidpoint]; ring]
  rw [hp] at hmap
  change (1 / 2) * (∫ x in bRef..1, J x) = _
  linarith only [hR, hs, hmap]

private theorem reference_pair_source_expansion (u v w t : ℝ) :
    pairIntegrand u v w (xp t) (xm t) =
      u ^ 2 * (pair00 t * pairS t) + 2 * u * v * (pair02 t * pairS t) +
      v ^ 2 * (pair22 t * pairS t) + 2 * u * w * (pair04 t * pairS t) +
      2 * v * w * (pair24 t * pairS t) + w ^ 2 * (pair44 t * pairS t) := by
  unfold pairIntegrand pairGeom pairNumerator source pair00 pair02 pair22 pair04 pair24 pair44 pairS pairZ p2 p4
  ring

private theorem capacity_reference_eq (u v w : ℝ) :
    capacity bRef u v w = referenceCapacityQuad u v w := by
  unfold capacity
  rw [outside_source_integral, reference_pair_integral]
  simp_rw [reference_pair_source_expansion]
  have hq : Continuous qStrip := by unfold qStrip firstOverlapEvenStripReciprocal; fun_prop
  have hp : Continuous xp := by unfold xp; fun_prop
  have hm : Continuous xm := by unfold xm; fun_prop
  have hi (f : ℝ → ℝ) (hf : Continuous f) : IntervalIntegrable f volume 0 1 := hf.intervalIntegrable 0 1
  simp (disch := (apply hi; dsimp only [pair00, pair02, pair22, pair04, pair24, pair44, pairS, pairZ, p2, p4]; fun_prop)) only
    [intervalIntegral.integral_add, intervalIntegral.integral_const_mul]
  unfold referenceCapacityQuad cap00 cap02 cap22 cap04 cap24 cap44
  ring

private theorem reciprocal_young {q U : ℝ} (hq : 0 < q) (hU : 1 ≤ U * q)
    (p u : ℝ) : 2 * p * u ≤ U * u ^ 2 + q * p ^ 2 := by
  have hprod := mul_nonneg (sub_nonneg.mpr hU) (sq_nonneg u)
  have hs := sq_nonneg (u - q * p)
  have h : 0 ≤ q * (U * u ^ 2 + q * p ^ 2 - 2 * p * u) := by
    nlinarith only [hprod, hs]
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right h hq)

private theorem reflection_pair_young_potential {q r U V w p s : ℝ}
    (hq : 0 < q) (hr : 0 < r) (hU : 1 ≤ U * q) (hV : 1 ≤ V * r)
    (hz : w ^ 2 * q * r ≤ 1 / 10) (u v : ℝ) :
    2 * (p * u + s * v) ≤ U * u ^ 2 - 2 * w * u * v + V * v ^ 2 +
      pairGeom w q r * pairNumerator w q r p s := by
  have h := reflection_pair_young hq hr hz u v (p := p) (s := s)
  have hu : u ^ 2 / q ≤ U * u ^ 2 := by
    apply (div_le_iff₀ hq).mpr
    have hn := mul_nonneg (sub_nonneg.mpr hU) (sq_nonneg u)
    nlinarith only [hn]
  have hv : v ^ 2 / r ≤ V * v ^ 2 := by
    apply (div_le_iff₀ hr).mpr
    have hn := mul_nonneg (sub_nonneg.mpr hV) (sq_nonneg v)
    nlinarith only [hn]
  have he : pairNumerator w q r p s = q * p ^ 2 + 2 * w * q * r * p * s + r * s ^ 2 := by
    unfold pairNumerator
    ring
  rw [he]
  dsimp only [pairGeom]
  linarith only [h, hu, hv]

private theorem reflected_integral (f : ℝ → ℝ) (b : ℝ) :
    (∫ x in b..1, f (b + 1 - x)) = ∫ x in b..1, f x := by
  have h := intervalIntegral.integral_comp_sub_left (f := f) (a := b) (b := 1) (d := b + 1)
  simpa only [add_sub_cancel_right, add_sub_cancel_left] using h

/-- Integrating scalar and reflected-pair square completions gives the source-capacity bound. -/
private theorem source_young_integral {G : ℝ → ℝ} (hG : Continuous G) {b : ℝ}
    (hb : 84249 / 100000 ≤ b) (hb1 : b ≤ 337 / 400) (u v w : ℝ) :
    2 * (∫ x in (0 : ℝ)..1, source u v w x * G x) ≤
      (∫ x in (0 : ℝ)..1, firstOverlapEvenPotential x * G x ^ 2) -
        wRef * (∫ x in b..1, G x * G (b + 1 - x)) + capacity b u v w := by
  let P := fun x => source u v w x * G x
  let A := fun x => firstOverlapEvenPotential x * G x ^ 2
  let O := fun x => firstOverlapEvenOutsideReciprocal x * source u v w x ^ 2
  let J := fun x => pairIntegrand u v w x (b + 1 - x)
  let C := fun x => G x * G (b + 1 - x)
  have hS : Continuous (source u v w) := by unfold source; fun_prop
  have hU : Continuous firstOverlapEvenPotential := by unfold firstOverlapEvenPotential; fun_prop
  have hP : Continuous P := hS.mul hG
  have hA : Continuous A := hU.mul (hG.pow 2)
  have hO : Continuous O := continuous_capacity_outside u v w
  have hJ : Continuous J := continuous_capacity_pair b u v w
  have hC : Continuous C := hG.mul (hG.comp (continuous_const.sub continuous_id))
  have hPR : Continuous (fun x => P (b + 1 - x)) := hP.comp (continuous_const.sub continuous_id)
  have hAR : Continuous (fun x => A (b + 1 - x)) := hA.comp (continuous_const.sub continuous_id)
  have hb0 : 0 ≤ b := by linarith only [hb]
  have hbOne : b ≤ 1 := by linarith only [hb1]
  have hout := intervalIntegral.integral_mono_on (μ := volume)
    (f := fun x => 2 * P x) (g := fun x => A x + O x) hb0
    ((continuous_const.mul hP).intervalIntegrable 0 b)
    ((hA.add hO).intervalIntegrable 0 b)
    (show ∀ x ∈ Icc (0 : ℝ) b, 2 * P x ≤ A x + O x from by
      intro x hx
      obtain ⟨hq, hrec⟩ := firstOverlapEvenOutsideReciprocal_bound hx.1 (hx.2.trans hb1)
      simpa only [P, A, O, mul_assoc] using reciprocal_young hq hrec (source u v w x) (G x))
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (hA.intervalIntegrable 0 b) (hO.intervalIntegrable 0 b)] at hout
  have hstrip := intervalIntegral.integral_mono_on (μ := volume)
    (f := fun x => 2 * (P x + P (b + 1 - x)))
    (g := fun x => A x + A (b + 1 - x) - (2 * wRef) * C x + J x) hbOne
    ((continuous_const.mul (hP.add hPR)).intervalIntegrable b 1)
    (((hA.add hAR).sub (continuous_const.mul hC) |>.add hJ).intervalIntegrable b 1)
    (show ∀ x ∈ Icc b 1,
      2 * (P x + P (b + 1 - x)) ≤ A x + A (b + 1 - x) - 2 * wRef * C x + J x from by
      intro x hx
      have hy0 : 84249 / 100000 ≤ b + 1 - x := by linarith only [hb, hx.2]
      have hy1 : b + 1 - x ≤ 1 := by linarith only [hx.1]
      obtain ⟨hq, hrec⟩ := firstOverlapEvenStripReciprocal_bound (hb.trans hx.1) hx.2
      obtain ⟨hr, hrecR⟩ := firstOverlapEvenStripReciprocal_bound hy0 hy1
      obtain ⟨hqx, hqx1⟩ := qStrip_bounds (hb.trans hx.1) hx.2
      obtain ⟨hqy, hqy1⟩ := qStrip_bounds hy0 hy1
      have hz := (pairGeom_bounds (show 0 ≤ wRef by norm_num [wRef])
        (show wRef ≤ 1 / 2 by norm_num [wRef]) hq.le hqx1 hr.le hqy1).2.1
      have h := reflection_pair_young_potential hq hr hrec hrecR hz
        (G x) (G (b + 1 - x)) (p := source u v w x) (s := source u v w (b + 1 - x))
      change 2 * (P x + P (b + 1 - x)) ≤
        A x - 2 * wRef * G x * G (b + 1 - x) + A (b + 1 - x) + J x at h
      dsimp only [C]
      linarith only [h])
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (hP.intervalIntegrable b 1) (hPR.intervalIntegrable b 1),
    intervalIntegral.integral_add (μ := volume)
      (f := fun x => A x + A (b + 1 - x) - (2 * wRef) * C x) (g := J)
      (((hA.add hAR).sub (continuous_const.mul hC)).intervalIntegrable b 1)
      (hJ.intervalIntegrable b 1),
    intervalIntegral.integral_sub (μ := volume)
      (f := fun x => A x + A (b + 1 - x)) (g := fun x => (2 * wRef) * C x)
      ((hA.add hAR).intervalIntegrable b 1) ((continuous_const.mul hC).intervalIntegrable b 1),
    intervalIntegral.integral_add (μ := volume) (f := A) (g := fun x => A (b + 1 - x))
      (hA.intervalIntegrable b 1) (hAR.intervalIntegrable b 1),
    intervalIntegral.integral_const_mul, reflected_integral P b, reflected_integral A b] at hstrip
  have hPs := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hP.intervalIntegrable 0 b) (hP.intervalIntegrable b 1)
  have hAs := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hA.intervalIntegrable 0 b) (hA.intervalIntegrable b 1)
  change 2 * (∫ x in (0 : ℝ)..1, P x) ≤
    (∫ x in (0 : ℝ)..1, A x) - wRef * (∫ x in b..1, C x) +
      ((∫ x in (0 : ℝ)..b, O x) + (1 / 2) * ∫ x in b..1, J x)
  nlinarith only [hout, hstrip, hPs, hAs]

/-- The three even charges, including the retained pole and primitive contributions. -/
def firstOverlapEvenCharge (m0 m2 m4 : ℝ) : ℝ :=
  let a : ℝ := 1881 / 5000
  let p0 := 1 + a ^ 2 / 24 + a ^ 4 / 1920
  let p2 := a ^ 2 / 12 + a ^ 4 / 672
  (49 / 20 - 97 / 50000 + a ^ 2 / 24 * (1 / 3 - 5 / 49) + a / 2 - a ^ 2 / 24 - a ^ 3 / 24 -
    4 * a * p0 ^ 2) * m0 ^ 2 -
  2 * (4 * a * p0 * p2 + a ^ 3 / 24 + a ^ 2 / 72) * m0 * m2 +
  (19 / 4 - 5 * (97 / 50000) - 4 * a * p2 ^ 2) * m2 ^ 2 +
  (33 / 10 - 9 * (97 / 50000)) * m4 ^ 2

private theorem source_integral (G : ℝ → ℝ) (hG : Continuous G) (u v w : ℝ) :
    (∫ x in (0 : ℝ)..1, source u v w x * G x) =
      u * (∫ x in (0 : ℝ)..1, G x) + v * (∫ x in (0 : ℝ)..1, G x * p2 x) +
        w * (∫ x in (0 : ℝ)..1, G x * p4 x) := by
  have he : (fun x => source u v w x * G x) =
      fun x => u * G x + v * (G x * p2 x) + w * (G x * p4 x) := by
    funext x
    dsimp [source, p2, p4]
    ring
  have hi0 : IntervalIntegrable (fun x => u * G x) volume 0 1 :=
    (continuous_const.mul hG).intervalIntegrable 0 1
  have hi2 : IntervalIntegrable (fun x => v * (G x * p2 x)) volume 0 1 := by
    apply Continuous.intervalIntegrable
    dsimp only [p2]
    fun_prop
  have hi4 : IntervalIntegrable (fun x => w * (G x * p4 x)) volume 0 1 := by
    apply Continuous.intervalIntegrable
    dsimp only [p4]
    fun_prop
  rw [he, intervalIntegral.integral_add (μ := volume)
      (f := fun x => u * G x + v * (G x * p2 x)) (g := fun x => w * (G x * p4 x))
      (hi0.add hi2) hi4,
    intervalIntegral.integral_add (μ := volume)
      (f := fun x => u * G x) (g := fun x => v * (G x * p2 x)) hi0 hi2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]

/-- At the logarithmic strip endpoint the full source capacity is dominated by the inverse charge. -/
private theorem actual_capacity_le_inverse (u v w : ℝ) :
    capacity (Real.log 2 / (1881 / 5000) - 1) u v w ≤
      (charge2 * u ^ 2 + 2 * poleMixedCharge * u * v + charge0 * v ^ 2) / chargeDet +
        w ^ 2 / (33 / 10 - 9 * (97 / 50000)) := by
  obtain ⟨hb, hbRef⟩ := aperture_reflection_bounds
  have h := capacity_le_reference hb hbRef u v w
  rw [capacity_reference_eq] at h
  have hr := reference_capacity_quad_le u v w
  have hn : 0 ≤ u ^ 2 + v ^ 2 + w ^ 2 := by positivity
  linarith only [h, hr, hn]

/-- Square completion pays the first three even moments at the first overlap aperture. -/
theorem firstOverlapEvenCharge_le_reference_energy {G : ℝ → ℝ} (hG : Continuous G) :
    firstOverlapEvenCharge (∫ x in (0 : ℝ)..1, G x)
      (∫ x in (0 : ℝ)..1, G x * ((3 * x ^ 2 - 1) / 2))
      (∫ x in (0 : ℝ)..1, G x * ((35 * x ^ 4 - 30 * x ^ 2 + 3) / 8)) ≤
      (∫ x in (0 : ℝ)..1, firstOverlapEvenPotential x * G x ^ 2) -
        (49013 / 100000 : ℝ) *
          (∫ x in (Real.log 2 / (1881 / 5000) - 1)..1,
            G x * G (Real.log 2 / (1881 / 5000) - x)) := by
  let m0 := ∫ x in (0 : ℝ)..1, G x
  let m2 := ∫ x in (0 : ℝ)..1, G x * p2 x
  let m4 := ∫ x in (0 : ℝ)..1, G x * p4 x
  let d4 : ℝ := 33 / 10 - 9 * (97 / 50000)
  let u := charge0 * m0 - poleMixedCharge * m2
  let v := charge2 * m2 - poleMixedCharge * m0
  let w := d4 * m4
  let Q := charge0 * m0 ^ 2 - 2 * poleMixedCharge * m0 * m2 + charge2 * m2 ^ 2 + d4 * m4 ^ 2
  have hsource : (∫ x in (0 : ℝ)..1, source u v w x * G x) = Q := by
    rw [source_integral G hG]
    change u * m0 + v * m2 + w * m4 = Q
    dsimp [u, v, w, Q]
    ring
  have hinv : (charge2 * u ^ 2 + 2 * poleMixedCharge * u * v + charge0 * v ^ 2) / chargeDet +
      w ^ 2 / d4 = Q := by
    have hd4 : d4 ≠ 0 := by norm_num [d4]
    dsimp only [u, v, w, Q]
    field_simp [chargeDet_pos.ne', hd4]
    dsimp only [chargeDet]
    ring
  obtain ⟨hb, hbRef⟩ := aperture_reflection_bounds
  have hbmin : (84249 / 100000 : ℝ) ≤ Real.log 2 / (1881 / 5000) - 1 := by
    linarith only [hb]
  have hbmax : Real.log 2 / (1881 / 5000) - 1 ≤ (337 / 400 : ℝ) := by
    linarith only [hbRef]
  have hy := source_young_integral hG hbmin hbmax u v w
  have hc := actual_capacity_le_inverse u v w
  rw [hsource] at hy
  change capacity (Real.log 2 / (1881 / 5000) - 1) u v w ≤
    (charge2 * u ^ 2 + 2 * poleMixedCharge * u * v + charge0 * v ^ 2) / chargeDet + w ^ 2 / d4 at hc
  rw [hinv] at hc
  change Q ≤ _
  have he : (fun x => G x * G (Real.log 2 / (1881 / 5000) - 1 + 1 - x)) =
      fun x => G x * G (Real.log 2 / (1881 / 5000) - x) := by
    funext x
    congr 2
    ring
  rw [he] at hy
  dsimp only [wRef] at hy
  linarith only [hy, hc]

#print axioms firstOverlapEvenCharge_le_reference_energy

private theorem negative_mass_le_reflected_pair {G : ℝ → ℝ} (hG : Continuous G)
    {b : ℝ} (hb : 0 ≤ b) (hb1 : b ≤ 1) :
    -(∫ x in (0 : ℝ)..1, G x ^ 2) ≤ ∫ x in b..1, G x * G (b + 1 - x) := by
  let A := fun x => G x ^ 2
  let C := fun x => G x * G (b + 1 - x)
  have hA : Continuous A := hG.pow 2
  have hAR : Continuous (fun x => A (b + 1 - x)) := hA.comp (continuous_const.sub continuous_id)
  have hC : Continuous C := hG.mul (hG.comp (continuous_const.sub continuous_id))
  have hn : 0 ≤ ∫ x in b..1, (G x + G (b + 1 - x)) ^ 2 :=
    intervalIntegral.integral_nonneg hb1 (fun x _ => sq_nonneg _)
  have he : (fun x => (G x + G (b + 1 - x)) ^ 2) =
      fun x => A x + A (b + 1 - x) + 2 * C x := by
    funext x
    dsimp [A, C]
    ring
  rw [he, intervalIntegral.integral_add (μ := volume)
      (f := fun x => A x + A (b + 1 - x)) (g := fun x => 2 * C x)
      ((hA.add hAR).intervalIntegrable b 1) ((continuous_const.mul hC).intervalIntegrable b 1),
    intervalIntegral.integral_add (μ := volume) (f := A) (g := fun x => A (b + 1 - x))
      (hA.intervalIntegrable b 1) (hAR.intervalIntegrable b 1),
    intervalIntegral.integral_const_mul, reflected_integral A b] at hn
  have hleft : 0 ≤ ∫ x in (0 : ℝ)..b, A x :=
    intervalIntegral.integral_nonneg hb (fun x _ => sq_nonneg _)
  have hs := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hA.intervalIntegrable 0 b) (hA.intervalIntegrable b 1)
  change -(∫ x in (0 : ℝ)..1, A x) ≤ ∫ x in b..1, C x
  linarith only [hn, hleft, hs]

/-- The actual prime weight pays all three even charges with rounding loss at most `10⁻⁶` of the mass. -/
theorem firstOverlapEvenCharge_le_energy {G : ℝ → ℝ} (hG : Continuous G) :
    firstOverlapEvenCharge (∫ x in (0 : ℝ)..1, G x)
      (∫ x in (0 : ℝ)..1, G x * ((3 * x ^ 2 - 1) / 2))
      (∫ x in (0 : ℝ)..1, G x * ((35 * x ^ 4 - 30 * x ^ 2 + 3) / 8)) ≤
      (∫ x in (0 : ℝ)..1, firstOverlapEvenPotential x * G x ^ 2) -
        (Real.log 2 / Real.sqrt 2) *
          (∫ x in (Real.log 2 / (1881 / 5000) - 1)..1,
            G x * G (Real.log 2 / (1881 / 5000) - x)) +
          (1 / 1000000 : ℝ) * (∫ x in (0 : ℝ)..1, G x ^ 2) := by
  obtain ⟨hb, hbRef⟩ := aperture_reflection_bounds
  have hb0 : 0 ≤ Real.log 2 / (1881 / 5000) - 1 := by linarith only [hb]
  have hb1 : Real.log 2 / (1881 / 5000) - 1 ≤ 1 := by linarith only [hbRef]
  have hC := negative_mass_le_reflected_pair hG hb0 hb1
  simp only [sub_add_cancel] at hC
  have hQ := firstOverlapEvenCharge_le_reference_energy hG
  have hM : 0 ≤ ∫ x in (0 : ℝ)..1, G x ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) (fun x _ => sq_nonneg _)
  obtain ⟨hwlo, hwhi⟩ := prime_weight_reference_bounds
  have hp := mul_nonneg (sub_nonneg.mpr hwhi) (sub_nonneg.mpr hC)
  have hm := mul_le_mul_of_nonneg_right
    (show (49013 / 100000 : ℝ) - Real.log 2 / Real.sqrt 2 ≤ 1 / 1000000 by linarith only [hwlo]) hM
  nlinarith only [hQ, hp, hm]

#print axioms firstOverlapEvenCharge_le_energy

end GaloisForLFunctions.WindowTowerOfSpecZ
