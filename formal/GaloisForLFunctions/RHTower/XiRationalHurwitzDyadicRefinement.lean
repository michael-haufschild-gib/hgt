import GaloisForLFunctions.RHTower.XiHurwitzOrientationEnergy
import GaloisForLFunctions.RHTower.XiHurwitzRationalFiberSeam
import GaloisForLFunctions.RHTower.XiPrimeSeamReflectionEnergy
import GaloisForLFunctions.HTGeometry.TwoProjectionQuantumWalk

/-!
# Rational-Hurwitz power refinement and its positive dyadic defect

The finite rational-Hurwitz response at modulus `n` is the exact character `n ^ s`.  This module
connects that value law to the canonical FE--Schwarz seam at every integer scale.  After the unique
normalization which removes its logarithmic amplitude and reciprocal-scale weight, the seam energy
is exactly

`sinh ((re rho - 1 / 2) * log n) ^ 2`.

This gives arbitrary two-scale rigidity, multiplicative and power recurrences for the reflected
finite values, the HTGeometry inverse-pair recurrence for the full energy hierarchy, and the
all-power lower bound

`k ^ 2 * H n rho ≤ H (n ^ k) rho`.

The first nonlinear specialization is the dyadic positive-square remainder

`H (n ^ 2) rho - 4 * H n rho = 4 * H n rho ^ 2`.

On the actual Xi divisor, equality in any genuinely higher linearized power refinement—or merely
boundedness of one complete power-energy ray—is equivalent to RH and to vanishing of the existing
Hurwitz orientation energy.  These are exact source interfaces, not proofs that linear refinement
or boundedness is supplied by the source.
-/

open Complex
open GaloisForLFunctions

namespace RHTower

noncomputable section

/-- The canonical integer-scale seam energy after removing its logarithmic amplitude and
reciprocal-scale weight. -/
def normalizedScaleSeamEnergy (n : ℕ) (rho : ℂ) : ℝ :=
  (n : ℝ) * ‖orbitwiseNatPrimeSeamCharge n rho‖ ^ 2 /
    (4 * (Real.log (n : ℝ)) ^ 2)

/-- The corresponding energy written only with the finite rational-Hurwitz packet. -/
def normalizedRationalHurwitzReflectionEnergy (n : ℕ) (rho : ℂ) : ℝ :=
  (n : ℝ) * ‖rationalHurwitzFiberReflectionSeam n rho‖ ^ 2 /
    (4 * (Real.log (n : ℝ)) ^ 2)

/-- The finite rational-Hurwitz reflection seam with its logarithmic modulus factor removed. -/
def rationalHurwitzFiberReducedReflectionSeam (n : ℕ) (rho : ℂ) : ℂ :=
  (rationalHurwitzFiberResponse n ((starRingEnd ℂ) rho))⁻¹ -
    (rationalHurwitzFiberResponse n (1 - rho))⁻¹

/-- The original finite-value seam is the logarithmic modulus times the reduced seam. -/
theorem rationalHurwitzFiberReflectionSeam_eq_log_mul_reduced
    (n : ℕ) (rho : ℂ) :
    rationalHurwitzFiberReflectionSeam n rho =
      (Real.log n : ℂ) * rationalHurwitzFiberReducedReflectionSeam n rho := rfl

/-- **Exact normalized reflection law.**  The normalized seam at every integer scale is a
height-free hyperbolic square. -/
theorem normalizedScaleSeamEnergy_eq_sinh
    (rho : ℂ) (n : ℕ) :
    normalizedScaleSeamEnergy n rho =
      Real.sinh ((rho.re - 1 / 2) * Real.log (n : ℝ)) ^ 2 := by
  by_cases hn : 1 < n
  · have h := orbitwiseNatSeamCharge_weighted_norm_sq_eq_sinh rho n hn
    have hnR : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast Nat.zero_lt_of_lt hn
    have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
    have hlog : Real.log (n : ℝ) ≠ 0 :=
      ne_of_gt (Real.log_pos (by exact_mod_cast hn))
    rw [Real.rpow_neg hnR.le, Real.rpow_two] at h
    unfold normalizedScaleSeamEnergy
    field_simp [hn0, hlog] at h ⊢
    nlinarith
  · have hnle : n ≤ 1 := Nat.le_of_not_gt hn
    interval_cases n <;>
      simp [normalizedScaleSeamEnergy, orbitwiseNatPrimeSeamCharge,
        orbitwiseScaleSeamCharge]

/-- On the open strip, the finite rational-Hurwitz packet and the canonical scale seam have the
same normalized energy. -/
theorem normalizedRationalHurwitzReflectionEnergy_eq_scale
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1)
    (n : ℕ) :
    normalizedRationalHurwitzReflectionEnergy n rho =
      normalizedScaleSeamEnergy n rho := by
  rcases n with _ | n
  · simp [normalizedRationalHurwitzReflectionEnergy, normalizedScaleSeamEnergy,
      rationalHurwitzFiberReflectionSeam, rationalHurwitzFiberResponse,
      orbitwiseNatPrimeSeamCharge, orbitwiseScaleSeamCharge]
  · rw [normalizedRationalHurwitzReflectionEnergy, normalizedScaleSeamEnergy,
      rationalHurwitzFiberReflectionSeam_eq_primeSeamCharge (Nat.succ_pos n) hstrip]

/-- Finite-value form of the exact normalized reflection law. -/
theorem normalizedRationalHurwitzReflectionEnergy_eq_sinh
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1)
    (n : ℕ) :
    normalizedRationalHurwitzReflectionEnergy n rho =
      Real.sinh ((rho.re - 1 / 2) * Real.log (n : ℝ)) ^ 2 := by
  rw [normalizedRationalHurwitzReflectionEnergy_eq_scale hstrip n,
    normalizedScaleSeamEnergy_eq_sinh rho n]

/-- Critical-line reflection preserves normalized energy at every integer scale, including the
degenerate scales. -/
theorem normalizedScaleSeamEnergy_lineReflect (rho : ℂ) (n : ℕ) :
    normalizedScaleSeamEnergy n (1 - (starRingEnd ℂ) rho) =
      normalizedScaleSeamEnergy n rho := by
  unfold normalizedScaleSeamEnergy
  rw [orbitwiseNatPrimeSeamCharge_lineReflect, norm_neg]

/-- Schwarz reflection preserves normalized energy at every integer scale. -/
theorem normalizedScaleSeamEnergy_conj
    (rho : ℂ) (n : ℕ) :
    normalizedScaleSeamEnergy n ((starRingEnd ℂ) rho) =
      normalizedScaleSeamEnergy n rho := by
  rw [normalizedScaleSeamEnergy_eq_sinh, normalizedScaleSeamEnergy_eq_sinh]
  simp

/-- Functional-equation reflection preserves normalized energy at every integer scale. -/
theorem normalizedScaleSeamEnergy_one_sub
    (rho : ℂ) (n : ℕ) :
    normalizedScaleSeamEnergy n (1 - rho) =
      normalizedScaleSeamEnergy n rho := by
  rw [normalizedScaleSeamEnergy_eq_sinh, normalizedScaleSeamEnergy_eq_sinh]
  simp only [Complex.sub_re, Complex.one_re]
  rw [show (1 - rho.re - 1 / 2) * Real.log (n : ℝ) =
      -((rho.re - 1 / 2) * Real.log (n : ℝ)) by ring, Real.sinh_neg]
  ring

/-- The normalized energy is nonnegative without a strip hypothesis. -/
theorem normalizedScaleSeamEnergy_nonneg (rho : ℂ) (n : ℕ) :
    0 ≤ normalizedScaleSeamEnergy n rho := by
  rw [normalizedScaleSeamEnergy_eq_sinh rho n]
  positivity

/-- The normalized energy is strictly positive exactly away from the critical line. -/
theorem normalizedScaleSeamEnergy_pos_iff
    (rho : ℂ) (n : ℕ) (hn : 1 < n) :
    0 < normalizedScaleSeamEnergy n rho ↔ rho.re ≠ 1 / 2 := by
  rw [normalizedScaleSeamEnergy_eq_sinh rho n]
  have hlog : Real.log (n : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast hn))
  constructor
  · intro hpos hre
    rw [hre] at hpos
    norm_num at hpos
  · intro hre
    exact sq_pos_of_ne_zero
      (Real.sinh_ne_zero.mpr (mul_ne_zero (sub_ne_zero.mpr hre) hlog))

/-- Exact zero set of the normalized scale energy. -/
theorem normalizedScaleSeamEnergy_eq_zero_iff
    (rho : ℂ) (n : ℕ) (hn : 1 < n) :
    normalizedScaleSeamEnergy n rho = 0 ↔ rho.re = 1 / 2 := by
  constructor
  · intro hzero
    by_contra hre
    exact (ne_of_gt ((normalizedScaleSeamEnergy_pos_iff rho n hn).mpr hre)) hzero
  · intro hre
    rw [normalizedScaleSeamEnergy_eq_sinh rho n, hre]
    norm_num

/-- The normalized energy zero interface is exactly the original complex seam-vanishing
interface, now for every integer scale rather than only prime scales. -/
theorem normalizedScaleSeamEnergy_eq_zero_iff_seamCharge_eq_zero
    (rho : ℂ) (n : ℕ) (hn : 1 < n) :
    normalizedScaleSeamEnergy n rho = 0 ↔
      orbitwiseNatPrimeSeamCharge n rho = 0 := by
  have hnR : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast Nat.zero_lt_of_lt hn
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  have hden : 4 * (Real.log (n : ℝ)) ^ 2 ≠ 0 := by
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hlog.ne')
  unfold normalizedScaleSeamEnergy
  rw [div_eq_zero_iff, mul_eq_zero]
  simp [hnR.ne', hden]

/-- On a finite rational-Hurwitz fibre, zero normalized energy is exactly equality of the two
reflected convergent value packets. -/
theorem normalizedRationalHurwitzReflectionEnergy_eq_zero_iff_response_fixed
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1)
    (n : ℕ) (hn : 1 < n) :
    normalizedRationalHurwitzReflectionEnergy n rho = 0 ↔
      rationalHurwitzFiberResponse n ((starRingEnd ℂ) rho) =
        rationalHurwitzFiberResponse n (1 - rho) := by
  rw [normalizedRationalHurwitzReflectionEnergy_eq_scale hstrip n,
    normalizedScaleSeamEnergy_eq_zero_iff rho n hn,
    rationalHurwitzFiberResponse_reflection_fixed_iff hn hstrip]

/-- Squared hyperbolic displacement is strictly increasing with the integer scale away from the
critical line. -/
lemma sinh_sq_mul_log_nat_lt
    {x : ℝ} (hx : x ≠ 0) {m n : ℕ} (hm : 1 < m) (hmn : m < n) :
    Real.sinh (x * Real.log (m : ℝ)) ^ 2 <
      Real.sinh (x * Real.log (n : ℝ)) ^ 2 := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hm
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt (hm.trans hmn)
  have hlogm : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast hm)
  have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hm.trans hmn)
  have hlogmn : Real.log (m : ℝ) < Real.log (n : ℝ) :=
    Real.strictMonoOn_log hmR hnR (by exact_mod_cast hmn)
  rcases lt_or_gt_of_ne hx with hxneg | hxpos
  · have hxpos' : 0 < -x := neg_pos.mpr hxneg
    have harg : (-x) * Real.log (m : ℝ) < (-x) * Real.log (n : ℝ) :=
      mul_lt_mul_of_pos_left hlogmn hxpos'
    have hsinh := Real.sinh_strictMono harg
    have hsm : 0 < Real.sinh ((-x) * Real.log (m : ℝ)) :=
      Real.sinh_pos_iff.mpr (mul_pos hxpos' hlogm)
    have hsn : 0 < Real.sinh ((-x) * Real.log (n : ℝ)) :=
      Real.sinh_pos_iff.mpr (mul_pos hxpos' hlogn)
    rw [show x * Real.log (m : ℝ) = -((-x) * Real.log (m : ℝ)) by ring,
      show x * Real.log (n : ℝ) = -((-x) * Real.log (n : ℝ)) by ring,
      Real.sinh_neg, Real.sinh_neg]
    nlinarith
  · have harg : x * Real.log (m : ℝ) < x * Real.log (n : ℝ) :=
      mul_lt_mul_of_pos_left hlogmn hxpos
    have hsinh := Real.sinh_strictMono harg
    have hsm : 0 < Real.sinh (x * Real.log (m : ℝ)) :=
      Real.sinh_pos_iff.mpr (mul_pos hxpos hlogm)
    have hsn : 0 < Real.sinh (x * Real.log (n : ℝ)) :=
      Real.sinh_pos_iff.mpr (mul_pos hxpos hlogn)
    nlinarith

/-- **Arbitrary two-scale strict rigidity.**  Off the critical line, normalized energy strictly
increases between any two distinct nontrivial integer scales. -/
theorem normalizedScaleSeamEnergy_lt_of_lt_of_re_ne_half
    {rho : ℂ} {m n : ℕ} (hm : 1 < m) (hmn : m < n)
    (hre : rho.re ≠ 1 / 2) :
    normalizedScaleSeamEnergy m rho < normalizedScaleSeamEnergy n rho := by
  rw [normalizedScaleSeamEnergy_eq_sinh rho m,
    normalizedScaleSeamEnergy_eq_sinh rho n]
  exact sinh_sq_mul_log_nat_lt (sub_ne_zero.mpr hre) hm hmn

/-- Normalized energy is monotone between arbitrary integer scales. -/
theorem normalizedScaleSeamEnergy_mono
    (rho : ℂ) {m n : ℕ} (hm : 1 < m) (hmn : m < n) :
    normalizedScaleSeamEnergy m rho ≤ normalizedScaleSeamEnergy n rho := by
  by_cases hre : rho.re = 1 / 2
  · rw [(normalizedScaleSeamEnergy_eq_zero_iff rho m hm).mpr hre,
      (normalizedScaleSeamEnergy_eq_zero_iff rho n (hm.trans hmn)).mpr hre]
  · exact (normalizedScaleSeamEnergy_lt_of_lt_of_re_ne_half hm hmn hre).le

/-- Equality at any two distinct normalized scales is equivalent to the critical-line equation. -/
theorem normalizedScaleSeamEnergy_eq_iff_re_eq_half
    (rho : ℂ) {m n : ℕ} (hm : 1 < m) (hmn : m < n) :
    normalizedScaleSeamEnergy m rho = normalizedScaleSeamEnergy n rho ↔
      rho.re = 1 / 2 := by
  constructor
  · intro heq
    by_contra hre
    exact (normalizedScaleSeamEnergy_lt_of_lt_of_re_ne_half hm hmn hre).ne heq
  · intro hre
    rw [(normalizedScaleSeamEnergy_eq_zero_iff rho m hm).mpr hre,
      (normalizedScaleSeamEnergy_eq_zero_iff rho n (hm.trans hmn)).mpr hre]

/-- The arbitrary two-scale law transferred to finite rational-Hurwitz values. -/
theorem normalizedRationalHurwitzReflectionEnergy_eq_iff_re_eq_half
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1)
    {m n : ℕ} (hm : 1 < m) (hmn : m < n) :
    normalizedRationalHurwitzReflectionEnergy m rho =
        normalizedRationalHurwitzReflectionEnergy n rho ↔
      rho.re = 1 / 2 := by
  rw [normalizedRationalHurwitzReflectionEnergy_eq_scale hstrip m,
    normalizedRationalHurwitzReflectionEnergy_eq_scale hstrip n]
  exact normalizedScaleSeamEnergy_eq_iff_re_eq_half rho hm hmn

/-- Strict two-scale rigidity transferred to finite rational-Hurwitz values. -/
theorem normalizedRationalHurwitzReflectionEnergy_lt_of_lt_of_re_ne_half
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1)
    {m n : ℕ} (hm : 1 < m) (hmn : m < n) (hre : rho.re ≠ 1 / 2) :
    normalizedRationalHurwitzReflectionEnergy m rho <
      normalizedRationalHurwitzReflectionEnergy n rho := by
  rw [normalizedRationalHurwitzReflectionEnergy_eq_scale hstrip m,
    normalizedRationalHurwitzReflectionEnergy_eq_scale hstrip n]
  exact normalizedScaleSeamEnergy_lt_of_lt_of_re_ne_half hm hmn hre

/-- Finite rational-Hurwitz normalized energy is monotone between arbitrary integer scales. -/
theorem normalizedRationalHurwitzReflectionEnergy_mono
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1)
    {m n : ℕ} (hm : 1 < m) (hmn : m < n) :
    normalizedRationalHurwitzReflectionEnergy m rho ≤
      normalizedRationalHurwitzReflectionEnergy n rho := by
  rw [normalizedRationalHurwitzReflectionEnergy_eq_scale hstrip m,
    normalizedRationalHurwitzReflectionEnergy_eq_scale hstrip n]
  exact normalizedScaleSeamEnergy_mono rho hm hmn

private lemma natCast_mul_cpow_on_nonnegative_ray (m n : ℕ) (s : ℂ) :
    ((m * n : ℕ) : ℂ) ^ s =
      ((m : ℕ) : ℂ) ^ s * ((n : ℕ) : ℂ) ^ s := by
  push_cast
  rw [show (m : ℂ) = ((m : ℝ) : ℂ) by push_cast; rfl,
    show (n : ℂ) = ((n : ℝ) : ℂ) by push_cast; rfl,
    Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg m) (Nat.cast_nonneg n)]

/-- **Multiplicative finite response law.**  Natural-number moduli form an exact multiplicative
character on every exponent in the convergence half-plane, including the zero boundary cases. -/
theorem rationalHurwitzFiberResponse_mul
    (m n : ℕ) {s : ℂ} (hs : 0 < s.re) :
    rationalHurwitzFiberResponse (m * n) s =
      rationalHurwitzFiberResponse m s * rationalHurwitzFiberResponse n s := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp [rationalHurwitzFiberResponse]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [rationalHurwitzFiberResponse]
  have hmpos := Nat.pos_of_ne_zero hm
  have hnpos := Nat.pos_of_ne_zero hn
  rw [rationalHurwitzFiberResponse_eq_cpow (mul_pos hmpos hnpos) hs,
    rationalHurwitzFiberResponse_eq_cpow hmpos hs,
    rationalHurwitzFiberResponse_eq_cpow hnpos hs]
  exact natCast_mul_cpow_on_nonnegative_ray m n s

/-- **Reduced-seam crossed cocycle.**  Multiplication of moduli composes the FE--Schwarz defect
by the two inverse response characters. -/
theorem rationalHurwitzFiberReducedReflectionSeam_mul
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1)
    (m n : ℕ) :
    rationalHurwitzFiberReducedReflectionSeam (m * n) rho =
      rationalHurwitzFiberReducedReflectionSeam m rho *
          (rationalHurwitzFiberResponse n ((starRingEnd ℂ) rho))⁻¹ +
        (rationalHurwitzFiberResponse m (1 - rho))⁻¹ *
          rationalHurwitzFiberReducedReflectionSeam n rho := by
  have hconj : 0 < ((starRingEnd ℂ) rho).re := by simpa using hstrip.1
  have href : 0 < (1 - rho).re := by simp; linarith
  rw [rationalHurwitzFiberReducedReflectionSeam,
    rationalHurwitzFiberReducedReflectionSeam,
    rationalHurwitzFiberReducedReflectionSeam,
    rationalHurwitzFiberResponse_mul m n hconj,
    rationalHurwitzFiberResponse_mul m n href,
    mul_inv_rev, mul_inv_rev]
  ring

/-- Commutativity of modulus multiplication gives an exact four-packet value relation between
the two crossed-cocycle decompositions. -/
theorem rationalHurwitzFiberReducedReflectionSeam_mul_comm_relation
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1)
    (m n : ℕ) :
    rationalHurwitzFiberReducedReflectionSeam m rho *
          (rationalHurwitzFiberResponse n ((starRingEnd ℂ) rho))⁻¹ +
        (rationalHurwitzFiberResponse m (1 - rho))⁻¹ *
          rationalHurwitzFiberReducedReflectionSeam n rho =
      rationalHurwitzFiberReducedReflectionSeam n rho *
          (rationalHurwitzFiberResponse m ((starRingEnd ℂ) rho))⁻¹ +
        (rationalHurwitzFiberResponse n (1 - rho))⁻¹ *
          rationalHurwitzFiberReducedReflectionSeam m rho := by
  rw [← rationalHurwitzFiberReducedReflectionSeam_mul hstrip m n,
    Nat.mul_comm,
    rationalHurwitzFiberReducedReflectionSeam_mul hstrip n m]

/-- **All-power finite response law.**  Passing from modulus `n` to `n ^ k` raises the finite
rational-Hurwitz response to the same natural power. -/
theorem rationalHurwitzFiberResponse_pow
    (n : ℕ) {s : ℂ} (hs : 0 < s.re) (k : ℕ) :
    rationalHurwitzFiberResponse (n ^ k) s =
      rationalHurwitzFiberResponse n s ^ k := by
  induction k with
  | zero =>
      rw [pow_zero, rationalHurwitzFiberResponse_eq_cpow one_pos hs]
      simp
  | succ k ih =>
      rw [pow_succ, rationalHurwitzFiberResponse_mul (n ^ k) n hs,
        ih, pow_succ]

/-- The reduced reflected value on a modulus-power ray is exactly the difference of the two
inverse response powers. -/
theorem rationalHurwitzFiberReducedReflectionSeam_pow
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1)
    (n k : ℕ) :
    rationalHurwitzFiberReducedReflectionSeam (n ^ k) rho =
      (rationalHurwitzFiberResponse n ((starRingEnd ℂ) rho))⁻¹ ^ k -
        (rationalHurwitzFiberResponse n (1 - rho))⁻¹ ^ k := by
  have hconj : 0 < ((starRingEnd ℂ) rho).re := by simpa using hstrip.1
  have href : 0 < (1 - rho).re := by simp; linarith
  rw [rationalHurwitzFiberReducedReflectionSeam,
    rationalHurwitzFiberResponse_pow n hconj k,
    rationalHurwitzFiberResponse_pow n href k, ← inv_pow, ← inv_pow]

/-- **Determinant-weighted reflected-value recurrence.**  The complete reduced seam along a
modulus-power ray is the two-root sine/Lucas recurrence of the inverse response pair. -/
theorem rationalHurwitzFiberReducedReflectionSeam_power_recurrence
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1)
    (n k : ℕ) :
    rationalHurwitzFiberReducedReflectionSeam (n ^ (k + 2)) rho =
      ((rationalHurwitzFiberResponse n ((starRingEnd ℂ) rho))⁻¹ +
          (rationalHurwitzFiberResponse n (1 - rho))⁻¹) *
          rationalHurwitzFiberReducedReflectionSeam (n ^ (k + 1)) rho -
        (rationalHurwitzFiberResponse n ((starRingEnd ℂ) rho))⁻¹ *
          (rationalHurwitzFiberResponse n (1 - rho))⁻¹ *
          rationalHurwitzFiberReducedReflectionSeam (n ^ k) rho := by
  rw [rationalHurwitzFiberReducedReflectionSeam_pow hstrip,
    rationalHurwitzFiberReducedReflectionSeam_pow hstrip,
    rationalHurwitzFiberReducedReflectionSeam_pow hstrip]
  simp only [pow_succ]
  ring

/-- The inverse-response geometric factor in the complete modulus-power seam refinement. -/
def rationalHurwitzFiberInversePowerFactor (n k : ℕ) (rho : ℂ) : ℂ :=
  ∑ j ∈ Finset.range k,
    (rationalHurwitzFiberResponse n ((starRingEnd ℂ) rho))⁻¹ ^ j *
      (rationalHurwitzFiberResponse n (1 - rho))⁻¹ ^ (k - 1 - j)

/-- **Complete finite-value power refinement.**  The modulus-`n ^ k` reflected packet factors as
the modulus-`n` seam times an explicit finite geometric response packet. -/
theorem rationalHurwitzFiberReflectionSeam_pow
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1)
    (n k : ℕ) :
    rationalHurwitzFiberReflectionSeam (n ^ k) rho =
      (k : ℂ) * rationalHurwitzFiberReflectionSeam n rho *
        rationalHurwitzFiberInversePowerFactor n k rho := by
  have hconj : 0 < ((starRingEnd ℂ) rho).re := by simpa using hstrip.1
  have href : 0 < (1 - rho).re := by simp; linarith
  have hA := rationalHurwitzFiberResponse_pow n hconj k
  have hB := rationalHurwitzFiberResponse_pow n href k
  have hlog : Real.log ((n ^ k : ℕ) : ℝ) =
      (k : ℝ) * Real.log (n : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]
  let A : ℂ := (rationalHurwitzFiberResponse n ((starRingEnd ℂ) rho))⁻¹
  let B : ℂ := (rationalHurwitzFiberResponse n (1 - rho))⁻¹
  have hfactor : (A - B) *
      (∑ j ∈ Finset.range k, A ^ j * B ^ (k - 1 - j)) =
        A ^ k - B ^ k :=
    (Commute.all A B).mul_geom_sum₂ k
  unfold rationalHurwitzFiberReflectionSeam
  rw [hA, hB, ← inv_pow, ← inv_pow, hlog]
  change (((k : ℝ) * Real.log (n : ℝ) : ℝ) : ℂ) * (A ^ k - B ^ k) =
    (k : ℂ) * ((Real.log (n : ℝ) : ℂ) * (A - B)) *
      rationalHurwitzFiberInversePowerFactor n k rho
  rw [rationalHurwitzFiberInversePowerFactor]
  change (((k : ℝ) * Real.log (n : ℝ) : ℝ) : ℂ) * (A ^ k - B ^ k) =
    (k : ℂ) * ((Real.log (n : ℝ) : ℂ) * (A - B)) *
      (∑ j ∈ Finset.range k, A ^ j * B ^ (k - 1 - j))
  push_cast
  rw [← hfactor]
  ring

/-- Every natural power refinement is controlled by multiplication of the one-dimensional
hyperbolic coordinate. -/
theorem normalizedScaleSeamEnergy_pow_eq_sinh
    (rho : ℂ) (n k : ℕ) :
    normalizedScaleSeamEnergy (n ^ k) rho =
      Real.sinh ((k : ℝ) *
        ((rho.re - 1 / 2) * Real.log (n : ℝ))) ^ 2 := by
  rw [normalizedScaleSeamEnergy_eq_sinh rho (n ^ k),
    Nat.cast_pow, Real.log_pow]
  congr 2
  ring

private lemma sinh_sq_add_sub_recurrence (a u : ℝ) :
    Real.sinh (a + u) ^ 2 + Real.sinh (a - u) ^ 2 =
      2 * (1 + 2 * Real.sinh u ^ 2) * Real.sinh a ^ 2 +
        2 * Real.sinh u ^ 2 := by
  rw [Real.sinh_add, Real.sinh_sub]
  nlinarith [Real.cosh_sq_sub_sinh_sq a, Real.cosh_sq_sub_sinh_sq u]

private lemma natCast_mul_sinh_le_sinh_natCast_mul
    (u : ℝ) (hu : 0 ≤ u) (k : ℕ) :
    (k : ℝ) * Real.sinh u ≤ Real.sinh ((k : ℝ) * u) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hsku : 0 ≤ Real.sinh ((k : ℝ) * u) :=
        Real.sinh_nonneg_iff.mpr (mul_nonneg (Nat.cast_nonneg k) hu)
      have hsu : 0 ≤ Real.sinh u := Real.sinh_nonneg_iff.mpr hu
      have hleft := mul_le_mul_of_nonneg_left (Real.one_le_cosh u) hsku
      have hright := mul_le_mul_of_nonneg_right
        (Real.one_le_cosh ((k : ℝ) * u)) hsu
      simp only [Nat.cast_succ, add_mul, one_mul, Real.sinh_add]
      nlinarith

private lemma natCast_mul_sinh_lt_sinh_natCast_mul
    (u : ℝ) (hu : 0 < u) {k : ℕ} (hk : 1 < k) :
    (k : ℝ) * Real.sinh u < Real.sinh ((k : ℝ) * u) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  let q := j + 1
  have hq : 0 < q := by simp [q]
  have hqu : 0 < (q : ℝ) * u := mul_pos (by exact_mod_cast hq) hu
  have hsqu : 0 < Real.sinh ((q : ℝ) * u) := Real.sinh_pos_iff.mpr hqu
  have hsu : 0 ≤ Real.sinh u := (Real.sinh_pos_iff.mpr hu).le
  have hleft : Real.sinh ((q : ℝ) * u) <
      Real.sinh ((q : ℝ) * u) * Real.cosh u := by
    nlinarith [mul_pos hsqu (sub_pos.mpr (Real.one_lt_cosh.mpr hu.ne'))]
  have hright : Real.sinh u ≤
      Real.cosh ((q : ℝ) * u) * Real.sinh u := by
    nlinarith [mul_nonneg (sub_nonneg.mpr
      (Real.one_le_cosh ((q : ℝ) * u))) hsu]
  calc
    ((j + 2 : ℕ) : ℝ) * Real.sinh u =
        (q : ℝ) * Real.sinh u + Real.sinh u := by
      simp [q]
      ring
    _ ≤ Real.sinh ((q : ℝ) * u) + Real.sinh u := by
      simpa only [add_comm] using
        add_le_add_right (natCast_mul_sinh_le_sinh_natCast_mul u hu.le q)
          (Real.sinh u)
    _ < Real.sinh ((q : ℝ) * u) * Real.cosh u +
        Real.cosh ((q : ℝ) * u) * Real.sinh u :=
      add_lt_add_of_lt_of_le hleft hright
    _ = Real.sinh (((j + 2 : ℕ) : ℝ) * u) := by
      rw [← Real.sinh_add]
      congr 1
      simp [q]
      ring

private lemma natCast_sq_mul_sinh_sq_le_sinh_natCast_mul_sq
    (u : ℝ) (k : ℕ) :
    (k : ℝ) ^ 2 * Real.sinh u ^ 2 ≤
      Real.sinh ((k : ℝ) * u) ^ 2 := by
  have h := natCast_mul_sinh_le_sinh_natCast_mul |u| (abs_nonneg u) k
  have hleft : 0 ≤ (k : ℝ) * Real.sinh |u| :=
    mul_nonneg (Nat.cast_nonneg k) (Real.sinh_nonneg_iff.mpr (abs_nonneg u))
  have hright : 0 ≤ Real.sinh ((k : ℝ) * |u|) :=
    Real.sinh_nonneg_iff.mpr (mul_nonneg (Nat.cast_nonneg k) (abs_nonneg u))
  have hsabs : Real.sinh |u| ^ 2 = Real.sinh u ^ 2 := by
    rw [← Real.abs_sinh, sq_abs]
  have harg : (k : ℝ) * |u| = |(k : ℝ) * u| := by
    rw [abs_mul, show |(k : ℝ)| = (k : ℝ) from
      abs_of_nonneg (Nat.cast_nonneg k)]
  calc
    (k : ℝ) ^ 2 * Real.sinh u ^ 2 =
        ((k : ℝ) * Real.sinh |u|) ^ 2 := by
      rw [← hsabs]
      ring
    _ ≤ Real.sinh ((k : ℝ) * |u|) ^ 2 := by nlinarith
    _ = Real.sinh ((k : ℝ) * u) ^ 2 := by
      rw [harg, ← Real.abs_sinh, sq_abs]

private lemma natCast_sq_mul_sinh_sq_lt_sinh_natCast_mul_sq
    {u : ℝ} (hu : u ≠ 0) {k : ℕ} (hk : 1 < k) :
    (k : ℝ) ^ 2 * Real.sinh u ^ 2 <
      Real.sinh ((k : ℝ) * u) ^ 2 := by
  have h := natCast_mul_sinh_lt_sinh_natCast_mul |u| (abs_pos.mpr hu) hk
  have hleft : 0 ≤ (k : ℝ) * Real.sinh |u| :=
    mul_nonneg (Nat.cast_nonneg k) (Real.sinh_nonneg_iff.mpr (abs_nonneg u))
  have hsabs : Real.sinh |u| ^ 2 = Real.sinh u ^ 2 := by
    rw [← Real.abs_sinh, sq_abs]
  have harg : (k : ℝ) * |u| = |(k : ℝ) * u| := by
    rw [abs_mul, show |(k : ℝ)| = (k : ℝ) from
      abs_of_nonneg (Nat.cast_nonneg k)]
  calc
    (k : ℝ) ^ 2 * Real.sinh u ^ 2 =
        ((k : ℝ) * Real.sinh |u|) ^ 2 := by
      rw [← hsabs]
      ring
    _ < Real.sinh ((k : ℝ) * |u|) ^ 2 := by
      nlinarith [Real.sinh_nonneg_iff.mpr
        (mul_nonneg (Nat.cast_nonneg k) (abs_nonneg u))]
    _ = Real.sinh ((k : ℝ) * u) ^ 2 := by
      rw [harg, ← Real.abs_sinh, sq_abs]

/-- Every power refinement dominates its quadratic linearization, at all integer scales and
without a strip hypothesis. -/
theorem normalizedScaleSeamEnergy_pow_linear_le
    (rho : ℂ) (n k : ℕ) :
    (k : ℝ) ^ 2 * normalizedScaleSeamEnergy n rho ≤
      normalizedScaleSeamEnergy (n ^ k) rho := by
  rw [normalizedScaleSeamEnergy_pow_eq_sinh rho n k,
    normalizedScaleSeamEnergy_eq_sinh rho n]
  exact natCast_sq_mul_sinh_sq_le_sinh_natCast_mul_sq _ _

/-- Away from the critical line, every genuinely higher power refinement has a strictly positive
nonlinear excess. -/
theorem normalizedScaleSeamEnergy_pow_linear_lt_of_re_ne_half
    (rho : ℂ) (n : ℕ) (hn : 1 < n) (k : ℕ) (hk : 1 < k)
    (hre : rho.re ≠ 1 / 2) :
    (k : ℝ) ^ 2 * normalizedScaleSeamEnergy n rho <
      normalizedScaleSeamEnergy (n ^ k) rho := by
  rw [normalizedScaleSeamEnergy_pow_eq_sinh rho n k,
    normalizedScaleSeamEnergy_eq_sinh rho n]
  exact natCast_sq_mul_sinh_sq_lt_sinh_natCast_mul_sq
    (mul_ne_zero (sub_ne_zero.mpr hre)
      (ne_of_gt (Real.log_pos (by exact_mod_cast hn)))) hk

/-- Equality in an all-power linear refinement detects the critical line exactly.  The hypotheses
exclude precisely the degenerate scales and tautological powers. -/
theorem normalizedScaleSeamEnergy_pow_eq_linear_iff
    (rho : ℂ) (n : ℕ) (hn : 1 < n) (k : ℕ) (hk : 1 < k) :
    normalizedScaleSeamEnergy (n ^ k) rho =
        (k : ℝ) ^ 2 * normalizedScaleSeamEnergy n rho ↔
      rho.re = 1 / 2 := by
  constructor
  · intro heq
    by_contra hre
    exact (ne_of_gt
      (normalizedScaleSeamEnergy_pow_linear_lt_of_re_ne_half
        rho n hn k hk hre)) heq
  · intro hre
    rw [normalizedScaleSeamEnergy_pow_eq_sinh,
      normalizedScaleSeamEnergy_eq_sinh, hre]
    norm_num

/-- Boundedness of the complete normalized energy ray generated by one integer modulus. -/
def ScaleSeamPowerEnergyBounded (n : ℕ) (rho : ℂ) : Prop :=
  ∃ B : ℝ, ∀ k : ℕ, normalizedScaleSeamEnergy (n ^ k) rho ≤ B

/-- **One-ray boundedness criterion.**  At every nondegenerate modulus, the normalized power ray
is bounded exactly on the critical line. -/
theorem scaleSeamPowerEnergyBounded_iff_re_eq_half
    (rho : ℂ) (n : ℕ) (hn : 1 < n) :
    ScaleSeamPowerEnergyBounded n rho ↔ rho.re = 1 / 2 := by
  constructor
  · rintro ⟨B, hB⟩
    by_contra hre
    have hpos : 0 < normalizedScaleSeamEnergy n rho :=
      (normalizedScaleSeamEnergy_pos_iff rho n hn).mpr hre
    obtain ⟨k, hk⟩ := exists_nat_gt
      (max 1 (|B| / normalizedScaleSeamEnergy n rho + 1))
    have hk1 : (1 : ℝ) < (k : ℝ) :=
      lt_of_le_of_lt (le_max_left _ _) hk
    have hratioAdd :
        |B| / normalizedScaleSeamEnergy n rho + 1 < (k : ℝ) :=
      lt_of_le_of_lt (le_max_right _ _) hk
    have hratio : |B| / normalizedScaleSeamEnergy n rho < (k : ℝ) := by
      linarith
    have habs : |B| < (k : ℝ) * normalizedScaleSeamEnergy n rho :=
      (div_lt_iff₀ hpos).mp hratio
    have hkquadratic : (k : ℝ) < (k : ℝ) ^ 2 := by
      nlinarith
    have hquadratic :
        (k : ℝ) * normalizedScaleSeamEnergy n rho <
          (k : ℝ) ^ 2 * normalizedScaleSeamEnergy n rho := by
      exact mul_lt_mul_of_pos_right hkquadratic hpos
    have hlarge : B < normalizedScaleSeamEnergy (n ^ k) rho :=
      calc
        B ≤ |B| := le_abs_self B
        _ < (k : ℝ) * normalizedScaleSeamEnergy n rho := habs
        _ < (k : ℝ) ^ 2 * normalizedScaleSeamEnergy n rho := hquadratic
        _ ≤ normalizedScaleSeamEnergy (n ^ k) rho :=
          normalizedScaleSeamEnergy_pow_linear_le rho n k
    exact (not_lt_of_ge (hB k)) hlarge
  · intro hre
    refine ⟨0, fun k => ?_⟩
    rw [normalizedScaleSeamEnergy_pow_eq_sinh, hre]
    norm_num

/-- **All-power polynomial recurrence.**  The normalized energies along every power ray are
generated from the first energy by one universal second-order affine recurrence. -/
theorem normalizedScaleSeamEnergy_power_recurrence
    (rho : ℂ) (n k : ℕ) :
    normalizedScaleSeamEnergy (n ^ (k + 2)) rho +
        normalizedScaleSeamEnergy (n ^ k) rho =
      2 * (1 + 2 * normalizedScaleSeamEnergy n rho) *
          normalizedScaleSeamEnergy (n ^ (k + 1)) rho +
        2 * normalizedScaleSeamEnergy n rho := by
  rw [normalizedScaleSeamEnergy_pow_eq_sinh rho n (k + 2),
    normalizedScaleSeamEnergy_pow_eq_sinh rho n k,
    normalizedScaleSeamEnergy_pow_eq_sinh rho n (k + 1),
    normalizedScaleSeamEnergy_eq_sinh rho n]
  convert sinh_sq_add_sub_recurrence
      (((k + 1 : ℕ) : ℝ) * ((rho.re - 1 / 2) * Real.log (n : ℝ)))
      ((rho.re - 1 / 2) * Real.log (n : ℝ)) using 1
  all_goals push_cast
  all_goals ring_nf

/-- **HTGeometry--RHTower Chebyshev bridge.**  The abstract inverse-pair recurrence evaluated at
the affine first-scale energy is exactly the complete normalized power-energy hierarchy. -/
theorem unitaryCosineRecurrence_normalizedScaleSeamEnergy
    (rho : ℂ) (n k : ℕ) :
    HTGeometry.unitaryCosineRecurrence
        (2 + 4 * normalizedScaleSeamEnergy n rho) k =
      2 + 4 * normalizedScaleSeamEnergy (n ^ k) rho := by
  induction k using Nat.twoStepInduction with
  | zero =>
      norm_num [HTGeometry.unitaryCosineRecurrence,
        normalizedScaleSeamEnergy_eq_sinh]
  | one => simp [HTGeometry.unitaryCosineRecurrence]
  | more k ih0 ih1 =>
      rw [HTGeometry.unitaryCosineRecurrence, ih1, ih0]
      nlinarith [normalizedScaleSeamEnergy_power_recurrence rho n k]

/-- Finite rational-Hurwitz form of the all-power normalized-energy law. -/
theorem normalizedRationalHurwitzReflectionEnergy_pow_eq_sinh
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1)
    (n k : ℕ) :
    normalizedRationalHurwitzReflectionEnergy (n ^ k) rho =
      Real.sinh ((k : ℝ) *
        ((rho.re - 1 / 2) * Real.log (n : ℝ))) ^ 2 := by
  rw [normalizedRationalHurwitzReflectionEnergy_eq_scale hstrip (n ^ k)]
  exact normalizedScaleSeamEnergy_pow_eq_sinh rho n k

/-- Finite rational-Hurwitz form of the all-power polynomial recurrence. -/
theorem normalizedRationalHurwitzReflectionEnergy_power_recurrence
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1)
    (n k : ℕ) :
    normalizedRationalHurwitzReflectionEnergy (n ^ (k + 2)) rho +
        normalizedRationalHurwitzReflectionEnergy (n ^ k) rho =
      2 * (1 + 2 * normalizedRationalHurwitzReflectionEnergy n rho) *
          normalizedRationalHurwitzReflectionEnergy (n ^ (k + 1)) rho +
        2 * normalizedRationalHurwitzReflectionEnergy n rho := by
  rw [normalizedRationalHurwitzReflectionEnergy_eq_scale hstrip (n ^ (k + 2)),
    normalizedRationalHurwitzReflectionEnergy_eq_scale hstrip (n ^ k),
    normalizedRationalHurwitzReflectionEnergy_eq_scale hstrip (n ^ (k + 1)),
    normalizedRationalHurwitzReflectionEnergy_eq_scale hstrip n]
  exact normalizedScaleSeamEnergy_power_recurrence rho n k

/-- Finite rational-Hurwitz form of the HTGeometry inverse-pair recurrence bridge. -/
theorem unitaryCosineRecurrence_normalizedRationalHurwitzReflectionEnergy
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1)
    (n k : ℕ) :
    HTGeometry.unitaryCosineRecurrence
        (2 + 4 * normalizedRationalHurwitzReflectionEnergy n rho) k =
      2 + 4 * normalizedRationalHurwitzReflectionEnergy (n ^ k) rho := by
  rw [normalizedRationalHurwitzReflectionEnergy_eq_scale hstrip n,
    normalizedRationalHurwitzReflectionEnergy_eq_scale hstrip (n ^ k)]
  exact unitaryCosineRecurrence_normalizedScaleSeamEnergy rho n k

/-- Finite rational-Hurwitz form of the total all-power linearization bound. -/
theorem normalizedRationalHurwitzReflectionEnergy_pow_linear_le
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1)
    (n k : ℕ) :
    (k : ℝ) ^ 2 * normalizedRationalHurwitzReflectionEnergy n rho ≤
      normalizedRationalHurwitzReflectionEnergy (n ^ k) rho := by
  rw [normalizedRationalHurwitzReflectionEnergy_eq_scale hstrip n,
    normalizedRationalHurwitzReflectionEnergy_eq_scale hstrip (n ^ k)]
  exact normalizedScaleSeamEnergy_pow_linear_le rho n k

/-- Strict all-power linearization excess for an off-line finite rational-Hurwitz fibre. -/
theorem normalizedRationalHurwitzReflectionEnergy_pow_linear_lt_of_re_ne_half
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1)
    (n : ℕ) (hn : 1 < n) (k : ℕ) (hk : 1 < k)
    (hre : rho.re ≠ 1 / 2) :
    (k : ℝ) ^ 2 * normalizedRationalHurwitzReflectionEnergy n rho <
      normalizedRationalHurwitzReflectionEnergy (n ^ k) rho := by
  rw [normalizedRationalHurwitzReflectionEnergy_eq_scale hstrip n,
    normalizedRationalHurwitzReflectionEnergy_eq_scale hstrip (n ^ k)]
  exact normalizedScaleSeamEnergy_pow_linear_lt_of_re_ne_half
    rho n hn k hk hre

/-- Linear refinement at any genuinely higher power detects the critical line exactly on every
finite rational-Hurwitz fibre in the open strip. -/
theorem normalizedRationalHurwitzReflectionEnergy_pow_eq_linear_iff
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1)
    (n : ℕ) (hn : 1 < n) (k : ℕ) (hk : 1 < k) :
    normalizedRationalHurwitzReflectionEnergy (n ^ k) rho =
        (k : ℝ) ^ 2 * normalizedRationalHurwitzReflectionEnergy n rho ↔
      rho.re = 1 / 2 := by
  rw [normalizedRationalHurwitzReflectionEnergy_eq_scale hstrip (n ^ k),
    normalizedRationalHurwitzReflectionEnergy_eq_scale hstrip n]
  exact normalizedScaleSeamEnergy_pow_eq_linear_iff rho n hn k hk

/-- Boundedness of one complete finite rational-Hurwitz normalized-energy power ray. -/
def RationalHurwitzPowerEnergyBounded (n : ℕ) (rho : ℂ) : Prop :=
  ∃ B : ℝ, ∀ k : ℕ,
    normalizedRationalHurwitzReflectionEnergy (n ^ k) rho ≤ B

/-- On the open strip, boundedness of one nondegenerate finite-value power ray detects the
critical line exactly. -/
theorem rationalHurwitzPowerEnergyBounded_iff_re_eq_half
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1)
    (n : ℕ) (hn : 1 < n) :
    RationalHurwitzPowerEnergyBounded n rho ↔ rho.re = 1 / 2 := by
  unfold RationalHurwitzPowerEnergyBounded
  simp_rw [normalizedRationalHurwitzReflectionEnergy_eq_scale hstrip]
  exact scaleSeamPowerEnergyBounded_iff_re_eq_half rho n hn

/-- Dyadic specialization of the complete finite-value refinement factorization. -/
theorem rationalHurwitzFiberReflectionSeam_sq
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1)
    (n : ℕ) :
    rationalHurwitzFiberReflectionSeam (n ^ 2) rho =
      2 * rationalHurwitzFiberReflectionSeam n rho *
        ((rationalHurwitzFiberResponse n ((starRingEnd ℂ) rho))⁻¹ +
          (rationalHurwitzFiberResponse n (1 - rho))⁻¹) := by
  have hfactor : rationalHurwitzFiberInversePowerFactor n 2 rho =
      (rationalHurwitzFiberResponse n ((starRingEnd ℂ) rho))⁻¹ +
        (rationalHurwitzFiberResponse n (1 - rho))⁻¹ := by
    simp [rationalHurwitzFiberInversePowerFactor, Finset.sum_range_succ]
    ring
  rw [rationalHurwitzFiberReflectionSeam_pow hstrip n 2]
  rw [hfactor]
  norm_num

/-- **Dyadic refinement square law.**  The normalized energy at modulus `n ^ 2` is a universal
quadratic polynomial in the energy at modulus `n`. -/
theorem normalizedScaleSeamEnergy_sq
    (rho : ℂ) (n : ℕ) :
    normalizedScaleSeamEnergy (n ^ 2) rho =
      4 * normalizedScaleSeamEnergy n rho *
        (1 + normalizedScaleSeamEnergy n rho) := by
  have hzero : normalizedScaleSeamEnergy 1 rho = 0 := by
    rw [normalizedScaleSeamEnergy_eq_sinh]
    simp
  have hrec := normalizedScaleSeamEnergy_power_recurrence rho n 0
  norm_num [hzero] at hrec
  nlinarith

/-- The failure of linear dyadic refinement is exactly a nonnegative square. -/
theorem normalizedScaleSeamEnergy_sq_sub_linear
    (rho : ℂ) (n : ℕ) :
    normalizedScaleSeamEnergy (n ^ 2) rho -
        4 * normalizedScaleSeamEnergy n rho =
      4 * normalizedScaleSeamEnergy n rho ^ 2 := by
  rw [normalizedScaleSeamEnergy_sq rho n]
  ring

/-- The dyadic nonlinear remainder is nonnegative unconditionally. -/
theorem normalizedScaleSeamEnergy_sq_sub_linear_nonneg
    (rho : ℂ) (n : ℕ) :
    0 ≤ normalizedScaleSeamEnergy (n ^ 2) rho -
      4 * normalizedScaleSeamEnergy n rho := by
  rw [normalizedScaleSeamEnergy_sq_sub_linear rho n]
  positivity

/-- Exact equality in the linear dyadic refinement pins the critical line. -/
theorem normalizedScaleSeamEnergy_sq_eq_linear_iff
    (rho : ℂ) (n : ℕ) (hn : 1 < n) :
    normalizedScaleSeamEnergy (n ^ 2) rho =
        4 * normalizedScaleSeamEnergy n rho ↔
      rho.re = 1 / 2 := by
  rw [← sub_eq_zero,
    normalizedScaleSeamEnergy_sq_sub_linear rho n]
  constructor
  · intro hzero
    have hsquare : normalizedScaleSeamEnergy n rho ^ 2 = 0 := by
      nlinarith
    exact (normalizedScaleSeamEnergy_eq_zero_iff rho n hn).mp
      (sq_eq_zero_iff.mp hsquare)
  · intro hre
    rw [(normalizedScaleSeamEnergy_eq_zero_iff rho n hn).mpr hre]
    norm_num

/-- Finite rational-Hurwitz form of the dyadic square law. -/
theorem normalizedRationalHurwitzReflectionEnergy_sq
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1)
    (n : ℕ) :
    normalizedRationalHurwitzReflectionEnergy (n ^ 2) rho =
      4 * normalizedRationalHurwitzReflectionEnergy n rho *
        (1 + normalizedRationalHurwitzReflectionEnergy n rho) := by
  rw [normalizedRationalHurwitzReflectionEnergy_eq_scale hstrip (n ^ 2),
    normalizedRationalHurwitzReflectionEnergy_eq_scale hstrip n]
  exact normalizedScaleSeamEnergy_sq rho n

/-- Finite rational-Hurwitz form of the positive-square dyadic remainder. -/
theorem normalizedRationalHurwitzReflectionEnergy_sq_sub_linear
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1)
    (n : ℕ) :
    normalizedRationalHurwitzReflectionEnergy (n ^ 2) rho -
        4 * normalizedRationalHurwitzReflectionEnergy n rho =
      4 * normalizedRationalHurwitzReflectionEnergy n rho ^ 2 := by
  rw [normalizedRationalHurwitzReflectionEnergy_sq hstrip n]
  ring

/-- The finite rational-Hurwitz dyadic refinement remainder is nonnegative. -/
theorem normalizedRationalHurwitzReflectionEnergy_sq_sub_linear_nonneg
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1)
    (n : ℕ) :
    0 ≤ normalizedRationalHurwitzReflectionEnergy (n ^ 2) rho -
      4 * normalizedRationalHurwitzReflectionEnergy n rho := by
  rw [normalizedRationalHurwitzReflectionEnergy_sq_sub_linear hstrip n]
  positivity

/-- Linear dyadic refinement of one finite Hurwitz fibre is equivalent to the critical-line
equation. -/
theorem normalizedRationalHurwitzReflectionEnergy_sq_eq_linear_iff
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1)
    (n : ℕ) (hn : 1 < n) :
    normalizedRationalHurwitzReflectionEnergy (n ^ 2) rho =
        4 * normalizedRationalHurwitzReflectionEnergy n rho ↔
      rho.re = 1 / 2 := by
  rw [normalizedRationalHurwitzReflectionEnergy_eq_scale hstrip (n ^ 2),
    normalizedRationalHurwitzReflectionEnergy_eq_scale hstrip n]
  exact normalizedScaleSeamEnergy_sq_eq_linear_iff rho n hn

/-- Equality of two distinct normalized rational-Hurwitz energies on every actual Xi divisor
fibre. -/
def XiRationalHurwitzTwoScaleEnergyEqual (m n : ℕ) : Prop :=
  ∀ rho : XiDivisorSupport,
    normalizedRationalHurwitzReflectionEnergy m (rho : ℂ) =
      normalizedRationalHurwitzReflectionEnergy n (rho : ℂ)

/-- **Arbitrary two-scale finite-value criterion.**  Any two distinct nontrivial moduli replace
the previously isolated prime-two--prime-three comparison after canonical normalization. -/
theorem xiRationalHurwitzTwoScaleEnergyEqual_iff_riemannHypothesis
    {m n : ℕ} (hm : 1 < m) (hmn : m < n) :
    XiRationalHurwitzTwoScaleEnergyEqual m n ↔ RiemannHypothesis := by
  constructor
  · intro hscale
    apply xiRationalHurwitzFiberTwoReflectionFixed_iff_riemannHypothesis.mp
    intro rho
    apply (rationalHurwitzFiberResponse_reflection_fixed_iff (n := 2)
      (by norm_num) (xi_divisor_support_re_mem_open_unit rho)).mpr
    exact (normalizedRationalHurwitzReflectionEnergy_eq_iff_re_eq_half
      (xi_divisor_support_re_mem_open_unit rho) hm hmn).mp (hscale rho)
  · intro hRH rho
    apply (normalizedRationalHurwitzReflectionEnergy_eq_iff_re_eq_half
      (xi_divisor_support_re_mem_open_unit rho) hm hmn).mpr
    exact xi_divisor_support_re_eq_half_of_rh hRH rho

/-- Linearization of one arbitrary power refinement on every actual Xi divisor point. -/
def XiRationalHurwitzPowerLinearRefinement (n k : ℕ) : Prop :=
  ∀ rho : XiDivisorSupport,
    normalizedRationalHurwitzReflectionEnergy (n ^ k) (rho : ℂ) =
      (k : ℝ) ^ 2 * normalizedRationalHurwitzReflectionEnergy n (rho : ℂ)

/-- **All-power finite-value criterion.**  At every nondegenerate modulus and genuinely higher
power, disappearance of the nonlinear refinement excess on the Xi divisor is equivalent to RH. -/
theorem xiRationalHurwitzPowerLinearRefinement_iff_riemannHypothesis
    (n : ℕ) (hn : 1 < n) (k : ℕ) (hk : 1 < k) :
    XiRationalHurwitzPowerLinearRefinement n k ↔ RiemannHypothesis := by
  constructor
  · intro hrefine
    apply xiRationalHurwitzFiberTwoReflectionFixed_iff_riemannHypothesis.mp
    intro rho
    apply (rationalHurwitzFiberResponse_reflection_fixed_iff (n := 2)
      (by norm_num) (xi_divisor_support_re_mem_open_unit rho)).mpr
    exact (normalizedRationalHurwitzReflectionEnergy_pow_eq_linear_iff
      (xi_divisor_support_re_mem_open_unit rho) n hn k hk).mp (hrefine rho)
  · intro hRH rho
    apply (normalizedRationalHurwitzReflectionEnergy_pow_eq_linear_iff
      (xi_divisor_support_re_mem_open_unit rho) n hn k hk).mpr
    exact xi_divisor_support_re_eq_half_of_rh hRH rho

/-- Boundedness of one fixed rational-Hurwitz power ray on every actual Xi divisor point. -/
def XiRationalHurwitzPowerEnergyBounded (n : ℕ) : Prop :=
  ∀ rho : XiDivisorSupport, RationalHurwitzPowerEnergyBounded n (rho : ℂ)

/-- **Bounded finite-value ray criterion.**  At every nondegenerate modulus, boundedness of the
complete normalized power ray on the Xi divisor is equivalent to RH. -/
theorem xiRationalHurwitzPowerEnergyBounded_iff_riemannHypothesis
    (n : ℕ) (hn : 1 < n) :
    XiRationalHurwitzPowerEnergyBounded n ↔ RiemannHypothesis := by
  constructor
  · intro hbounded
    apply xiRationalHurwitzFiberTwoReflectionFixed_iff_riemannHypothesis.mp
    intro rho
    apply (rationalHurwitzFiberResponse_reflection_fixed_iff (n := 2)
      (by norm_num) (xi_divisor_support_re_mem_open_unit rho)).mpr
    exact (rationalHurwitzPowerEnergyBounded_iff_re_eq_half
      (xi_divisor_support_re_mem_open_unit rho) n hn).mp (hbounded rho)
  · intro hRH rho
    apply (rationalHurwitzPowerEnergyBounded_iff_re_eq_half
      (xi_divisor_support_re_mem_open_unit rho) n hn).mpr
    exact xi_divisor_support_re_eq_half_of_rh hRH rho

/-- Every bounded finite-value power-ray interface is equivalent to every genuinely higher
power-linearization interface. -/
theorem xiRationalHurwitzPowerEnergyBounded_iff_powerLinearRefinement
    (n : ℕ) (hn : 1 < n) (m : ℕ) (hm : 1 < m)
    (k : ℕ) (hk : 1 < k) :
    XiRationalHurwitzPowerEnergyBounded n ↔
      XiRationalHurwitzPowerLinearRefinement m k := by
  exact (xiRationalHurwitzPowerEnergyBounded_iff_riemannHypothesis n hn).trans
    (xiRationalHurwitzPowerLinearRefinement_iff_riemannHypothesis
      m hm k hk).symm

/-- Every bounded finite-value power-ray interface is exactly vanishing of the global Hurwitz
orientation energy. -/
theorem xiRationalHurwitzPowerEnergyBounded_iff_orientationEnergy_eq_zero
    (n : ℕ) (hn : 1 < n) :
    XiRationalHurwitzPowerEnergyBounded n ↔ xiHurwitzOrientationEnergy = 0 := by
  exact (xiRationalHurwitzPowerEnergyBounded_iff_riemannHypothesis n hn).trans
    riemannHypothesis_iff_xiHurwitzOrientationEnergy_eq_zero

/-- The finite-fibre linear dyadic refinement condition on every actual Xi divisor point. -/
def XiRationalHurwitzDyadicLinearRefinement (n : ℕ) : Prop :=
  ∀ rho : XiDivisorSupport,
    normalizedRationalHurwitzReflectionEnergy (n ^ 2) (rho : ℂ) =
      4 * normalizedRationalHurwitzReflectionEnergy n (rho : ℂ)

/-- The original dyadic interface is exactly the power-linearization interface at exponent two. -/
theorem xiRationalHurwitzPowerLinearRefinement_two_iff_dyadic
    (n : ℕ) :
    XiRationalHurwitzPowerLinearRefinement n 2 ↔
      XiRationalHurwitzDyadicLinearRefinement n := by
  constructor <;> intro h rho
  · specialize h rho
    norm_num at h ⊢
    exact h
  · specialize h rho
    norm_num at h ⊢
    exact h

/-- **Finite-value dyadic criterion.**  At every fixed modulus `n > 1`, disappearance of the
nonlinear finite-Hurwitz refinement square on the Xi divisor is equivalent to RH. -/
theorem xiRationalHurwitzDyadicLinearRefinement_iff_riemannHypothesis
    (n : ℕ) (hn : 1 < n) :
    XiRationalHurwitzDyadicLinearRefinement n ↔ RiemannHypothesis := by
  exact (xiRationalHurwitzPowerLinearRefinement_two_iff_dyadic n).symm.trans
    (xiRationalHurwitzPowerLinearRefinement_iff_riemannHypothesis
      n hn 2 (by norm_num))

/-- Every genuinely higher power-linearization interface is equivalent to every nondegenerate
dyadic interface. -/
theorem xiRationalHurwitzPowerLinearRefinement_iff_dyadic
    (n : ℕ) (hn : 1 < n) (k : ℕ) (hk : 1 < k)
    (m : ℕ) (hm : 1 < m) :
    XiRationalHurwitzPowerLinearRefinement n k ↔
      XiRationalHurwitzDyadicLinearRefinement m := by
  exact (xiRationalHurwitzPowerLinearRefinement_iff_riemannHypothesis
    n hn k hk).trans
      (xiRationalHurwitzDyadicLinearRefinement_iff_riemannHypothesis m hm).symm

/-- Every genuinely higher power-linearization interface is equivalent to every fixed
nondegenerate two-scale normalized-energy interface. -/
theorem xiRationalHurwitzPowerLinearRefinement_iff_twoScaleEnergyEqual
    (n : ℕ) (hn : 1 < n) (k : ℕ) (hk : 1 < k)
    {m q : ℕ} (hm : 1 < m) (hmq : m < q) :
    XiRationalHurwitzPowerLinearRefinement n k ↔
      XiRationalHurwitzTwoScaleEnergyEqual m q := by
  exact (xiRationalHurwitzPowerLinearRefinement_iff_riemannHypothesis
    n hn k hk).trans
      (xiRationalHurwitzTwoScaleEnergyEqual_iff_riemannHypothesis hm hmq).symm

/-- Every genuinely higher power-linearization interface is exactly vanishing of the existing
global Hurwitz orientation energy. -/
theorem xiRationalHurwitzPowerLinearRefinement_iff_orientationEnergy_eq_zero
    (n : ℕ) (hn : 1 < n) (k : ℕ) (hk : 1 < k) :
    XiRationalHurwitzPowerLinearRefinement n k ↔
      xiHurwitzOrientationEnergy = 0 := by
  exact (xiRationalHurwitzPowerLinearRefinement_iff_riemannHypothesis
    n hn k hk).trans riemannHypothesis_iff_xiHurwitzOrientationEnergy_eq_zero

/-- Every fixed dyadic linear-refinement interface is equivalent to every fixed two-scale
normalized-energy interface. -/
theorem xiRationalHurwitzDyadicLinearRefinement_iff_twoScaleEnergyEqual
    (n : ℕ) (hn : 1 < n) {m k : ℕ} (hm : 1 < m) (hmk : m < k) :
    XiRationalHurwitzDyadicLinearRefinement n ↔
      XiRationalHurwitzTwoScaleEnergyEqual m k := by
  exact (xiRationalHurwitzDyadicLinearRefinement_iff_riemannHypothesis n hn).trans
    (xiRationalHurwitzTwoScaleEnergyEqual_iff_riemannHypothesis hm hmk).symm

/-- At modulus two, the finite dyadic refinement condition is exactly vanishing of the existing
global Hurwitz orientation energy. -/
theorem xiRationalHurwitzDyadicLinearRefinement_two_iff_orientationEnergy_eq_zero :
    XiRationalHurwitzDyadicLinearRefinement 2 ↔
      xiHurwitzOrientationEnergy = 0 := by
  exact (xiRationalHurwitzDyadicLinearRefinement_iff_riemannHypothesis 2
    (by norm_num)).trans riemannHypothesis_iff_xiHurwitzOrientationEnergy_eq_zero

end

end RHTower
