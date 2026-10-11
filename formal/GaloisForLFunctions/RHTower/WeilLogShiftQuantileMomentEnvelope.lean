import GaloisForLFunctions.RHTower.WeilLogShiftQuantileMoments
import GaloisForLFunctions.HTGeometry.MomentBochnerBridge

/-! A polynomial envelope for every integer power of the joint quantile error. -/

open MeasureTheory ProbabilityTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

def finiteWeilQuantileMomentEnvelope (p : ℕ) (x y : ℝ) : ℝ :=
  (2 : ℝ) ^ p * ((2 : ℝ) ^ p *
    (1 + (2 : ℝ) ^ p * (2 + x ^ (2 * p) + y ^ (2 * p))))

theorem finiteWeilQuantileMomentEnvelope_nonneg (p : ℕ) (x y : ℝ) :
    0 ≤ finiteWeilQuantileMomentEnvelope p x y := by
  have hx : 0 ≤ x ^ (2 * p) := by rw [pow_mul]; exact pow_nonneg (sq_nonneg x) p
  have hy : 0 ≤ y ^ (2 * p) := by rw [pow_mul]; exact pow_nonneg (sq_nonneg y) p
  unfold finiteWeilQuantileMomentEnvelope
  positivity

theorem finiteWeil_nonnegative_add_pow_bound {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (p : ℕ) :
    (a + b) ^ p ≤ (2 : ℝ) ^ p * (a ^ p + b ^ p) := by
  exact (add_pow_le ha hb p).trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : p - 1 ≤ p)) (by positivity))

theorem finiteWeil_distance_pow_envelope {d x y : ℝ} (hd0 : 0 ≤ d)
    (hd : d ≤ 2 + 2 * |x - y|) (p : ℕ) :
    d ^ p ≤ finiteWeilQuantileMomentEnvelope p x y := by
  have habs : |x - y| ^ p ≤ (2 : ℝ) ^ p * (|x| ^ p + |y| ^ p) :=
    (pow_le_pow_left₀ (abs_nonneg _) (abs_sub x y) p).trans
      (finiteWeil_nonnegative_add_pow_bound (abs_nonneg x) (abs_nonneg y) p)
  have hx : |x| ^ p ≤ 1 + x ^ (2 * p) := by
    simpa only [abs_pow] using HTGeometry.abs_pow_le_one_add_even p x
  have hy : |y| ^ p ≤ 1 + y ^ (2 * p) := by
    simpa only [abs_pow] using HTGeometry.abs_pow_le_one_add_even p y
  have hdiff : |x - y| ^ p ≤ (2 : ℝ) ^ p * (2 + x ^ (2 * p) + y ^ (2 * p)) :=
    habs.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
  calc
    _ ≤ (2 + 2 * |x - y|) ^ p := pow_le_pow_left₀ hd0 hd p
    _ ≤ (2 : ℝ) ^ p * ((2 : ℝ) ^ p + (2 * |x - y|) ^ p) :=
      finiteWeil_nonnegative_add_pow_bound (by norm_num) (by positivity) p
    _ = (2 : ℝ) ^ p * ((2 : ℝ) ^ p * (1 + |x - y| ^ p)) := by rw [mul_pow]; ring
    _ ≤ finiteWeilQuantileMomentEnvelope p x y := by
      unfold finiteWeilQuantileMomentEnvelope
      gcongr

theorem finiteWeilCanonicalJointQuantile_pow_envelope_bound (r t p : ℕ)
    (u : {u : ℝ // u ∈ Ioo (0 : ℝ) 1}) :
    dist (finiteWeilCanonicalJointQuantile r (2 * (r + 1) ^ 2 + t) u.val)
      (finiteWeilDiagonalGaussianQuantile u.val) ^ p ≤
      finiteWeilQuantileMomentEnvelope p
        (quantile (finiteWeilCanonicalProjectedProbabilityLaw r (2 * (r + 1) ^ 2 + t) 1 0 : Measure ℝ) u.val)
        (quantile (finiteWeilProjectedGaussian 1 0 : Measure ℝ) u.val) := by
  have htrans := finiteWeilCanonicalJointQuantile_diagonal_bound r t u
  have hs : (1 : ℝ) ≤ Real.sqrt (r + 1 : ℕ) := by
    have h := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ (r + 1 : ℕ) by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le r))
    simpa only [Real.sqrt_one] using h
  have ht : (2 : ℝ) / Real.sqrt (r + 1 : ℕ) ≤ 2 := by
    apply (div_le_iff₀ (by linarith : 0 < Real.sqrt (r + 1 : ℕ))).mpr
    linarith
  have hdiag := finiteWeilDiagonalPoint_lipschitz.dist_le_mul
    (quantile (finiteWeilCanonicalProjectedProbabilityLaw r (2 * (r + 1) ^ 2 + t) 1 0 : Measure ℝ) u.val)
    (quantile (finiteWeilProjectedGaussian 1 0 : Measure ℝ) u.val)
  change dist _ (finiteWeilDiagonalGaussianQuantile u.val) ≤ (2 : ℝ) * _ at hdiag
  rw [Real.dist_eq] at hdiag
  have htri := dist_triangle
    (finiteWeilCanonicalJointQuantile r (2 * (r + 1) ^ 2 + t) u.val)
    (finiteWeilDiagonalPoint
      (quantile (finiteWeilCanonicalProjectedProbabilityLaw r (2 * (r + 1) ^ 2 + t) 1 0 : Measure ℝ) u.val))
    (finiteWeilDiagonalGaussianQuantile u.val)
  apply finiteWeil_distance_pow_envelope dist_nonneg (by linarith) p

end RHTower
