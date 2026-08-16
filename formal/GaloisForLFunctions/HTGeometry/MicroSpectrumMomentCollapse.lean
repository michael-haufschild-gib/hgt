import GaloisForLFunctions.HTGeometry.RankEnergyPowerSum
import Mathlib.Algebra.Group.ForwardDiff

/-!
# Which moments a vanishing micro-spectrum can retain

A packet whose entries all tend to zero in absolute value, but whose low moment stays bounded, has
every higher moment forced to zero.  The two sign regimes differ in how many moments survive:

* a **positive** packet with bounded first moment loses every moment of degree at least two,
  because `∑ aᵢ^k ≤ (max aᵢ)^{k-1} ∑ aᵢ`;
* a **self-adjoint** packet with bounded second moment loses every moment of degree at least
  three, because `|∑ aᵢ^k| ≤ (max |aᵢ|)^{k-2} ∑ aᵢ²`.

So positivity alone cannot carry a higher anomaly, and a group completion is needed to recover the
full hierarchy.  Both bounds are elementary and sharp in the exponent.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- **Positive packets: only the first moment survives.** -/
theorem sum_pow_le_max_pow_mul_sum {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) {m : ℝ} (hm : ∀ i ∈ s, a i ≤ m) {k : ℕ} (hk : 1 ≤ k) :
    ∑ i ∈ s, a i ^ k ≤ m ^ (k - 1) * ∑ i ∈ s, a i := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  have hsplit : a i ^ k = a i ^ (k - 1) * a i := by
    rw [← pow_succ]
    congr 1
    omega
  rw [hsplit]
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (ha i hi) (hm i hi) (k - 1)) (ha i hi)

/-- **Self-adjoint packets: only the first two moments survive.** -/
theorem abs_sum_pow_le_max_pow_mul_sum_sq {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    {m : ℝ} (hm : ∀ i ∈ s, |a i| ≤ m) {k : ℕ} (hk : 2 ≤ k) :
    |∑ i ∈ s, a i ^ k| ≤ m ^ (k - 2) * ∑ i ∈ s, a i ^ 2 := by
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  have hsplit : |a i ^ k| = |a i| ^ (k - 2) * a i ^ 2 := by
    rw [abs_pow]
    have hk2 : k - 2 + 2 = k := by omega
    conv_lhs => rw [← hk2]
    rw [pow_add, sq_abs]
  rw [hsplit]
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (abs_nonneg _) (hm i hi) (k - 2)) (by positivity)

/-- A quantity dominated by a null sequence times a constant tends to zero. -/
theorem tendsto_zero_of_abs_le_mul {T M : ℕ → ℝ} {C : ℝ}
    (hT : ∀ n, |T n| ≤ M n * C) (hM : Tendsto M atTop (𝓝 0)) :
    Tendsto T atTop (𝓝 0) := by
  have hbound : Tendsto (fun n => M n * C) atTop (𝓝 0) := by
    have := hM.mul_const C
    simpa using this
  refine squeeze_zero_norm ?_ hbound
  intro n
  simpa using hT n

/-! ## Forward-difference multiplicities -/

/-- **Forward-difference multiplicities cancel every lower degree.**  The alternating binomial
weights `(-1)^{n-k} C(n,k)` annihilate every power below `n`. -/
theorem alternating_binomial_sum_pow_eq_zero {R : Type*} [CommRing R] {j n : ℕ} (h : j < n) :
    ∑ k ∈ Finset.range (n + 1),
        ((-1 : R) ^ (n - k) * (n.choose k : R)) * (k : R) ^ j = 0 := by
  have hz : (fwdDiff (1 : R))^[n] (fun r : R => r ^ j) 0 = 0 := by
    rw [fwdDiff_iter_pow_eq_zero_of_lt h]
    rfl
  rw [fwdDiff_iter_eq_sum_shift] at hz
  rw [← hz]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [zsmul_eq_mul]
  push_cast
  ring_nf

/-- **...and retain exactly `n!` in degree `n`.** -/
theorem alternating_binomial_sum_pow_eq_factorial {R : Type*} [CommRing R] {n : ℕ} :
    ∑ k ∈ Finset.range (n + 1),
        ((-1 : R) ^ (n - k) * (n.choose k : R)) * (k : R) ^ n
      = ((Nat.factorial n : ℕ) : R) := by
  have hz : (fwdDiff (1 : R))^[n] (fun r : R => r ^ n) 0 = ((Nat.factorial n : ℕ) : R) := by
    rw [fwdDiff_iter_eq_factorial]
    rfl
  rw [fwdDiff_iter_eq_sum_shift] at hz
  rw [← hz]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [zsmul_eq_mul]
  push_cast
  ring_nf

end GaloisForLFunctions.HTGeometry
