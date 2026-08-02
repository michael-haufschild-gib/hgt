import GaloisForLFunctions.RHTower.MobiusBlockDefectEnergy

/-!
# Bounded-increment interpolation for Möbius mesh energy

The Route E mesh-energy criterion cannot be interpreted as an arbitrary sparse array estimate.
A bounded-increment sequence is controlled between mesh points by its sampled energy plus the
sharp block interpolation error. Conversely, a large value persists for a quantitatively long
one-sided plateau and therefore consumes cubic energy.

For the Mertens function the increment bound is one, so a critical width-`h` mesh estimate
interpolates to the classical full Mertens mean-square scale. A sampled spike of height `A`
costs order `A³ / h`, sharpening the coefficient-blind `A²` observation.
-/

open scoped BigOperators

namespace RHTower

/-- A value within distance `H` of a sample has square at most twice the sample square plus twice
the squared interpolation error. -/
theorem sq_le_two_sq_add_two_error_sq
    {a b H : ℝ} (hH : 0 ≤ H) (hab : |a - b| ≤ H) :
    a ^ 2 ≤ 2 * b ^ 2 + 2 * H ^ 2 := by
  have hab0 : 0 ≤ |a - b| := abs_nonneg _
  have habsq : |a - b| ^ 2 ≤ H ^ 2 := by
    nlinarith
  rw [sq_abs] at habsq
  nlinarith [sq_nonneg (a - 2 * b)]

/-- Exact regular-grid interpolation bound. The full energy is controlled by twice the mesh
energy times the block width, plus the unavoidable bounded-increment block error. -/
theorem sum_regularGrid_sq_le_sampleEnergy_add_blockError
    (v : ℕ → ℝ) (N h : ℕ)
    (hlocal : ∀ j ∈ Finset.range N, ∀ k ∈ Finset.range h,
      |v (j * h + k) - v (j * h)| ≤ (h : ℝ)) :
    ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range h, v (j * h + k) ^ 2 ≤
      2 * (h : ℝ) * (∑ j ∈ Finset.range N, v (j * h) ^ 2) +
        2 * (N : ℝ) * (h : ℝ) ^ 3 := by
  calc
    ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range h, v (j * h + k) ^ 2
        ≤ ∑ j ∈ Finset.range N, ∑ _k ∈ Finset.range h,
            (2 * v (j * h) ^ 2 + 2 * (h : ℝ) ^ 2) := by
          apply Finset.sum_le_sum
          intro j hj
          apply Finset.sum_le_sum
          intro k hk
          exact sq_le_two_sq_add_two_error_sq (Nat.cast_nonneg h) (hlocal j hj k hk)
    _ = 2 * (h : ℝ) * (∑ j ∈ Finset.range N, v (j * h) ^ 2) +
        2 * (N : ℝ) * (h : ℝ) ^ 3 := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, Finset.mul_sum]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      simp only [Nat.mul_comm]
      ring_nf

/-- A uniform step bound propagates linearly from the initial value. -/
theorem abs_sub_zero_le_nat_mul_of_step
    (v : ℕ → ℝ) (N : ℕ) {L : ℝ}
    (hstep : ∀ k < N, |v (k + 1) - v k| ≤ L) :
    ∀ k ≤ N, |v k - v 0| ≤ (k : ℝ) * L := by
  intro k hk
  induction k with
  | zero => simp
  | succ k ih =>
      have hkN : k < N := Nat.lt_of_succ_le hk
      calc
        |v (k + 1) - v 0| =
            |(v (k + 1) - v k) + (v k - v 0)| := by ring_nf
        _ ≤ |v (k + 1) - v k| + |v k - v 0| := abs_add_le _ _
        _ ≤ L + (k : ℝ) * L := add_le_add (hstep k hkN) (ih (Nat.le_of_lt hkN))
        _ = ((k + 1 : ℕ) : ℝ) * L := by push_cast; ring

/-- One-sided spike persistence. If `m` steps cannot change half the initial height, the first
`m` values consume at least `m |v 0|² / 4` energy. -/
theorem oneSided_plateauEnergy_lower
    (v : ℕ → ℝ) (m : ℕ) {L : ℝ} (hL : 0 ≤ L)
    (hstep : ∀ k < m, |v (k + 1) - v k| ≤ L)
    (hplateau : 2 * (m : ℝ) * L ≤ |v 0|) :
    (m : ℝ) * (|v 0| / 2) ^ 2 ≤
      ∑ k ∈ Finset.range m, v k ^ 2 := by
  have hpoint : ∀ k ∈ Finset.range m, (|v 0| / 2) ^ 2 ≤ v k ^ 2 := by
    intro k hk
    have hkm : k < m := Finset.mem_range.mp hk
    have hdist := abs_sub_zero_le_nat_mul_of_step v m hstep k (Nat.le_of_lt hkm)
    have hkmul : (k : ℝ) * L ≤ (m : ℝ) * L := by
      gcongr
    have hhalf : (m : ℝ) * L ≤ |v 0| / 2 := by linarith
    have hv0 : |v 0| ≤ |v k| + |v k - v 0| := by
      calc
        |v 0| = |v k - (v k - v 0)| := by ring_nf
        _ ≤ |v k| + |v k - v 0| := abs_sub _ _
    have hlower : |v 0| / 2 ≤ |v k| := by linarith
    calc
      (|v 0| / 2) ^ 2 ≤ |v k| ^ 2 :=
        (sq_le_sq₀ (by positivity) (abs_nonneg _)).2 hlower
      _ = v k ^ 2 := sq_abs _
  calc
    (m : ℝ) * (|v 0| / 2) ^ 2 =
        ∑ _k ∈ Finset.range m, (|v 0| / 2) ^ 2 := by simp
    _ ≤ ∑ k ∈ Finset.range m, v k ^ 2 := Finset.sum_le_sum hpoint

end RHTower
