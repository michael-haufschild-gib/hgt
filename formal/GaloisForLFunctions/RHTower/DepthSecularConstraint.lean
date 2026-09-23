import GaloisForLFunctions.RHTower.ConstrainedProlateDepthSecular
import GaloisForLFunctions.RHTower.ConstrainedProlateSecularVector

/-!
# The depth-`k` eigenvector satisfies the constraint exactly

The depth-`k` secular function is the full constrained secular sum, merely bookkept in three
pieces — head poles `0..k`, the shoulder pole `k+1`, and the tail.  Since each term
`ℓ_j²/(d_j − μ)` is `ℓ_j · v_j`, the secular function *is* the pairing of the eigenvector against
the coordinate vector.  So vanishing of the secular function at the depth-`k` root says exactly
that the eigenvector lies in the constrained hyperplane — not approximately, but identically.

This is the counterpart on the constraint side of the raw-defect analysis: the constraint carries
no defect at all against the true coordinates `ℓ`, so the only deviation against the limiting
coordinates `a` comes from the coordinate drift `ℓ_j → a_j`.
-/

open Filter

noncomputable section

namespace RHTower

variable {d ℓ : ℕ → ℝ} {k : ℕ} {B μ : ℝ}

theorem mul_secularVector_eq (j : ℕ) :
    ℓ j * secularVector d ℓ μ j = ℓ j ^ (2 : ℕ) / (d j - μ) := by
  rw [secularVector, pow_two]
  exact (mul_div_assoc _ _ _).symm

theorem summable_mul_secularVector
    (hB : ∀ j, B ≤ d (j + (k + 2))) (hsum : Summable fun j => ℓ j ^ (2 : ℕ)) (hμ : μ < B) :
    Summable fun j : ℕ => ℓ j * secularVector d ℓ μ j := by
  have htail : Summable fun j : ℕ => ℓ (j + (k + 2)) ^ (2 : ℕ) / (d (j + (k + 2)) - μ) :=
    summable_offsetSecularTail hB hsum hμ
  have hall : Summable fun j : ℕ => ℓ j ^ (2 : ℕ) / (d j - μ) :=
    (summable_nat_add_iff (k + 2)).mp htail
  exact hall.congr fun j => (mul_secularVector_eq j).symm

/-- **The depth-`k` secular function is the constraint pairing.** -/
theorem depthSecular_eq_tsum_mul_secularVector
    (hB : ∀ j, B ≤ d (j + (k + 2))) (hsum : Summable fun j => ℓ j ^ (2 : ℕ)) (hμ : μ < B) :
    depthSecular d ℓ k μ = ∑' j : ℕ, ℓ j * secularVector d ℓ μ j := by
  have hall : Summable fun j : ℕ => ℓ j * secularVector d ℓ μ j :=
    summable_mul_secularVector hB hsum hμ
  have hsplit := hall.sum_add_tsum_nat_add (k + 2)
  have hR : (∑ i ∈ Finset.range (k + 2), ℓ i * secularVector d ℓ μ i)
      = (∑ j ∈ Finset.range (k + 1), ℓ j ^ (2 : ℕ) / (d j - μ))
        + ℓ (k + 1) ^ (2 : ℕ) / (d (k + 1) - μ) := by
    rw [show k + 2 = (k + 1) + 1 from rfl, Finset.sum_range_succ]
    congr 1
    · exact Finset.sum_congr rfl fun j _ => mul_secularVector_eq j
    · exact mul_secularVector_eq (k + 1)
  have hT : (∑' i : ℕ, ℓ (i + (k + 2)) * secularVector d ℓ μ (i + (k + 2)))
      = offsetSecularTail d ℓ (k + 2) μ := by
    rw [offsetSecularTail]
    exact tsum_congr fun j => mul_secularVector_eq (j + (k + 2))
  rw [depthSecular, ← hsplit, hR, hT]

/-- **The depth-`k` eigenvector lies in the constrained hyperplane exactly.**  At a root of the
depth-`k` secular function the pairing against the coordinate vector vanishes identically. -/
theorem tsum_mul_secularVector_eq_zero_of_depthSecular
    (hB : ∀ j, B ≤ d (j + (k + 2))) (hsum : Summable fun j => ℓ j ^ (2 : ℕ)) (hμ : μ < B)
    (hroot : depthSecular d ℓ k μ = 0) :
    ∑' j : ℕ, ℓ j * secularVector d ℓ μ j = 0 := by
  rw [← depthSecular_eq_tsum_mul_secularVector hB hsum hμ]
  exact hroot

/-- The head pairing is the negative of the tail pairing: what the head owes the constraint is
carried entirely by the tail. -/
theorem sum_range_mul_secularVector_eq_neg_tsum
    (hB : ∀ j, B ≤ d (j + (k + 2))) (hsum : Summable fun j => ℓ j ^ (2 : ℕ)) (hμ : μ < B)
    (hroot : depthSecular d ℓ k μ = 0) :
    (∑ j ∈ Finset.range (k + 2), ℓ j * secularVector d ℓ μ j)
      = -∑' j : ℕ, ℓ (j + (k + 2)) * secularVector d ℓ μ (j + (k + 2)) := by
  have hall : Summable fun j : ℕ => ℓ j * secularVector d ℓ μ j :=
    summable_mul_secularVector hB hsum hμ
  have hsplit := hall.sum_add_tsum_nat_add (k + 2)
  have hzero := tsum_mul_secularVector_eq_zero_of_depthSecular hB hsum hμ hroot
  rw [hzero] at hsplit
  linarith [hsplit]

/-! ## The tail pairing is uniformly small

The head discrepancy is carried entirely by the tail, and the tail is bounded by the coordinate
mass divided by the distance from the root to the tail floor.  This is the offset analogue of the
ground-index estimate `infiniteSecularTail_le`.
-/

/-- **Uniform bound on the offset secular tail.** -/
theorem offsetSecularTail_le (hB : ∀ j, B ≤ d (j + m)) (hsum : Summable fun j => ℓ j ^ (2 : ℕ))
    (hμ : μ < B) :
    offsetSecularTail d ℓ m μ ≤ (∑' j : ℕ, ℓ (j + m) ^ (2 : ℕ)) / (B - μ) := by
  have hsum2 : Summable fun j : ℕ => ℓ (j + m) ^ (2 : ℕ) := (summable_nat_add_iff m).mpr hsum
  rw [offsetSecularTail, ← tsum_div_const]
  refine Summable.tsum_le_tsum (fun j => ?_) (summable_offsetSecularTail hB hsum hμ)
    (hsum2.div_const _)
  exact div_le_div_of_nonneg_left (sq_nonneg _) (by linarith)
    (by linarith [hB j])

/-- **The head pairing against the true coordinates is uniformly small.**  Combining the exact
constraint with the tail bound: at a depth-`k` root the head pairing is bounded in absolute value
by the coordinate mass over the distance to the tail floor. -/
theorem abs_sum_range_mul_secularVector_le
    (hB : ∀ j, B ≤ d (j + (k + 2))) (hsum : Summable fun j => ℓ j ^ (2 : ℕ)) (hμ : μ < B)
    (hroot : depthSecular d ℓ k μ = 0) :
    |∑ j ∈ Finset.range (k + 2), ℓ j * secularVector d ℓ μ j|
      ≤ (∑' j : ℕ, ℓ (j + (k + 2)) ^ (2 : ℕ)) / (B - μ) := by
  have hneg := sum_range_mul_secularVector_eq_neg_tsum hB hsum hμ hroot
  have hTeq : (∑' j : ℕ, ℓ (j + (k + 2)) * secularVector d ℓ μ (j + (k + 2)))
      = offsetSecularTail d ℓ (k + 2) μ := by
    rw [offsetSecularTail]
    exact tsum_congr fun j => mul_secularVector_eq (j + (k + 2))
  rw [hneg, hTeq, abs_neg,
    abs_of_nonneg (offsetSecularTail_nonneg hB hμ)]
  exact offsetSecularTail_le hB hsum hμ

/-- The head weight in closed form. -/
theorem abs_secularVector_zero_mul (hd0 : d 0 < μ) :
    |secularVector d ℓ μ 0 * ℓ 0| = ℓ 0 ^ (2 : ℕ) / (μ - d 0) := by
  have hval : secularVector d ℓ μ 0 * ℓ 0 = ℓ 0 ^ (2 : ℕ) / (d 0 - μ) := by
    rw [mul_comm, mul_secularVector_eq]
  rw [hval, abs_div, abs_of_nonneg (sq_nonneg _),
    abs_of_neg (show d 0 - μ < 0 by linarith)]
  congr 1
  ring

/-- **The normalized head defect is bounded by scale data alone.**  Relative to its own head
weight, the exact eigenvector's pairing against the true coordinates is at most the coordinate mass
times the root's height above `d_0`, divided by the distance to the tail floor and the head
coordinate. -/
theorem abs_sum_range_mul_secularVector_div_le
    (hB : ∀ j, B ≤ d (j + (k + 2))) (hsum : Summable fun j => ℓ j ^ (2 : ℕ)) (hμ : μ < B)
    (hd0 : d 0 < μ) (hℓ0 : ℓ 0 ≠ 0)
    (hroot : depthSecular d ℓ k μ = 0) :
    |∑ j ∈ Finset.range (k + 2), ℓ j * secularVector d ℓ μ j|
        / |secularVector d ℓ μ 0 * ℓ 0|
      ≤ (∑' j : ℕ, ℓ (j + (k + 2)) ^ (2 : ℕ)) * (μ - d 0) / ((B - μ) * ℓ 0 ^ (2 : ℕ)) := by
  have hbound := abs_sum_range_mul_secularVector_le hB hsum hμ hroot
  have hl0sq : (0 : ℝ) < ℓ 0 ^ (2 : ℕ) := by positivity
  have hBμ : (0 : ℝ) < B - μ := by linarith
  have hμd : (0 : ℝ) < μ - d 0 := by linarith
  rw [abs_secularVector_zero_mul hd0, div_div_eq_mul_div]
  have hRHS : (∑' j : ℕ, ℓ (j + (k + 2)) ^ (2 : ℕ)) * (μ - d 0) / ((B - μ) * ℓ 0 ^ (2 : ℕ))
      = (∑' j : ℕ, ℓ (j + (k + 2)) ^ (2 : ℕ)) / (B - μ) * (μ - d 0) / ℓ 0 ^ (2 : ℕ) := by
    field_simp
  rw [hRHS]
  gcongr

end RHTower

end
