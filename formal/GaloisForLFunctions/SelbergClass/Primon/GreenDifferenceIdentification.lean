import GaloisForLFunctions.SelbergClass.Primon.KestenGreenConditioning
import GaloisForLFunctions.HilbertMetric.Observation.AitkenIdentification

/-!
# Prime and offset identification from Green observations

The three-point difference identities of arXiv:2611.13534, Corollary 3.2,
apply to actual prime Green operator entries. Three consecutive depths
recover both an unknown additive offset and the prime. Along the diagonal,
the same extrapolation recovers the limiting bulk variance exactly.
-/

open _root_.RHTower GaloisForLFunctions.HilbertMetric.Observation
namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

/-- Observations of one Green column with a constant calibration offset. -/
def shiftedGreenColumn (p : Nat.Primes) (c : ℝ) (n k : ℕ) : ℝ :=
  c + kestenGreenEntry p n (n + k)

private theorem column_eq (p : Nat.Primes) (c : ℝ) (n k j : ℕ) :
    shiftedGreenColumn p c n (k + j) =
      c + (primeReciprocal p ^ k * kestenGreenEntry p n n) * primeReciprocal p ^ j := by
  rw [shiftedGreenColumn, kestenGreenEntry_propagation, pow_add]
  ring

/-- The difference ratio identifies the prime reciprocal at every depth. -/
theorem shiftedGreenColumn_ratio (p : Nat.Primes) (c : ℝ) (n k : ℕ) :
    differenceRatio (shiftedGreenColumn p c n k)
      (shiftedGreenColumn p c n (k + 1))
      (shiftedGreenColumn p c n (k + 2)) = primeReciprocal p := by
  have ha : primeReciprocal p ^ k * kestenGreenEntry p n n ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (primeReciprocal_pos p).ne')
      (kestenGreenEntry_pos p n n).ne'
  have h := differenceRatio_geometric c
    (primeReciprocal p ^ k * kestenGreenEntry p n n) (primeReciprocal p)
  simp only [ha, (primeReciprocal_lt_one p).ne, false_or, if_false] at h
  rw [column_eq p c n k 1, column_eq p c n k 2]
  simpa only [shiftedGreenColumn, kestenGreenEntry_propagation, pow_one] using h

/-- An inverse difference ratio recovers the prime itself, despite an unknown offset. -/
theorem shiftedGreenColumn_prime (p : Nat.Primes) (c : ℝ) (n k : ℕ) :
    (differenceRatio (shiftedGreenColumn p c n k)
      (shiftedGreenColumn p c n (k + 1))
      (shiftedGreenColumn p c n (k + 2)))⁻¹ = (p.1 : ℝ) := by
  rw [shiftedGreenColumn_ratio, primeReciprocal, inv_inv]

/-- Three Green observations recover their additive calibration offset exactly. -/
theorem shiftedGreenColumn_offset (p : Nat.Primes) (c : ℝ) (n k : ℕ) :
    aitkenOffset (shiftedGreenColumn p c n k)
      (shiftedGreenColumn p c n (k + 1))
      (shiftedGreenColumn p c n (k + 2)) = c := by
  have h := aitkenOffset_geometric c
    (primeReciprocal p ^ k * kestenGreenEntry p n n) (primeReciprocal p)
  rw [if_neg (primeReciprocal_lt_one p).ne] at h
  rw [column_eq p c n k 1, column_eq p c n k 2]
  simpa only [shiftedGreenColumn, kestenGreenEntry_propagation, pow_one] using h

/-- Consecutive diagonal increments identify the squared prime reciprocal. -/
theorem kestenGreenEntry_diagonal_ratio (p : Nat.Primes) (n : ℕ) :
    differenceRatio (kestenGreenEntry p n n)
      (kestenGreenEntry p (n + 1) (n + 1))
      (kestenGreenEntry p (n + 2) (n + 2)) = primeReciprocal p ^ 2 := by
  unfold differenceRatio
  rw [show n + 2 = (n + 1) + 1 by omega,
    kestenGreenEntry_diagonal_step, kestenGreenEntry_diagonal_step,
    show 2 * (n + 1 + 1) = 2 * (n + 1) + 2 by omega, pow_add]
  exact mul_div_cancel_left₀ _ (pow_ne_zero _ (primeReciprocal_pos p).ne')

/-- The bulk variance is extrapolated exactly from three diagonal entries. -/
theorem kestenGreenEntry_diagonal_aitken (p : Nat.Primes) (n : ℕ) :
    aitkenOffset (kestenGreenEntry p n n)
      (kestenGreenEntry p (n + 1) (n + 1))
      (kestenGreenEntry p (n + 2) (n + 2)) =
        primeReciprocal p / (1 - primeReciprocal p ^ 2) := by
  have hq : primeReciprocal p ^ 2 ≠ 1 :=
    (pow_lt_one₀ (primeReciprocal_pos p).le (primeReciprocal_lt_one p)
      (by omega : (2 : ℕ) ≠ 0)).ne
  have hrep (j : ℕ) : kestenGreenEntry p (n + j) (n + j) =
      primeReciprocal p / (1 - primeReciprocal p ^ 2) +
        (-(primeReciprocal p ^ (2 * (n + 1)) / (1 - primeReciprocal p ^ 2))) *
          (primeReciprocal p ^ 2) ^ j := by
    have h := kestenGreenEntry_diagonal_defect p (n + j)
    rw [show 2 * (n + j + 1) = 2 * (n + 1) + 2 * j by omega,
      pow_add, pow_mul] at h
    linear_combination -h
  have h := aitkenOffset_geometric (primeReciprocal p / (1 - primeReciprocal p ^ 2))
    (-(primeReciprocal p ^ (2 * (n + 1)) / (1 - primeReciprocal p ^ 2)))
    (primeReciprocal p ^ 2)
  rw [if_neg hq] at h
  have hz := hrep 0
  simp only [Nat.add_zero, pow_zero, mul_one] at hz
  rw [hz, hrep 1, hrep 2]
  simpa only [pow_zero, pow_one, mul_one] using h

#print axioms shiftedGreenColumn_prime
#print axioms shiftedGreenColumn_offset
#print axioms kestenGreenEntry_diagonal_ratio
#print axioms kestenGreenEntry_diagonal_aitken

end
end GaloisForLFunctions.SelbergClass.Primon
