import GaloisForLFunctions.HTGeometry.ProductLawDiagonal
import GaloisForLFunctions.HTGeometry.ProductLawDegenerate
import GaloisForLFunctions.HTGeometry.HeadGradientLogarithmic
import GaloisForLFunctions.HTGeometry.ScaledLogWronskian

/-!
# The scaled logarithmic derivative in the model

The quantity a level of the logarithmic Jacobian contributes at its own coordinate is
`(Q'/Q)(X)·v(X)`, and its coordinate derivative is the Wronskian of the cleared numerator over the
square of the denominator.  This is the model form of the polynomial identity, and it is what the
height induction differentiates at each level.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

variable (Q v : ℕ → Polynomial ℂ)

/-- The scaled logarithmic derivative at one coordinate, as a quotient of factors. -/
theorem logFactor_mul_fact_eq (j : ℕ) :
    logFactor (Q j) j * fact (v j) j
      = fact ((Q j).derivative * v j) j / fact (Q j) j := by
  rw [logFactor, fact_mul]
  field_simp

/-- **The derivative of the scaled logarithmic derivative is the Wronskian over the square.** -/
theorem fpderiv_logFactor_mul_fact {j : ℕ} (hQ : Q j ≠ 0) :
    fpderiv j (logFactor (Q j) j * fact (v j) j)
      = fact (scaledLogWronskian (Q j) (v j)) j / fact (Q j) j ^ (2 : ℕ) := by
  have hne : fact (Q j) j ≠ 0 := fact_ne_zero hQ j
  rw [logFactor_mul_fact_eq Q v j, div_eq_mul_inv, Derivation.leibniz,
    Derivation.leibniz_inv, derivation_fact, derivation_fact, fpderiv_fx_self,
    scaledLogWronskian]
  simp only [smul_eq_mul, mul_one, Polynomial.derivative_mul, fact_sub, fact_mul, fact_add,
    fact_pow]
  field_simp
  ring

/-! ## The diagonal entry of the logarithmic Jacobian -/

/-- **Only the newest term of the logarithmic sum sees the newest coordinate**, and it contributes the
Wronskian over the square of the denominator, scaled by the head product below it. -/
theorem fpderiv_logSum_top {n : ℕ} (hQ : Q (n + 1) ≠ 0) :
    fpderiv (n + 1) (logSum Q v (n + 2))
      = prodHead Q (n + 1)
        * (fact (scaledLogWronskian (Q (n + 1)) (v (n + 1))) (n + 1)
            / fact (Q (n + 1)) (n + 1) ^ (2 : ℕ)) := by
  rw [logSum, Finset.sum_range_succ, map_add]
  have hlow : fpderiv (n + 1)
      (∑ j ∈ Finset.range (n + 1), logFactor (Q j) j * prodJet Q v j) = 0 := by
    rw [map_sum]
    refine Finset.sum_eq_zero fun j hj => ?_
    have hjn : j < n + 1 := Finset.mem_range.mp hj
    refine fpderiv_eq_zero_of_mem_lowSub Q v (m := n) (by omega) ?_
    exact Subalgebra.mul_mem _ (logFactorQ_mem_lowSub Q v (by omega))
      (prodJet_mem_lowSub Q v (by omega))
  rw [hlow, zero_add, prodJet_eq]
  have hsplit : logFactor (Q (n + 1)) (n + 1)
      * (prodHead Q (n + 1) * fact (v (n + 1)) (n + 1))
      = prodHead Q (n + 1) * (logFactor (Q (n + 1)) (n + 1) * fact (v (n + 1)) (n + 1)) := by
    ring
  rw [hsplit, Derivation.leibniz,
    fpderiv_prodHead_of_le Q (le_refl (n + 1)),
    fpderiv_logFactor_mul_fact Q v (j := n + 1) hQ]
  simp

/-! ## The off-diagonal entries -/

/-- **A higher term of the logarithmic sum, differentiated at a lower coordinate, is multiplied by
that coordinate's logarithmic derivative.**  Only the head product of the term sees the coordinate,
and its logarithmic derivative there is exactly `Q_j'/Q_j`. -/
theorem fpderiv_logSum_term_high {Q : ℕ → Polynomial ℂ} (v : ℕ → Polynomial ℂ)
    (hQ : ∀ i, Q i ≠ 0) {j k : ℕ} (hjk : j < k) :
    fpderiv j (logFactor (Q k) k * prodJet Q v k)
      = logFactor (Q j) j * (logFactor (Q k) k * prodJet Q v k) := by
  have hlog : fpderiv j (logFactor (Q k) k) = 0 := by
    rw [logFactor, div_eq_mul_inv, Derivation.leibniz, Derivation.leibniz_inv,
      derivation_fact, derivation_fact, fpderiv_fx_of_ne (by omega : k ≠ j)]
    simp
  have hv : fpderiv j (fact (v k) k) = 0 :=
    fpderiv_fact_of_ne (by omega : k ≠ j)
  rw [prodJet_eq, Derivation.leibniz, hlog]
  simp only [smul_eq_mul, mul_zero, add_zero]
  rw [Derivation.leibniz, hv, fpderiv_prodHead_eq hQ hjk]
  simp only [smul_eq_mul, mul_zero]
  ring

/-! ## The row formula -/

/-- The logarithmic sum splits at any level into the part up to that level and the tail above it. -/
theorem logSum_split {Q v : ℕ → Polynomial ℂ} {j n : ℕ} (hj : j ≤ n) :
    logSum Q v (n + 2)
      = logSum Q v (j + 2)
        + ∑ k ∈ Finset.Ico (j + 2) (n + 2), logFactor (Q k) k * prodJet Q v k := by
  rw [logSum, logSum, Finset.range_eq_Ico, Finset.range_eq_Ico]
  exact (Finset.sum_Ico_consecutive _ (by omega : 0 ≤ j + 2) (by omega : j + 2 ≤ n + 2)).symm

/-- **The row of the logarithmic Jacobian.**  Differentiating the logarithmic sum at a coordinate
kills everything below it, contributes the Wronskian at the coordinate itself, and multiplies the tail
above it by that coordinate's logarithmic derivative. -/
theorem fpderiv_logSum_row {Q : ℕ → Polynomial ℂ} (v : ℕ → Polynomial ℂ)
    (hQ : ∀ i, Q i ≠ 0) {n j : ℕ} (hj : j ≤ n) :
    fpderiv (j + 1) (logSum Q v (n + 2))
      = prodHead Q (j + 1)
          * (fact (scaledLogWronskian (Q (j + 1)) (v (j + 1))) (j + 1)
              / fact (Q (j + 1)) (j + 1) ^ (2 : ℕ))
        + logFactor (Q (j + 1)) (j + 1)
          * (logSum Q v (n + 2) - logSum Q v (j + 2)) := by
  have hsplit := logSum_split (Q := Q) (v := v) hj
  rw [hsplit, map_add, fpderiv_logSum_top Q v (n := j) (hQ (j + 1))]
  congr 1
  rw [add_sub_cancel_left, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hjk : j + 1 < k := by
    have := (Finset.mem_Ico.mp hk).1
    omega
  exact fpderiv_logSum_term_high v hQ hjk

end GaloisForLFunctions.HTGeometry
