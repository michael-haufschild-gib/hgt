import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.Intersection.SignedConductorDivisors
import GaloisForLFunctions.RHTower.QuasiRHQuotientHeadAndFiniteContactAbscissaLaw

/-!
# The finite part of a mixed integral graph intersection

Write an upper divisor by its signed endpoint jumps. A lower graph i and an
upper endpoint j meet at all ratios up to j/i. The continuum degree factors,
while the fractional part of j/i is an exact boundary correction. After paying
this correction, all pairs with the same integer quotient have a single coefficient.
-/

noncomputable section

namespace GaloisForLFunctions.SignedArithmeticCorrespondences
open ArithmeticCastelnuovoSeveri Finset _root_.RHTower
open scoped ArithmeticFunction.vonMangoldt

/-- Multiplicity at m of an upper divisor given by its jumps at j. -/
def upperDivisor (N : ℕ) (b : ℕ → ℤ) (m : ℕ) : ℤ :=
  ∑ j ∈ Icc 1 N, if m ≤ j then b j else 0

/-- Total signed multiplicity of pairs terminating in the same quotient cell. -/
def quotientCoefficient (X N : ℕ) (u b : ℕ → ℤ) (k : ℕ) : ℝ :=
  ∑ i ∈ Icc 1 X, ∑ j ∈ Icc 1 N, if j/i = k then (u i : ℝ)*b j else 0

/-- Product of the two endpoint degrees, obtained by integrating unit density in the ratio. -/
def poleProduct (X N : ℕ) (u b : ℕ → ℤ) : ℝ :=
  (∑ i ∈ Icc 1 X, (u i : ℝ)/i) * ∑ j ∈ Icc 1 N, (b j : ℝ)*j

/-- Signed mass between the rational endpoint and its last integral ratio. -/
def fractionalBoundary (X N : ℕ) (u b : ℕ → ℤ) : ℝ :=
  ∑ i ∈ Icc 1 X, ∑ j ∈ Icc 1 N, (u i : ℝ)*b j*((j : ℝ)/i - (j/i : ℕ))

private theorem height_eq_quotient (X N : ℕ) (u b : ℕ → ℤ) :
    signedDivisorHeight 1 X N u (upperDivisor N b) =
      ∑ i ∈ Icc 1 X, ∑ j ∈ Icc 1 N, (u i : ℝ)*b j*chebyshevPsi (j/i) := by
  rw [signedDivisorHeight_eq Nat.zero_lt_one]
  refine sum_congr rfl fun i hi => ?_
  have hi' := (mem_Icc.mp hi).1
  have hrow (q : ℕ) :
      (u i : ℝ)*(upperDivisor N b (i*q) : ℝ)*Λ q =
        ∑ j ∈ Icc 1 N, (u i : ℝ)*b j*(if q ≤ j/i then Λ q else 0) := by
    simp only [upperDivisor, Int.cast_sum, mul_sum, sum_mul]
    refine sum_congr rfl fun j _ => ?_
    by_cases h : q ≤ j/i
    · have h' : i*q ≤ j := by simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hi').mp h
      simp only [if_pos h, if_pos h']
    · have h' : ¬ i*q ≤ j := fun hq => h ((Nat.le_div_iff_mul_le hi').mpr (by simpa [Nat.mul_comm] using hq))
      simp only [if_neg h, if_neg h', Int.cast_zero, mul_zero, zero_mul]
  simp_rw [hrow]
  rw [sum_comm]
  refine sum_congr rfl fun j hj => ?_
  rw [← mul_sum, ← sum_filter]
  have hset : (Icc 1 N).filter (fun q => q ≤ j/i) = Icc 1 (j/i) := by
    ext q
    simp only [mem_filter, mem_Icc]
    have hle := (Nat.div_le_self j i).trans (mem_Icc.mp hj).2
    omega
  rw [hset]
  rfl

private theorem glue_quotients (X N : ℕ) (u b : ℕ → ℤ) (F : ℕ → ℝ) :
    ∑ k ∈ range (N+1), quotientCoefficient X N u b k * F k =
      ∑ i ∈ Icc 1 X, ∑ j ∈ Icc 1 N, (u i : ℝ)*b j*F (j/i) := by
  simp only [quotientCoefficient, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun i _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun j hj => ?_
  have hj' : j/i < N+1 := Nat.lt_succ_of_le ((Nat.div_le_self j i).trans (mem_Icc.mp hj).2)
  simp [ite_mul, hj', eq_comm]

/-- The boundary-corrected signed height is exactly the Chebyshev error paired
with the glued quotient endpoints. This includes endpoints below the first contact. -/
theorem mixed_height_finite_part (X N : ℕ) (u b : ℕ → ℤ) :
    signedDivisorHeight 1 X N u (upperDivisor N b) - poleProduct X N u b +
      fractionalBoundary X N u b =
      ∑ k ∈ range (N+1), quotientCoefficient X N u b k * psiRemainder k := by
  rw [height_eq_quotient, glue_quotients]
  simp only [poleProduct, fractionalBoundary, sum_mul, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  unfold psiRemainder
  ring

/-- One constant works for every support and both integer divisors. The variation
is measured after cancellation between all pairs sharing a quotient. -/
theorem mixed_height_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (X N : ℕ) (u b : ℕ → ℤ),
      |signedDivisorHeight 1 X N u (upperDivisor N b) - poleProduct X N u b +
        fractionalBoundary X N u b| ≤
      C * ∑ k ∈ range (N+1), |quotientCoefficient X N u b k| * (k : ℝ)^(zetaZeroAbscissa+ε) := by
  obtain ⟨C,hC,hbound⟩ := exists_psiRemainder_le_rpow_zetaZeroAbscissa ε hε
  refine ⟨C,hC,fun X N u b => ?_⟩
  rw [mixed_height_finite_part, mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k _ => ?_)
  rw [abs_mul, mul_left_comm]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  cases k with
  | zero => simp [psiRemainder, chebyshevPsi, hC, Real.rpow_nonneg]
  | succ k => exact hbound _ (Nat.succ_pos _)

#print axioms mixed_height_finite_part
#print axioms mixed_height_bound

end GaloisForLFunctions.SignedArithmeticCorrespondences
