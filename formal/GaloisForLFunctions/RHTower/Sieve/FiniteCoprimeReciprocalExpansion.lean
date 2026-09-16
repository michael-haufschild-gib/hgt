import GaloisForLFunctions.RHTower.Sieve.SmoothPrimeCoprimeConvolution
import GaloisForLFunctions.RHTower.Sieve.BivariateConvolutionSummatorySwap

/-!
# Finite coprime reciprocal expansion

The finite reciprocal Möbius column with a coprimality condition admits an exact convolution
expansion.  It separates the support-restricted reciprocal semigroup from the unit-modulus
reciprocal Möbius column without taking absolute values or passing to a limit.
-/

noncomputable section
set_option autoImplicit false

open ArithmeticFunction Finset
open scoped BigOperators ArithmeticFunction.Moebius

namespace RHTower.Sieve

open GaloisForLFunctions.HTGeometry

attribute [local instance] Classical.propDecidable

/-- A finite coprime reciprocal Möbius column expands exactly over the supported reciprocal
semigroup and the unit-modulus reciprocal column. -/
theorem finite_coprime_reciprocal_expansion (r Q : ℕ) :
    (∑ j ∈ Icc 1 Q,
      if r.Coprime j then ((μ j : ℤ) : ℝ) / (j : ℝ) else 0) =
      ∑ a ∈ (Icc 1 Q).filter (primeSupportedOn r), 1 / (a : ℝ) *
        ∑ b ∈ Icc 1 (Q / a), ((μ b : ℤ) : ℝ) / (b : ℝ) := by
  classical
  have hcoeff (n : ℕ) :
      (if r.Coprime n then ((μ n : ℤ) : ℝ) / (n : ℝ) else 0) =
        (primeSupportedReciprocal r * moebiusDiv) n := by
    rw [primeSupportedReciprocal_mul_moebiusDiv]
    exact (coprimeMoebiusDiv_apply r n).symm
  rw [show
    (∑ n ∈ Icc 1 Q, (if r.Coprime n then ((μ n : ℤ) : ℝ) / (n : ℝ) else 0)) =
      ∑ n ∈ Icc 1 Q, (primeSupportedReciprocal r * moebiusDiv) n by
      apply sum_congr rfl
      intro n _
      rw [← hcoeff n]]
  rw [show
    (∑ n ∈ Icc 1 Q, (primeSupportedReciprocal r * moebiusDiv) n) =
      ∑ n ∈ Icc 1 Q, ∑ x ∈ n.divisorsAntidiagonal,
        primeSupportedReciprocal r x.1 * moebiusDiv x.2 by
      apply sum_congr rfl
      intro n _
      rw [ArithmeticFunction.mul_apply]]
  calc
    ∑ n ∈ Icc 1 Q, ∑ x ∈ n.divisorsAntidiagonal,
        primeSupportedReciprocal r x.1 * moebiusDiv x.2 =
      ∑ a ∈ Icc 1 Q, ∑ b ∈ Icc 1 (Q / a),
        primeSupportedReciprocal r a * moebiusDiv b :=
      sum_Icc_divisorsAntidiagonal_swap
        (fun a b => primeSupportedReciprocal r a * moebiusDiv b) Q
    _ = _ := by
      rw [Finset.sum_filter]
      apply sum_congr rfl
      intro a ha
      have ha0 : a ≠ 0 := Nat.ne_of_gt (mem_Icc.mp ha).1
      by_cases hs : primeSupportedOn r a
      · rw [if_pos hs, primeSupportedReciprocal_apply_of_supported hs,
          reciprocalNatArithmetic_apply ha0, ← Finset.mul_sum]
        apply congrArg
        apply sum_congr rfl
        intro b hb
        rw [moebiusDiv_apply]
      · rw [if_neg hs, primeSupportedReciprocal_apply_of_not_supported hs]
        simp

end RHTower.Sieve
