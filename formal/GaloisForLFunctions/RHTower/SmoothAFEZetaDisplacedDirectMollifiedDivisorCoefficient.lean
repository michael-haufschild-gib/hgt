import GaloisForLFunctions.RHTower.SmoothAFEZetaDisplacedDirectMollifiedMeanSquare
import GaloisForLFunctions.RHTower.Sieve.DirichletConvolutionDivisorReindex

/-!
# Divisor form of the direct displaced mollified coefficient

The zero-based convolution coefficient is rewritten as the literal positive-natural divisor sum.
This exposes the Barban--Vehov arithmetic carried by the linear Levinson mollifier.
-/

noncomputable section

namespace RHTower

open Complex

/-- Positive-natural direct detector coefficient, before imposing a finite head cutoff. -/
def smoothAFEZetaDisplacedDirectDetectorPositiveCoeff
    (lam d x : ℝ) (n : ℕ) : ℂ :=
  ((n : ℂ) ^ (-displacedLinePt d 0) *
      smoothAFECutoff ((n : ℝ) / x)) *
    (1 - (lam : ℂ) * Complex.log (n : ℂ))

@[simp] theorem smoothAFEZetaDisplacedDirectDetectorPositiveCoeff_succ
    (lam d x : ℝ) (n : ℕ) :
    smoothAFEZetaDisplacedDirectDetectorPositiveCoeff lam d x (n + 1) =
      smoothAFEZetaDisplacedDirectDetectorCoeff lam d x n := by
  simp [smoothAFEZetaDisplacedDirectDetectorPositiveCoeff,
    smoothAFEZetaDisplacedDirectDetectorCoeff]

/-- The finite-vector extension of the direct detector is exactly its
positive-natural coefficient on the finite head and zero off it. -/
theorem Sieve.finCoeffNat_smoothAFEZetaDisplacedDirectDetectorCoeff
    (lam d x : ℝ) (L n : ℕ) :
    Sieve.finCoeffNat L
        (fun j : Fin L => smoothAFEZetaDisplacedDirectDetectorCoeff lam d x j) n =
      if 1 ≤ n ∧ n ≤ L then
        smoothAFEZetaDisplacedDirectDetectorPositiveCoeff lam d x n
      else 0 := by
  rw [Sieve.finCoeffNat]
  split_ifs with h
  · change smoothAFEZetaDisplacedDirectDetectorCoeff lam d x (n - 1) = _
    rw [← smoothAFEZetaDisplacedDirectDetectorPositiveCoeff_succ]
    congr 1
    exact Nat.sub_add_cancel h.1
  · rfl

/-- The finite-vector extension of the literal Levinson mollifier is its
positive-natural coefficient on `Icc 1 M` and zero off it. -/
theorem Sieve.finCoeffNat_levinsonLinearMollifierFinCoeff
    (M n : ℕ) :
    Sieve.finCoeffNat M (levinsonLinearMollifierFinCoeff M) n =
      if 1 ≤ n ∧ n ≤ M then Sieve.levinsonLinearMollifierCoeff M n else 0 := by
  rw [Sieve.finCoeffNat]
  split_ifs with h
  · change Sieve.levinsonLinearMollifierCoeff M (n - 1 + 1) = _
    rw [Nat.sub_add_cancel h.1]
  · rfl

/-- Exact divisor-sum formula for each direct mollified detector coefficient. -/
theorem smoothAFEZetaDisplacedDirectMollifiedCoeff_eq_divisorSum
    (lam d x : ℝ) (L M : ℕ) (r : Fin (L * M)) :
    smoothAFEZetaDisplacedDirectMollifiedCoeff lam d x L M r =
      ∑ k ∈ ((r : ℕ) + 1).divisors.filter
          (fun k => (1 ≤ k ∧ k ≤ L) ∧
            (1 ≤ ((r : ℕ) + 1) / k ∧ ((r : ℕ) + 1) / k ≤ M)),
        smoothAFEZetaDisplacedDirectDetectorPositiveCoeff lam d x k *
          Sieve.levinsonLinearMollifierCoeff M (((r : ℕ) + 1) / k) := by
  classical
  rw [smoothAFEZetaDisplacedDirectMollifiedCoeff,
    Sieve.dirConv_eq_sum_divisors_finCoeffNat]
  simp_rw [Sieve.finCoeffNat_smoothAFEZetaDisplacedDirectDetectorCoeff,
    Sieve.finCoeffNat_levinsonLinearMollifierFinCoeff]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hkL : 1 ≤ k ∧ k ≤ L
  · by_cases hkM : 1 ≤ ((r : ℕ) + 1) / k ∧ ((r : ℕ) + 1) / k ≤ M
    · simp only [hkL, hkM, and_self, if_true]
    · simp only [hkL, hkM, and_false, if_false, mul_zero]
  · simp only [hkL, false_and, if_false, zero_mul]

/-- Fully expanded Möbius--logarithmic divisor formula for each direct
mollified detector coefficient. -/
theorem smoothAFEZetaDisplacedDirectMollifiedCoeff_eq_moebiusDivisorSum
    (lam d x : ℝ) (L M : ℕ) (r : Fin (L * M)) :
    smoothAFEZetaDisplacedDirectMollifiedCoeff lam d x L M r =
      ∑ k ∈ ((r : ℕ) + 1).divisors.filter
          (fun k => (1 ≤ k ∧ k ≤ L) ∧
            (1 ≤ ((r : ℕ) + 1) / k ∧ ((r : ℕ) + 1) / k ≤ M)),
        smoothAFEZetaDisplacedDirectDetectorPositiveCoeff lam d x k *
          (((((ArithmeticFunction.moebius (((r : ℕ) + 1) / k) : ℤ) : ℝ) *
              Real.log ((M : ℝ) / ((((r : ℕ) + 1) / k : ℕ) : ℝ)) /
                Real.log M : ℝ) : ℂ) *
            (((1 : ℝ) /
                Real.sqrt (((((r : ℕ) + 1) / k : ℕ) : ℝ)) : ℝ) : ℂ)) := by
  rw [smoothAFEZetaDisplacedDirectMollifiedCoeff_eq_divisorSum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkM : ((r : ℕ) + 1) / k ≤ M := (Finset.mem_filter.mp hk).2.2.2
  rw [Sieve.levinsonLinearMollifierCoeff_eq hkM]

end RHTower
