import GaloisForLFunctions.RHTower.Sieve.SmoothPrimeCoprimeConvolution
import GaloisForLFunctions.RHTower.Sieve.CoprimeLogMoebiusRecursion
import GaloisForLFunctions.RHTower.Sieve.BivariateConvolutionSummatorySwap

/-!
# Smooth-prime expansion of the coprime logarithmic Möbius kernel

The coefficient convolution is summed exactly over the finite hyperbola.  It expresses the
modulus-`r` kernel as a sum of modulus-one kernels over integers supported on primes dividing `r`:

`T_r(Y) = ∑_{d ∈ D_r, d ≤ Y} d⁻¹ T_1(Y / d)`.

No positivity, squarefreeness, or asymptotic premise is needed.
-/

namespace RHTower.Sieve

open ArithmeticFunction Finset
open scoped BigOperators ArithmeticFunction.Moebius
open GaloisForLFunctions.HTGeometry

noncomputable section

private theorem sum_moebiusDiv_log_eq_coprimeLogMoebius_one
    (Y : ℝ) {d : ℕ} (_hd : 0 < d) :
    (∑ m ∈ Finset.Icc 1 (⌊Y⌋₊ / d),
        moebiusDiv m * Real.log (Y / ((d * m : ℕ) : ℝ))) =
      coprimeLogMoebius 1 (Y / (d : ℝ)) := by
  classical
  rw [coprimeLogMoebius, Nat.floor_div_natCast]
  have hfilter :
      (Finset.Icc 1 (⌊Y⌋₊ / d)).filter (fun m => Nat.Coprime 1 m) =
        Finset.Icc 1 (⌊Y⌋₊ / d) := by
    exact Finset.filter_true_of_mem (fun m _ => Nat.coprime_one_left m)
  rw [hfilter]
  apply Finset.sum_congr rfl
  intro m hm
  rw [moebiusDiv_apply]
  have hcast : ((d * m : ℕ) : ℝ) = (d : ℝ) * (m : ℝ) := by norm_num
  have harg : Y / ((d : ℝ) * (m : ℝ)) = Y / (d : ℝ) / (m : ℝ) :=
    (div_div Y (d : ℝ) (m : ℝ)).symm
  rw [hcast, harg]

theorem coprimeLogMoebius_eq_sum_primeSupportedReciprocal
    (r : ℕ) (Y : ℝ) :
    coprimeLogMoebius r Y =
      ∑ d ∈ Finset.Icc 1 ⌊Y⌋₊,
        primeSupportedReciprocal r d * coprimeLogMoebius 1 (Y / (d : ℝ)) := by
  classical
  rw [coprimeLogMoebius, Finset.sum_filter]
  have hcoeff : ∀ n : ℕ,
      (if Nat.Coprime r n then ((μ n : ℤ) : ℝ) / (n : ℝ) else 0) =
        (primeSupportedReciprocal r * moebiusDiv) n := by
    intro n
    rw [primeSupportedReciprocal_mul_moebiusDiv]
    exact (coprimeMoebiusDiv_apply r n).symm
  rw [show
    (∑ n ∈ Finset.Icc 1 ⌊Y⌋₊,
      if Nat.Coprime r n then
        ((μ n : ℤ) : ℝ) / (n : ℝ) * Real.log (Y / (n : ℝ)) else 0) =
      ∑ n ∈ Finset.Icc 1 ⌊Y⌋₊,
        (primeSupportedReciprocal r * moebiusDiv) n * Real.log (Y / (n : ℝ)) by
      apply Finset.sum_congr rfl
      intro n _
      rw [← hcoeff n]
      split_ifs <;> ring]
  rw [show
    (∑ n ∈ Finset.Icc 1 ⌊Y⌋₊,
        (primeSupportedReciprocal r * moebiusDiv) n * Real.log (Y / (n : ℝ))) =
      ∑ n ∈ Finset.Icc 1 ⌊Y⌋₊,
        ∑ x ∈ n.divisorsAntidiagonal,
          primeSupportedReciprocal r x.1 * moebiusDiv x.2 *
            Real.log (Y / (((x.1 * x.2 : ℕ) : ℝ))) by
      apply Finset.sum_congr rfl
      intro n hn
      rw [ArithmeticFunction.mul_apply, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x hx
      rw [Nat.mem_divisorsAntidiagonal] at hx
      rw [hx.1]]
  rw [sum_Icc_divisorsAntidiagonal_swap
    (fun d m => primeSupportedReciprocal r d * moebiusDiv m *
      Real.log (Y / (((d * m : ℕ) : ℝ)))) ⌊Y⌋₊]
  apply Finset.sum_congr rfl
  intro d hd
  calc
    (∑ m ∈ Finset.Icc 1 (⌊Y⌋₊ / d),
        primeSupportedReciprocal r d * moebiusDiv m *
          Real.log (Y / ((d * m : ℕ) : ℝ))) =
        primeSupportedReciprocal r d *
          ∑ m ∈ Finset.Icc 1 (⌊Y⌋₊ / d),
            moebiusDiv m * Real.log (Y / ((d * m : ℕ) : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _
      ring
    _ = primeSupportedReciprocal r d * coprimeLogMoebius 1 (Y / (d : ℝ)) := by
      rw [sum_moebiusDiv_log_eq_coprimeLogMoebius_one Y (Finset.mem_Icc.mp hd).1]

/-- Positive integers up to `N` supported on primes dividing `r`. -/
def primeSupportedIcc (r N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 N).filter (primeSupportedOn r)

/-- Exact smooth-semigroup expansion of the coprime logarithmic Möbius kernel. -/
theorem coprimeLogMoebius_eq_sum_primeSupported
    (r : ℕ) (Y : ℝ) :
    coprimeLogMoebius r Y =
      ∑ d ∈ primeSupportedIcc r ⌊Y⌋₊,
        (1 / (d : ℝ)) * coprimeLogMoebius 1 (Y / (d : ℝ)) := by
  classical
  rw [primeSupportedIcc]
  rw [coprimeLogMoebius_eq_sum_primeSupportedReciprocal, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  have hdIcc := Finset.mem_Icc.mp hd
  have hd0 : d ≠ 0 := by omega
  by_cases hs : primeSupportedOn r d
  · rw [if_pos hs, primeSupportedReciprocal_apply_of_supported hs,
      reciprocalNatArithmetic_apply hd0]
  · rw [if_neg hs, primeSupportedReciprocal_apply_of_not_supported hs, zero_mul]

end

end RHTower.Sieve
