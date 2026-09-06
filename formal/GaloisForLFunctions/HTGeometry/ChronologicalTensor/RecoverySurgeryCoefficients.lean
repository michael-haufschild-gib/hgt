import GaloisForLFunctions.HTGeometry.ChronologicalTensor.RecoverySurgeryGrid
import Mathlib.Algebra.Polynomial.Taylor

/-!
# Preservation of the missing homogeneous coefficient

The two highest coefficients of the cardinal cosine expansion determine
its penultimate coefficient after translation. The explicit perturbation
therefore has the same missing coefficient as the shifted Chebyshev polynomial.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section
open Polynomial


theorem recoveryTaylor_penultimate (k : ℕ) (P : ℝ[X]) (hP : P.natDegree ≤ k+1) (a : ℝ) :
    (taylor a P).coeff k = P.coeff k + (k+1 : ℝ)*a*P.coeff (k+1) := by
  rw [taylor_coeff]
  have hd : (hasseDeriv k P).natDegree < 2 := by
    have := natDegree_hasseDeriv_le P k
    omega
  rw [eval_eq_sum_range' hd a]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, mul_one,
    hasseDeriv_coeff, zero_add, Nat.choose_self, Nat.cast_one, one_mul, pow_one]
  rw [Nat.add_comm 1 k, Nat.choose_succ_self_right]
  push_cast
  ring

theorem recoveryChebyshev_top (k : ℕ) :
    (Chebyshev.T ℝ ((k+1 : ℕ) : ℤ)).coeff (k+1) = (2 : ℝ)^k := by
  have hd : (Chebyshev.T ℝ ((k+1 : ℕ) : ℤ)).natDegree = k+1 := by
    rw [Chebyshev.natDegree_T, Int.natAbs_natCast]
  have h := coeff_natDegree (p := Chebyshev.T ℝ ((k+1 : ℕ) : ℤ))
  rw [hd, Chebyshev.leadingCoeff_T, Int.natAbs_natCast, Nat.add_sub_cancel] at h
  exact h

theorem recoveryChebyshev_penultimate (k : ℕ) :
    (Chebyshev.T ℝ ((k+1 : ℕ) : ℤ)).coeff k = 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have he : ((k+1+1 : ℕ) : ℤ) = (k : ℤ)+2 := by push_cast; ring
    rw [he, Chebyshev.T_add_two]
    have hz : (Chebyshev.T ℝ (k : ℤ)).coeff (k+1) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [Chebyshev.natDegree_T, Int.natAbs_natCast]
      omega
    rw [coeff_sub, ← C_ofNat, mul_assoc, coeff_C_mul, coeff_X_mul, hz]
    simpa only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, ih, mul_zero, sub_zero] using
      congrArg (fun x : ℝ => 2*x-0) ih

theorem recoveryChebyshev_shifted_penultimate (k : ℕ) :
    (taylor (-2 : ℝ) (Chebyshev.T ℝ ((k+1 : ℕ) : ℤ))).coeff k =
      -(k+1 : ℝ)*(2 : ℝ)^(k+1) := by
  rw [recoveryTaylor_penultimate k _
    (by rw [Chebyshev.natDegree_T, Int.natAbs_natCast]),
    recoveryChebyshev_top, recoveryChebyshev_penultimate, pow_succ]
  ring

theorem recoveryCosinePolynomial_top (n : ℕ) (a : ℝ) :
    (recoveryCosinePolynomial n a).coeff (n+2) =
      (1/(n+2 : ℝ))*Real.cos (((n+2 : ℕ) : ℝ)*a)*(2 : ℝ)^(n+1) := by
  have hz : (∑ k ∈ Finset.range (n+1), C (Real.cos (((k+1 : ℕ) : ℝ)*a))*
      Chebyshev.T ℝ ((k+1 : ℕ) : ℤ)).coeff (n+2) = 0 := by
    rw [finsetSum_coeff]
    apply Finset.sum_eq_zero
    intro k hk
    rw [coeff_C_mul, coeff_eq_zero_of_natDegree_lt, mul_zero]
    rw [Chebyshev.natDegree_T, Int.natAbs_natCast]
    simp only [Finset.mem_range] at hk
    omega
  simp only [recoveryCosinePolynomial, coeff_C_mul, coeff_add, coeff_one,
    show n+2 ≠ 0 by omega, if_false, hz, mul_zero, zero_add,
    recoveryChebyshev_top (n+1)]
  ring

theorem recoveryCosinePolynomial_penultimate (n : ℕ) (a : ℝ) :
    (recoveryCosinePolynomial n a).coeff (n+1) =
      (1/(n+2 : ℝ))*2*Real.cos (((n+1 : ℕ) : ℝ)*a)*(2 : ℝ)^n := by
  have hs : (∑ k ∈ Finset.range (n+1), C (Real.cos (((k+1 : ℕ) : ℝ)*a))*
      Chebyshev.T ℝ ((k+1 : ℕ) : ℤ)).coeff (n+1) =
      Real.cos (((n+1 : ℕ) : ℝ)*a)*(2 : ℝ)^n := by
    rw [finsetSum_coeff, Finset.sum_eq_single n]
    · rw [coeff_C_mul, recoveryChebyshev_top]
    · intro k hk hkn
      rw [coeff_C_mul, coeff_eq_zero_of_natDegree_lt, mul_zero]
      rw [Chebyshev.natDegree_T, Int.natAbs_natCast]
      simp only [Finset.mem_range] at hk
      omega
    · intro h
      exact False.elim (h (Finset.mem_range.mpr (by omega)))
  simp only [recoveryCosinePolynomial, coeff_C_mul, coeff_add, coeff_one,
    show n+1 ≠ 0 by omega, if_false, hs,
    recoveryChebyshev_penultimate (n+1), mul_zero, zero_add, add_zero]
  ring

theorem recoveryCardinal_top (n : ℕ) :
    (recoveryCardinal n).coeff (n+2) = -(2 : ℝ)^(n+1)/(n+2 : ℝ) := by
  rw [recoveryCardinal_cosine_expansion, recoveryCosinePolynomial_top]
  have he : (((n+2 : ℕ) : ℝ))*(Real.pi/(n+2 : ℝ)) = Real.pi := by
    push_cast
    field_simp
  rw [he, Real.cos_pi]
  ring

theorem recoveryCardinal_penultimate (n : ℕ) :
    (recoveryCardinal n).coeff (n+1) =
      -Chebyshev.node (n+2) 1*(2 : ℝ)^(n+1)/(n+2 : ℝ) := by
  rw [recoveryCardinal_cosine_expansion, recoveryCosinePolynomial_penultimate]
  have he : (((n+1 : ℕ) : ℝ))*(Real.pi/(n+2 : ℝ)) = Real.pi-Real.pi/(n+2 : ℝ) := by
    push_cast
    field_simp
    ring
  rw [he, Real.cos_pi_sub]
  simp only [Chebyshev.node, Nat.cast_one, one_mul, Nat.cast_add, Nat.cast_ofNat, pow_succ]
  ring

theorem recoveryCardinal_shifted_penultimate (n : ℕ) :
    (taylor (-2 : ℝ) (recoveryCardinal n)).coeff (n+1) =
      (2*(n+2 : ℝ)-Chebyshev.node (n+2) 1)*(2 : ℝ)^(n+1)/(n+2 : ℝ) := by
  rw [recoveryTaylor_penultimate (n+1) _ (le_of_eq (recoveryCardinal_degree n)),
    recoveryCardinal_top, recoveryCardinal_penultimate]
  push_cast
  ring

theorem recoverySurgeryPolynomial_shifted_penultimate (n : ℕ) :
    (taylor (-2 : ℝ) (recoverySurgeryPolynomial n)).coeff (n+1) =
      -(n+2 : ℝ)*(2 : ℝ)^(n+2) := by
  have ht := recoveryChebyshev_shifted_penultimate (n+1)
  have hc := recoveryCardinal_shifted_penultimate n
  have hn : (0 : ℝ) < n+2 := by positivity
  have hx := Chebyshev.node_mem_Icc (n := n+2) (i := 1)
  have hd : 0 < 2*(n+2 : ℝ)-Chebyshev.node (n+2) 1 := by
    have hnn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith [hx.2]
  simp only [recoverySurgeryPolynomial, taylor_apply, add_comp, mul_comp, C_comp,
    coeff_add, coeff_C_mul]
  change (1-recoverySurgeryEpsilon n)*
    (taylor (-2 : ℝ) (Chebyshev.T ℝ ((n+2 : ℕ) : ℤ))).coeff (n+1) +
      (recoverySurgeryEpsilon n*recoverySurgeryAlpha n)*
        (taylor (-2 : ℝ) (recoveryCardinal n)).coeff (n+1) = _
  rw [ht, hc, recoverySurgeryAlpha]
  push_cast
  rw [pow_succ (2 : ℝ) (n+1)]
  field_simp
  ring

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
