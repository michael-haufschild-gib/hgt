import GaloisForLFunctions.SelbergClass.FinitePrimeRigidity
import GaloisForLFunctions.RHTower.SelbergClass.FullEulerLogPrime
import GaloisForLFunctions.RHTower.SelbergClass.FullOne

/-!
# Finite Dirichlet support in the full Selberg class

The logarithmic coefficient convolution forces every Euler factor above a
finite Dirichlet support to be trivial. Finite-prime rigidity then identifies
the full Selberg function with the Dirichlet unit.
-/

noncomputable section
open Complex Filter Set Topology

namespace GaloisForLFunctions.SelbergClass

/-- A prime above the Dirichlet support has no Euler-log coefficients. -/
theorem eulerLogCoeff_prime_pow_eq_zero_of_support_bound
    (F : RHTower.SelbergClass) {N : ℕ}
    (hN : ∀ n : ℕ, N < n → F.coeff n = 0)
    {p k : ℕ} (hp : p.Prime) (hpN : N < p) (hk : 0 < k) :
    F.eulerLogCoeff (p ^ k) = 0 := by
  have hpk : p ≤ p ^ k := by
    simpa only [pow_one] using pow_le_pow_right₀ hp.one_le hk
  have ha : F.coeff (p ^ k) = 0 := hN _ (hpN.trans_le hpk)
  have hcoeff := F.logMul_coeff_apply (p ^ k)
  have hsum : (∑ ij ∈ (p ^ k).divisorsAntidiagonal,
      F.coeff ij.1 * LSeries.logMul F.eulerLogCoeff ij.2) =
      LSeries.logMul F.eulerLogCoeff (p ^ k) := by
    rw [Finset.sum_eq_single (1, p ^ k)]
    · simp only [F.coeff_one, one_mul]
    · intro ij hij hne
      have hij' := Nat.mem_divisorsAntidiagonal.mp hij
      have hi : ij.1 ∣ p ^ k := ⟨ij.2, hij'.1.symm⟩
      obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow hp).mp hi
      have hj0 : j ≠ 0 := by
        intro hz
        have hi1 : ij.1 = 1 := by simpa [hz] using hj
        have hi2 : ij.2 = p ^ k := by simpa [hi1] using hij'.1
        exact hne (Prod.ext hi1 hi2)
      have hple : p ≤ ij.1 := by
        rw [hj]
        simpa only [pow_one] using pow_le_pow_right₀ hp.one_le (Nat.pos_of_ne_zero hj0)
      rw [hN _ (hpN.trans_le hple), zero_mul]
    · intro hnot
      exact (hnot (Nat.mem_divisorsAntidiagonal.mpr
        ⟨by simp, pow_ne_zero _ hp.ne_zero⟩)).elim
  rw [hsum] at hcoeff
  simp only [LSeries.logMul, ha, mul_zero] at hcoeff
  have hlog : Complex.log (p ^ k : ℕ) ≠ 0 := by
    rw [← Complex.natCast_log]
    exact Complex.ofReal_ne_zero.mpr
      (Real.log_pos (by exact_mod_cast (hp.one_lt.trans_le hpk))).ne'
  exact (mul_eq_zero.mp hcoeff.symm).resolve_left hlog

/-- Every full Selberg function with finite Dirichlet support is the unit,
independently of its Gamma presentation. -/
theorem coeff_eq_one_of_support_bound (F : RHTower.SelbergClass) {N : ℕ}
    (hN : ∀ n : ℕ, N < n → F.coeff n = 0) : F.coeff = 1 := by
  classical
  let P := (Finset.range (N + 1)).filter Nat.Prime
  have heq := coeff_eq_of_finite_prime_discrepancy_arbitrary_gamma
    F RHTower.SelbergClass.one P
    (fun p hp => (Finset.mem_filter.mp hp).2) (by
      intro p hp hpP k hk
      have hpN : N < p := by
        by_contra h
        exact hpP (Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr (by omega), hp⟩)
      rw [eulerLogCoeff_prime_pow_eq_zero_of_support_bound F hN hp hpN hk,
        RHTower.SelbergClass.one_eulerLogCoeff_apply])
  exact heq.trans RHTower.SelbergClass.one_coeff

end GaloisForLFunctions.SelbergClass
