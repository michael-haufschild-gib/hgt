import GaloisForLFunctions.RHTower.LiouvilleDirichletSeries
import Mathlib.NumberTheory.Chebyshev

/-!
# Signed cofactor transport for the literal prime-counting error

The actual Liouville pairing R(N)=sum(n<=N) lambda(n)(theta(N/n)-N/n) has exact
multiplicative transport. For every positive integer multiplier a, R(aN)-lambda(a)R(N)
is precisely the sum over cofactors not divisible by a. At a prime, the left side is
R(pN)+R(N). No sign, decay, or norm assumption is used.

This is a derived finite-sum bridge, not a new RH producer. The excluded-cofactor
remainder is retained in full. Numerical failures of suppression, amplification, and
centered sign transport are not inputs to these proofs. Controlling this remainder at
all scales remains open.
-/

open scoped BigOperators
namespace RHTower
noncomputable section

/-- Literal Liouville coefficients paired with an arbitrary real-ratio kernel. -/
def liouvilleCofactorSum (K : ℝ → ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, liouvilleC n * K ((N : ℝ) / n)

/-- Exact cancellation on the divisible cofactor fibre, for every positive integer multiplier. -/
theorem liouvilleCofactorSum_multiples (K : ℝ → ℂ) (k N : ℕ) :
    (∑ n ∈ Finset.Icc 1 ((k+1)*N) with (k+1) ∣ n,
      liouvilleC n * K (((k+1)*N : ℕ) / (n : ℝ))) =
    liouvilleC (k+1) * liouvilleCofactorSum K N := by
  classical
  unfold liouvilleCofactorSum
  rw [Finset.mul_sum]
  symm
  apply Finset.sum_bij (fun n _ => (k+1)*n)
  · intro n hn
    have hn := Finset.mem_Icc.mp hn
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨?_, Nat.mul_le_mul_left _ hn.2⟩, ⟨n, rfl⟩⟩
    have := Nat.mul_pos (by omega : 0 < k+1) (by omega : 0 < n)
    omega
  · intro a ha b hb hab
    exact Nat.eq_of_mul_eq_mul_left (by omega) hab
  · intro b hb
    obtain ⟨hb, m, rfl⟩ := Finset.mem_filter.mp hb
    have hb := Finset.mem_Icc.mp hb
    refine ⟨m, Finset.mem_Icc.mpr ⟨?_, ?_⟩, rfl⟩
    · by_contra h
      have hm : m = 0 := by omega
      simp [hm] at hb
    · exact Nat.le_of_mul_le_mul_left hb.2 (by omega)
  · intro n hn
    have hn := Finset.mem_Icc.mp hn
    have hk : ((k+1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show k+1 ≠ 0 by omega)
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    have hr : (((k+1)*N : ℕ) : ℝ) / (((k+1)*n : ℕ) : ℝ) = (N : ℝ)/n := by
      push_cast at hk ⊢
      field_simp
    rw [liouvilleC_mul, hr]
    ring

/-- The full dilation defect is exactly the retained nondivisible cofactor sum. -/
theorem liouvilleCofactorSum_dilation_residual (K : ℝ → ℂ) (k N : ℕ) :
    liouvilleCofactorSum K ((k+1)*N) -
      liouvilleC (k+1) * liouvilleCofactorSum K N =
    ∑ n ∈ Finset.Icc 1 ((k+1)*N) with ¬ (k+1) ∣ n,
      liouvilleC n * K (((k+1)*N : ℕ) / (n : ℝ)) := by
  classical
  have hs := Finset.sum_filter_add_sum_filter_not
    (Finset.Icc 1 ((k+1)*N)) (fun n => (k+1) ∣ n)
    (fun n => liouvilleC n * K (((k+1)*N : ℕ) / (n : ℝ)))
  rw [liouvilleCofactorSum_multiples] at hs
  change _ = liouvilleCofactorSum K ((k+1)*N) at hs
  rw [← hs]
  ring

/-- The actual Chebyshev counting-error pairing; no zero data enter its definition. -/
def liouvillePrimeCountingError (N : ℕ) : ℂ :=
  liouvilleCofactorSum (fun x => ((Chebyshev.theta x - x : ℝ) : ℂ)) N

/-- All-integer transport for the actual prime-counting error, with its complete residual. -/
theorem liouvillePrimeCountingError_dilation_residual (k N : ℕ) :
    liouvillePrimeCountingError ((k+1)*N) -
      liouvilleC (k+1) * liouvillePrimeCountingError N =
    ∑ n ∈ Finset.Icc 1 ((k+1)*N) with ¬ (k+1) ∣ n,
      liouvilleC n * (((Chebyshev.theta ((((k+1)*N : ℕ) : ℝ) / n) -
        (((k+1)*N : ℕ) : ℝ) / n : ℝ) : ℂ)) := by
  exact liouvilleCofactorSum_dilation_residual _ k N

/-- Every prime gives signed reversal plus the exact sum over cofactors it does not divide. -/
theorem liouvillePrimeCountingError_prime_residual (p : Nat.Primes) (N : ℕ) :
    liouvillePrimeCountingError ((p : ℕ)*N) + liouvillePrimeCountingError N =
    ∑ n ∈ Finset.Icc 1 ((p : ℕ)*N) with ¬ (p : ℕ) ∣ n,
      liouvilleC n * (((Chebyshev.theta ((((p : ℕ)*N : ℕ) : ℝ) / n) -
        (((p : ℕ)*N : ℕ) : ℝ) / n : ℝ) : ℂ)) := by
  have hp : ((p : ℕ)-1)+1 = (p : ℕ) := by
    have := p.property.two_le
    omega
  have hl : liouvilleC (p : ℕ) = -1 := by
    simpa using liouvilleC_prime_pow p.property 1
  have h := liouvillePrimeCountingError_dilation_residual ((p : ℕ)-1) N
  rw [hp, hl] at h
  simpa using h
end
end RHTower
