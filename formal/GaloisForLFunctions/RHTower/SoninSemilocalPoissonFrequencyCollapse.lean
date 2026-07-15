import GaloisForLFunctions.RHTower.SoninSemilocalPoissonExpansion

/-!
# Prime-log frequency form of the semilocal Poisson expansion

This module collapses the product Fourier phase of an integer prime packet to the single frequency
`sum_p m_p log p`.  The resulting capstone is equation (8) of the semilocal all-even Jacobi card in
its literal finite-lattice form.
-/

noncomputable section

open scoped BigOperators

namespace RHTower

/-- A finite-prime complex Fourier term is its positive Poisson weight times the exponential of the
single prime-log frequency. -/
theorem semilocalFinitePrimePoissonFourierTerm_eq_weight_mul_exp
    {n : ℕ} (p : Fin n → ℕ) (s : ℝ) (m : Fin n → ℤ) :
    semilocalFinitePrimePoissonFourierTerm p s m =
      (semilocalFinitePrimePoissonWeight p m : ℂ) *
        Complex.exp
          (((semilocalFinitePrimeLogFrequency p m * s : ℝ) : ℂ) * Complex.I) := by
  unfold semilocalFinitePrimePoissonFourierTerm
  simp_rw [semilocalBilateralPoissonTerm]
  rw [Finset.prod_mul_distrib]
  congr 1
  · norm_cast
  · simp_rw [semilocalPrimePhase, ← Complex.exp_int_mul]
    rw [← Complex.exp_sum]
    congr 1
    unfold semilocalFinitePrimeLogFrequency
    push_cast
    rw [Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _hi
    ring

/-- **Exact finite-prime Poisson expansion in prime-log frequency form.** -/
theorem semilocalFinitePrimePoissonExpansion_frequency
    {n : ℕ} (p : Fin n → ℕ) (hprime : ∀ i, (p i).Prime) (s : ℝ) :
    (∏ i, (Complex.normSq
        (1 - (semilocalPrimePoissonRatio (p i) : ℂ) *
          semilocalPrimePhase (p i) s) : ℂ)⁻¹) =
      (∏ i, (1 - (semilocalPrimePoissonRatio (p i) : ℂ) ^ 2)⁻¹) *
        ∑' m : Fin n → ℤ,
          (semilocalFinitePrimePoissonWeight p m : ℂ) *
            Complex.exp
              (((semilocalFinitePrimeLogFrequency p m * s : ℝ) : ℂ) * Complex.I) := by
  rw [semilocalFinitePrimePoissonExpansion p hprime s]
  congr 1
  apply tsum_congr
  intro m
  exact semilocalFinitePrimePoissonFourierTerm_eq_weight_mul_exp p s m

end RHTower
