import GaloisForLFunctions.RHTower.PolynomialFockCriticalPrimeSampling

/-!
# Critical-prime incidence as an atomic Toeplitz quadratic form

The positive sampling incidence has quadratic form equal to the complete weighted normalized-kernel
evaluation energy.  This is the exact operator-to-measure identification needed before applying
the doubling-Fock Toeplitz Schatten criterion.
-/

open scoped InnerProductSpace ComplexConjugate

namespace RHTower

noncomputable section

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Exact quadratic form of any bounded critical-prime sampler incidence. -/
theorem re_inner_criticalPrimeSamplingIncidence_apply_eq_tsum_normSq
    (S : H →L[ℂ] CriticalPrimeEllTwo) (f : H) :
    (inner ℂ (criticalPrimeSamplingIncidence S f) f).re =
      ∑' p : Nat.Primes, ‖S f p‖ ^ 2 := by
  have hnorm : ‖S f‖ ^ (2 : ℝ) = ∑' p : Nat.Primes, ‖S f p‖ ^ (2 : ℝ) := by
    simpa using lp.norm_rpow_eq_tsum (p := 2) (E := fun _ : Nat.Primes => ℂ)
      (by norm_num) (S f)
  rw [criticalPrimeSamplingIncidence, comp_apply, adjoint_inner_left,
    inner_self_eq_norm_sq_to_K]
  have hcast : ((↑‖S f‖ ^ 2 : ℂ)).re = ‖S f‖ ^ 2 := by
    rw [← Complex.ofReal_pow]
    rfl
  calc
    ((↑‖S f‖ ^ 2 : ℂ)).re = ‖S f‖ ^ 2 := hcast
    _ = ∑' p : Nat.Primes, ‖S f p‖ ^ 2 := by
      simpa [Real.rpow_two] using hnorm

/-- The literal polynomial-Fock incidence is exactly the atomic weighted normalized-kernel
quadratic form, with no abstract Toeplitz placeholder. -/
theorem re_inner_polynomialCriticalPrimeSamplingIncidence_apply_eq_tsum
    (m : ℝ) (hm : 4 ≤ m) (f : MomentFock) :
    (inner ℂ (polynomialCriticalPrimeSamplingIncidence m hm f) f).re =
      ∑' p : Nat.Primes,
        criticalPrimeSamplingWeight p *
          ‖inner ℂ
            (criticalPrimeMomentFockKernel
              (polynomialMomentFockData m (by linarith)) p) f‖ ^ 2 := by
  rw [polynomialCriticalPrimeSamplingIncidence,
    re_inner_criticalPrimeSamplingIncidence_apply_eq_tsum_normSq]
  apply tsum_congr
  intro p
  rw [polynomialCriticalPrimeSamplingOperator_apply,
    criticalPrimeKernelRestriction_apply, norm_mul, mul_pow,
    Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (criticalPrimeSamplingWeight_pos p).le]

end

end RHTower
