import GaloisForLFunctions.RHTower.ChebyshevMomentCorpusBridge
import GaloisForLFunctions.RHTower.XiTraceHankelCriterion

open Complex Polynomial
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Polynomial probe of the actual xi central reciprocal-square divisor. -/
def xiCentralPolynomialMomentTrace (p : Polynomial ℝ) : ℂ :=
  ∑' ρ : ↥(MeromorphicOn.divisor xi Set.univ).support,
    (((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) : ℂ) *
      xiCentralReciprocalSquare (ρ : ℂ) *
      evalRealPolynomial p (xiCentralReciprocalSquare (ρ : ℂ))

theorem xiCentralPolynomialMomentTrace_eq_moments (p : Polynomial ℝ) :
    xiCentralPolynomialMomentTrace p =
      ∑ k ∈ p.support, (p.coeff k : ℂ) * xiCentralReciprocalMoment k := by
  let D := MeromorphicOn.divisor xi Set.univ
  let lam : ↥D.support → ℂ := fun ρ => xiCentralReciprocalSquare (ρ : ℂ)
  let term : ℕ → ↥D.support → ℂ := fun k ρ =>
    ((D (ρ : ℂ) : ℝ) : ℂ) * lam ρ ^ (k + 1)
  have hmoment (k : ℕ) : Summable (term k) := by
    simpa only [D, lam, term] using xi_central_reciprocal_moment_summable k
  rw [xiCentralPolynomialMomentTrace]
  calc
    (∑' ρ : ↥D.support,
      ((D (ρ : ℂ) : ℝ) : ℂ) * lam ρ * evalRealPolynomial p (lam ρ)) =
      ∑' ρ : ↥D.support, ∑ k ∈ p.support, (p.coeff k : ℂ) * term k ρ := by
      apply tsum_congr
      intro ρ
      rw [evalRealPolynomial, Polynomial.eval_map, Polynomial.eval₂_eq_sum,
        Polynomial.sum_def, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      simp only [term, coe_algebraMap]
      ring
    _ = ∑ k ∈ p.support, (p.coeff k : ℂ) * ∑' ρ : ↥D.support, term k ρ := by
      rw [Summable.tsum_finsetSum (fun k _ => (hmoment k).mul_left (p.coeff k : ℂ))]
      apply Finset.sum_congr rfl
      intro k hk
      rw [tsum_mul_left]
    _ = ∑ k ∈ p.support, (p.coeff k : ℂ) * xiCentralReciprocalMoment k := by
      simp only [xiCentralReciprocalMoment, D, lam, term]

theorem xiCentralChebyshevMomentTrace_eq_re_polynomialTrace (n : ℕ) :
    xiCentralChebyshevMomentTrace n =
      (xiCentralPolynomialMomentTrace (HTGeometry.chebyshevTraceKernelPolynomial n)).re := by
  rw [xiCentralPolynomialMomentTrace_eq_moments, xiCentralChebyshevMomentTrace,
    HTGeometry.chebyshevShiftedMomentTrace, HTGeometry.momentFunctional_eq_support_sum,
    Complex.re_sum]
  apply Finset.sum_congr rfl
  intro k hk
  simp

theorem xiCentralChebyshevMomentTrace_eq_zeroModes (n : ℕ) :
    xiCentralChebyshevMomentTrace n =
      (∑' ρ : ↥(MeromorphicOn.divisor xi Set.univ).support,
        (((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) : ℂ) *
          xiCentralReciprocalSquare (ρ : ℂ) *
          (Chebyshev.T ℂ (n : ℤ)).eval
            (1 - 2 * xiCentralReciprocalSquare (ρ : ℂ))).re := by
  rw [xiCentralChebyshevMomentTrace_eq_re_polynomialTrace,
    xiCentralPolynomialMomentTrace]
  congr 1
  apply tsum_congr
  intro ρ
  congr 1
  simp [evalRealPolynomial, HTGeometry.chebyshevTraceKernelPolynomial,
    Polynomial.map_mul, Polynomial.map_comp, Chebyshev.map_T]

theorem primeArchChebyshevMomentTrace_eq_zeroModes (n : ℕ) :
    primeArchChebyshevMomentTrace n =
      (∑' ρ : ↥(MeromorphicOn.divisor xi Set.univ).support,
        (((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) : ℂ) *
          xiCentralReciprocalSquare (ρ : ℂ) *
          (Chebyshev.T ℂ (n : ℤ)).eval
            (1 - 2 * xiCentralReciprocalSquare (ρ : ℂ))).re := by
  rw [primeArchChebyshevMomentTrace_eq_xi,
    xiCentralChebyshevMomentTrace_eq_zeroModes]

end

end RHTower
