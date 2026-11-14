import GaloisForLFunctions.SelbergClass.DirichletSeries.PrimeDensityCoefficientField
import GaloisForLFunctions.SelbergClass.DirichletSeries.PrimeFilterVandermonde
import GaloisForLFunctions.HTGeometry.CofinitePacketVandermonde

/-!
# Prime-zeta logarithmic jets over sparse-prime coefficients

The existing prime indicator and all its finite logarithmic jet families remain algebraically
independent over the field of fractions with density-zero prime activity. The same statement
holds for polynomial weights in the prime itself. The enlarged coefficient field contains the
finite-prime field but also permits infinite exceptional prime sets of relative density zero.
-/

namespace GaloisForLFunctions.SelbergClass.DirichletSeries

open ArithmeticFunction HTGeometry Filter
open scoped Classical

noncomputable section

/-- Every finite family of powers of an injective prime label remains algebraically independent
over the standard density-zero prime coefficient field. -/
theorem algebraicIndependent_primePowers_over_densityField
    (u : Nat.Primes → ℂ) (hu : Function.Injective u) (n : ℕ) :
    AlgebraicIndependent (primeDensityCoefficientField primeCountingWindow)
      (fun i : Fin n => algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
        (arithmeticOfPrimeColumn (fun p => u p ^ (i : ℕ)))) := by
  letI := primeWindowDensityFilter_neBot primeCountingWindow primeCountingWindow_card_tendsto
  exact algebraicIndependent_primePowers_over_filterField _
    (primeWindowDensityFilter_le_cofinite primeCountingWindow primeCountingWindow_card_tendsto)
    u hu n

/-- The formal prime Dirichlet series with coefficient weights `1, p, …, p^(n-1)` are algebraically
independent even when coefficients may involve density-zero sets of primes. -/
theorem algebraicIndependent_primePolynomialWeights_over_densityField (n : ℕ) :
    AlgebraicIndependent (primeDensityCoefficientField primeCountingWindow)
      (fun i : Fin n => algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
        (arithmeticOfPrimeColumn (fun p => (p.1 : ℂ) ^ (i : ℕ)))) := by
  apply algebraicIndependent_primePowers_over_densityField _ _ n
  intro p q hpq
  apply Subtype.ext
  exact_mod_cast hpq

/-- The logarithmic jet of the prime indicator is the corresponding prime-supported power column. -/
theorem rotatedLogJet_primeIndicator_eq_primeColumn (k : ℕ) :
    primeProfileRotatedLogJet k primeIndicatorProfile =
      arithmeticOfPrimeColumn (fun p => (Complex.I * (Real.log p.1 : ℂ)) ^ k) := by
  ext n
  by_cases hn : n.Prime <;>
    simp [primeProfileRotatedLogJet_apply, primeIndicatorProfile_apply,
      arithmeticOfPrimeColumn, hn]

/-- All finite logarithmic jet families of the prime-zeta coefficient stream are algebraically
independent over the density-zero prime coefficient field. -/
theorem algebraicIndependent_primeIndicatorJets_over_densityField (n : ℕ) :
    AlgebraicIndependent (primeDensityCoefficientField primeCountingWindow)
      (fun i : Fin n => algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
        (primeProfileRotatedLogJet (i : ℕ) primeIndicatorProfile)) := by
  simp only [rotatedLogJet_primeIndicator_eq_primeColumn]
  apply algebraicIndependent_primePowers_over_densityField _ _ n
  intro p q hpq
  apply log_prime_injective
  have him := congrArg Complex.im hpq
  simpa only [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, one_mul, zero_add] using him

#print axioms algebraicIndependent_primePolynomialWeights_over_densityField
#print axioms algebraicIndependent_primeIndicatorJets_over_densityField

end
end GaloisForLFunctions.SelbergClass.DirichletSeries
