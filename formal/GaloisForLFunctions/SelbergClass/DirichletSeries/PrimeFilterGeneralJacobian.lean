import GaloisForLFunctions.SelbergClass.DirichletSeries.PrimeFilterCoefficientField
import GaloisForLFunctions.HTGeometry.ArithmeticFunctionGeneralJacobian

/-!
# Prime-filter Jacobian criterion for arbitrary Dirichlet coefficients

A polynomial uses finitely many coefficients, all killed by a filter-large set of prime
derivations. A nonsingular prime-value packet in that set proves independence over its common
kernel. Descending each polynomial relation this way extends the general arithmetic-function
Jacobian criterion from finite prime exceptions to arbitrary prime filters.
-/

namespace GaloisForLFunctions.SelbergClass.DirichletSeries

open ArithmeticFunction HTGeometry Filter
open scoped Classical

noncomputable section

/-- Independence over common kernels chosen inside every filter-large prime set descends to
independence over the entire filter coefficient field. -/
theorem algebraicIndependent_over_filterField_of_commonKernels
    {I : Type*} [Fintype I] [DecidableEq I]
    (F : Filter Nat.Primes) (x : I → arithmeticFunctionFractionField)
    (hlocal : ∀ S : Set Nat.Primes, S ∈ F →
      ∃ points : I → Nat.Primes, (∀ i, points i ∈ S) ∧
        AlgebraicIndependent (primeCommonKernelField points) x) :
    AlgebraicIndependent (primeFilterCoefficientField F) x := by
  rw [algebraicIndependent_iff]
  intro P hP
  obtain ⟨points, hpoints, hAI⟩ := hlocal _
    (eventually_polynomial_coeff_derivation_eq_zero F P)
  let K := primeCommonKernelField points
  let c : (I →₀ ℕ) → K := fun s => ⟨(P.coeff s).1, fun j => hpoints j s⟩
  let Q : MvPolynomial I K := ∑ s ∈ P.support, MvPolynomial.monomial s (c s)
  have hmap : MvPolynomial.map (algebraMap K arithmeticFunctionFractionField) Q =
      MvPolynomial.map
        (algebraMap (primeFilterCoefficientField F) arithmeticFunctionFractionField) P := by
    calc
      _ = ∑ s ∈ P.support, MvPolynomial.monomial s
          ((P.coeff s).1 : arithmeticFunctionFractionField) := by
        simp only [Q, map_sum, MvPolynomial.map_monomial]
        rfl
      _ = _ := by
        conv_rhs => rw [P.as_sum]
        simp only [map_sum, MvPolynomial.map_monomial]
        rfl
  have hQ : MvPolynomial.aeval x Q = 0 := by
    have heval := congrArg (MvPolynomial.eval x) hmap
    have heq : MvPolynomial.aeval x Q = MvPolynomial.aeval x P := by
      simpa only [MvPolynomial.aeval_def, MvPolynomial.eval_map] using heval
    exact heq.trans hP
  have hzero := hAI.eq_zero_of_aeval_eq_zero Q hQ
  apply MvPolynomial.map_injective
    (algebraMap (primeFilterCoefficientField F) arithmeticFunctionFractionField)
    (FaithfulSMul.algebraMap_injective _ _)
  rw [← hmap, hzero, _root_.map_zero, _root_.map_zero]

/-- Independence of the prime values modulo a filter suffices for algebraic independence of
arbitrary arithmetic functions over its coefficient field. Composite coefficients are unrestricted:
the constant term of the prime Jacobian already supplies its nonzero determinant. -/
theorem algebraicIndependent_fractionArithmetic_of_filterPrimeValues
    {I : Type*} [Fintype I] [DecidableEq I]
    (F : Filter Nat.Primes) (g : I → ArithmeticFunction ℂ)
    (h : FilterCoefficientIndependent F (fun i p => g i (p : ℕ))) :
    AlgebraicIndependent (primeFilterCoefficientField F)
      (fun i => algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField (g i)) := by
  apply algebraicIndependent_over_filterField_of_commonKernels F
  intro S hS
  obtain ⟨points, hpoints, hpacket⟩ := h.exists_fullRank_packet hS
  refine ⟨points, hpoints, algebraicIndependent_fractionArithmetic_over_commonKernel g points ?_⟩
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hpacket)

#print axioms algebraicIndependent_over_filterField_of_commonKernels
#print axioms algebraicIndependent_fractionArithmetic_of_filterPrimeValues

end
end GaloisForLFunctions.SelbergClass.DirichletSeries
