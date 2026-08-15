import GaloisForLFunctions.RHTower.BakerGeneralProof.PolynomialAuxiliaryBounds
import GaloisForLFunctions.RHTower.BakerGeneralProof.ExponentialPolynomial
import GaloisForLFunctions.RHTower.BakerGeneralProof.ExponentialPolynomialInterpolation

/-!
# Terminal exponential-polynomial form of the full Baker auxiliary function

At zero component index, the additive coordinate of every column becomes a polynomial weight and
the exponential coordinates combine into one additive frequency.  The assumed rational linear
independence of the chosen logarithms makes those frequencies injective.  Hence a nonzero Siegel
vector gives a nonzero polynomially weighted exponential function, allowing the terminal
gap-free zero estimate to be applied without any frequency-separation hypothesis.
-/

open scoped Classical
open BigOperators NumberField
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.RHTower.BakerGeneralProof

/-- Additive frequency of an exponential-column monomial on the auxiliary curve. -/
noncomputable def SolvedRelation.exponentialFrequency
    (R : SolvedRelation) {V : ℕ} (m : R.ExponentialColumn V) : ℂ :=
  ∑ i, (m i : ℂ) * R.lambda i

/-- Rational linear independence of the logarithms makes the bounded exponential frequencies
injective. -/
theorem SolvedRelation.exponentialFrequency_injective
    (R : SolvedRelation) {V : ℕ} : Function.Injective (R.exponentialFrequency (V := V)) := by
  intro m m' hfreq
  funext i
  apply Fin.ext
  have hsum : ∑ i : Fin R.n, ((m i : ℚ) - (m' i : ℚ)) • R.lambda i = 0 := by
    calc
      ∑ i : Fin R.n, ((m i : ℚ) - (m' i : ℚ)) • R.lambda i =
          R.exponentialFrequency m - R.exponentialFrequency m' := by
        unfold SolvedRelation.exponentialFrequency
        simp only [Rat.smul_def, Rat.cast_sub]
        change (∑ i : Fin R.n, (((m i : ℂ) - (m' i : ℂ)) * R.lambda i)) =
          ∑ i : Fin R.n, (m i : ℂ) * R.lambda i -
            ∑ i : Fin R.n, (m' i : ℂ) * R.lambda i
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        rw [sub_mul]
      _ = 0 := sub_eq_zero.mpr hfreq
  have hcoeff := (linearIndependent_iff'.mp R.lambda_independent)
    Finset.univ (fun i => (m i : ℚ) - (m' i : ℚ)) hsum
  have hi := hcoeff i (Finset.mem_univ i)
  exact_mod_cast sub_eq_zero.mp hi

/-- Polynomial coefficient at one exponential frequency, obtained by grouping all additive
degrees of the auxiliary vector. -/
noncomputable def SolvedRelation.polynomialAuxiliaryCoefficient
    (R : SolvedRelation) {U V : ℕ}
    (eta : R.AuxiliaryColumn U V → 𝓞 R.CoefficientField)
    (m : R.ExponentialColumn V) : Polynomial ℂ :=
  ∑ a : Fin U, Polynomial.monomial (a : ℕ)
    (R.embedding ((algebraMap (𝓞 R.CoefficientField) R.CoefficientField) (eta (a, m))))

/-- Exact terminal expansion of the zero component-jet auxiliary function. -/
theorem SolvedRelation.polynomialComponentJetAuxiliaryFunction_zero_expansion
    (R : SolvedRelation) (c : ℤ) {U V : ℕ}
    (eta : R.AuxiliaryColumn U V → 𝓞 R.CoefficientField) (z : ℂ) :
    R.polynomialComponentJetAuxiliaryFunction c (fun _ => 0) eta z =
      ∑ col, R.embedding ((algebraMap (𝓞 R.CoefficientField) R.CoefficientField) (eta col)) *
        z ^ (col.1 : ℕ) *
          Complex.exp (R.exponentialFrequency col.2 * z) := by
  unfold SolvedRelation.polynomialComponentJetAuxiliaryFunction
    SolvedRelation.auxiliaryFunction SolvedRelation.complexify
    SolvedRelation.polynomialComponentJetAuxiliaryPolynomial
    SolvedRelation.componentJetMonomial
  simp only [map_sum, map_mul, MvPolynomial.map_C,
    Function.iterate_zero_apply, SolvedRelation.nonconstantEigenProduct_zero, map_one, one_mul]
  apply Finset.sum_congr rfl
  intro col hcol
  simp only [MvPolynomial.eval_C, map_pow, MvPolynomial.map_X, MvPolynomial.eval_X]
  unfold SolvedRelation.exponentialMonomial
  rw [map_prod]
  rw [map_prod]
  simp_rw [map_pow]
  simp only [MvPolynomial.eval_X, MvPolynomial.map_X]
  change R.embedding ((algebraMap (𝓞 R.CoefficientField) R.CoefficientField) (eta col)) *
      (z ^ (col.1 : ℕ) *
        ∏ i, (R.auxiliaryPoint z (some i)) ^ (col.2 i : ℕ)) = _
  simp only [SolvedRelation.auxiliaryPoint]
  have hprod : (∏ i, Complex.exp (R.lambda i * z) ^ (col.2 i : ℕ)) =
      Complex.exp (R.exponentialFrequency col.2 * z) := by
    simp_rw [← Complex.exp_nat_mul]
    rw [← Complex.exp_sum]
    congr 1
    unfold SolvedRelation.exponentialFrequency
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hprod]
  ring

/-- The terminal function is the standard finite polynomial--exponential sum used by the
gap-free zero machinery. -/
theorem SolvedRelation.polynomialComponentJetAuxiliaryFunction_zero_eq_exponentialPolynomial
    (R : SolvedRelation) (c : ℤ) {U V : ℕ}
    (eta : R.AuxiliaryColumn U V → 𝓞 R.CoefficientField) :
    R.polynomialComponentJetAuxiliaryFunction c (fun _ => 0) eta =
      exponentialPolynomial (R.polynomialAuxiliaryCoefficient eta) R.exponentialFrequency := by
  funext z
  rw [R.polynomialComponentJetAuxiliaryFunction_zero_expansion]
  unfold exponentialPolynomial SolvedRelation.polynomialAuxiliaryCoefficient
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp only [polyExpC_apply, Polynomial.eval_finsetSum,
    Polynomial.eval_monomial, Finset.sum_mul]

/-- Coefficients recover the corresponding additive-degree entry of the Siegel vector. -/
theorem SolvedRelation.polynomialAuxiliaryCoefficient_coeff
    (R : SolvedRelation) {U V : ℕ}
    (eta : R.AuxiliaryColumn U V → 𝓞 R.CoefficientField)
    (a : Fin U) (m : R.ExponentialColumn V) :
    (R.polynomialAuxiliaryCoefficient eta m).coeff (a : ℕ) =
      R.embedding ((algebraMap (𝓞 R.CoefficientField) R.CoefficientField) (eta (a, m))) := by
  unfold SolvedRelation.polynomialAuxiliaryCoefficient
  simp [Polynomial.coeff_monomial]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hba
    have hne : (b : ℕ) ≠ (a : ℕ) := fun h => hba (Fin.ext h)
    simp [hne]
  · simp

/-- A nonzero full Siegel vector gives a nonzero terminal polynomial-coefficient family. -/
theorem SolvedRelation.polynomialAuxiliaryCoefficient_ne_zero_of_eta_ne_zero
    (R : SolvedRelation) {U V : ℕ}
    (eta : R.AuxiliaryColumn U V → 𝓞 R.CoefficientField) (heta : eta ≠ 0) :
    R.polynomialAuxiliaryCoefficient eta ≠ 0 := by
  intro hzero
  apply heta
  funext col
  rcases col with ⟨a, m⟩
  have hpoly : R.polynomialAuxiliaryCoefficient eta m = 0 := congrFun hzero m
  have hcoeff := congrArg (fun P : Polynomial ℂ => P.coeff (a : ℕ)) hpoly
  rw [R.polynomialAuxiliaryCoefficient_coeff eta a m] at hcoeff
  apply RingOfIntegers.coe_injective
  exact R.embedding.injective (by simpa using hcoeff)

/-- The terminal zero-jet auxiliary function is nonzero whenever its Siegel vector is nonzero. -/
theorem SolvedRelation.polynomialComponentJetAuxiliaryFunction_zero_ne_zero_of_eta_ne_zero
    (R : SolvedRelation) (c : ℤ) {U V : ℕ}
    (eta : R.AuxiliaryColumn U V → 𝓞 R.CoefficientField) (heta : eta ≠ 0) :
    R.polynomialComponentJetAuxiliaryFunction c (fun _ => 0) eta ≠ 0 := by
  rw [R.polynomialComponentJetAuxiliaryFunction_zero_eq_exponentialPolynomial]
  exact expPoly_sum_ne_zero R.exponentialFrequency (R.polynomialAuxiliaryCoefficient eta)
    R.exponentialFrequency_injective
    (R.polynomialAuxiliaryCoefficient_ne_zero_of_eta_ne_zero eta heta)

/-- The additive-degree cutoff is an exact degree cutoff for every terminal coefficient
polynomial. -/
theorem SolvedRelation.polynomialAuxiliaryCoefficient_natDegree_lt
    (R : SolvedRelation) {U V : ℕ} (hU : 0 < U)
    (eta : R.AuxiliaryColumn U V → 𝓞 R.CoefficientField)
    (m : R.ExponentialColumn V) :
    (R.polynomialAuxiliaryCoefficient eta m).natDegree < U := by
  unfold SolvedRelation.polynomialAuxiliaryCoefficient
  have hdegree : (∑ a : Fin U, Polynomial.monomial (a : ℕ)
      (R.embedding ((algebraMap (𝓞 R.CoefficientField) R.CoefficientField) (eta (a, m))))).natDegree ≤
      U - 1 := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro a ha
    exact (Polynomial.natDegree_monomial_le _).trans (by omega)
  omega

end GaloisForLFunctions.RHTower.BakerGeneralProof
