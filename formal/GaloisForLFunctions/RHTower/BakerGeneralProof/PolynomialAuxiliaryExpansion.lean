import GaloisForLFunctions.RHTower.BakerGeneralProof.PolynomialAuxiliaryTerminal

/-!
# Exact analytic expansion of the full Baker component jets

Every solved component jet of the auxiliary polynomial is a finite sum over the
additive--exponential columns.  The constant component contributes a binomial family of
additive-lowering terms, the nonconstant components contribute one diagonal eigenvalue product, and
the exponential coordinates combine into a single additive frequency.  Evaluating this expansion on
the analytic curve gives a closed polynomial--exponential formula, from which a boundary bound on a
closed disc follows termwise from the houses of the algebraic factors.
-/

open scoped Classical
open BigOperators NumberField

namespace GaloisForLFunctions.RHTower.BakerGeneralProof

/-- Coefficient of the `k`-th additive-lowering term of an iterated constant component. -/
noncomputable def SolvedRelation.jetLoweringCoeff
    (R : SolvedRelation) (c : ℤ) {V : ℕ} (r a k : ℕ) (m : R.ExponentialColumn V) :
    R.CoefficientField :=
  (Nat.choose r k : R.CoefficientField) * (a.descFactorial k : R.CoefficientField) *
    R.integerScalar c ^ k * R.componentEigenvalue c none m ^ (r - k)

theorem SolvedRelation.auxiliaryFunction_sum
    (R : SolvedRelation) {ι : Type*} (s : Finset ι)
    (P : ι → MvPolynomial R.Variable R.CoefficientField) (z : ℂ) :
    R.auxiliaryFunction (∑ i ∈ s, P i) z = ∑ i ∈ s, R.auxiliaryFunction (P i) z := by
  simp [SolvedRelation.auxiliaryFunction, SolvedRelation.complexify, map_sum]

/-- Value of an additive--exponential monomial on the analytic auxiliary curve. -/
theorem SolvedRelation.auxiliaryFunction_additivePowerMonomial
    (R : SolvedRelation) (b : ℕ) {V : ℕ} (m : R.ExponentialColumn V) (z : ℂ) :
    R.auxiliaryFunction (MvPolynomial.X none ^ b * R.exponentialMonomial m) z =
      z ^ b * Complex.exp (R.exponentialFrequency m * z) := by
  have hval : R.auxiliaryFunction (MvPolynomial.X none ^ b * R.exponentialMonomial m) z =
      (R.auxiliaryPoint z none) ^ b *
        ∏ i, (R.auxiliaryPoint z (some i)) ^ ((m i : ℕ)) := by
    unfold SolvedRelation.auxiliaryFunction SolvedRelation.complexify
      SolvedRelation.exponentialMonomial
    simp
  rw [hval]
  have hprod : (∏ i, (R.auxiliaryPoint z (some i)) ^ ((m i : ℕ))) =
      Complex.exp (R.exponentialFrequency m * z) := by
    simp only [SolvedRelation.auxiliaryPoint]
    simp_rw [← Complex.exp_nat_mul]
    rw [← Complex.exp_sum]
    congr 1
    unfold SolvedRelation.exponentialFrequency
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hprod]
  simp [SolvedRelation.auxiliaryPoint]

/-- Exact analytic value of a canonical component-jet monomial. -/
theorem SolvedRelation.auxiliaryFunction_componentJetMonomial
    (R : SolvedRelation) (c : ℤ) {V : ℕ}
    (nu : R.Direction → ℕ) (a : ℕ) (m : R.ExponentialColumn V) (z : ℂ) :
    R.auxiliaryFunction (R.componentJetMonomial c nu a m) z =
      R.embedding (R.nonconstantEigenProduct c nu m) *
        ∑ k ∈ Finset.range (nu none + 1),
          R.embedding (R.jetLoweringCoeff c (nu none) a k m) *
            (z ^ (a - k) * Complex.exp (R.exponentialFrequency m * z)) := by
  unfold SolvedRelation.componentJetMonomial
  rw [R.auxiliaryFunction_C_mul]
  congr 1
  rw [R.componentDerivation_none_iterate_additivePowerMonomial, R.auxiliaryFunction_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [R.auxiliaryFunction_C_mul, R.auxiliaryFunction_additivePowerMonomial]
  rfl

/-- Exact finite expansion of a full component-jet auxiliary function. -/
theorem SolvedRelation.polynomialComponentJetAuxiliaryFunction_expansion
    (R : SolvedRelation) (c : ℤ) {U V : ℕ}
    (nu : R.Direction → ℕ) (eta : R.AuxiliaryColumn U V → 𝓞 R.CoefficientField) (z : ℂ) :
    R.polynomialComponentJetAuxiliaryFunction c nu eta z =
      ∑ col : R.AuxiliaryColumn U V,
        R.embedding ((algebraMap (𝓞 R.CoefficientField) R.CoefficientField) (eta col)) *
          (R.embedding (R.nonconstantEigenProduct c nu col.2) *
            ∑ k ∈ Finset.range (nu none + 1),
              R.embedding (R.jetLoweringCoeff c (nu none) (col.1 : ℕ) k col.2) *
                (z ^ ((col.1 : ℕ) - k) *
                  Complex.exp (R.exponentialFrequency col.2 * z))) := by
  unfold SolvedRelation.polynomialComponentJetAuxiliaryFunction
    SolvedRelation.polynomialComponentJetAuxiliaryPolynomial
  rw [R.auxiliaryFunction_sum]
  refine Finset.sum_congr rfl fun col _ => ?_
  rw [R.auxiliaryFunction_C_mul, R.auxiliaryFunction_componentJetMonomial]

/-- Explicit finite boundary bound for a full component-jet auxiliary function. -/
noncomputable def SolvedRelation.jetAnalyticBound
    (R : SolvedRelation) (c : ℤ) {U V : ℕ}
    (nu : R.Direction → ℕ) (eta : R.AuxiliaryColumn U V → 𝓞 R.CoefficientField)
    (radius : ℝ) : ℝ :=
  ∑ col : R.AuxiliaryColumn U V,
    house ((algebraMap (𝓞 R.CoefficientField) R.CoefficientField) (eta col)) *
      (house (R.nonconstantEigenProduct c nu col.2) *
        ∑ k ∈ Finset.range (nu none + 1),
          house (R.jetLoweringCoeff c (nu none) (col.1 : ℕ) k col.2) *
            (radius ^ ((col.1 : ℕ) - k) *
              Real.exp (‖R.exponentialFrequency col.2‖ * radius)))

theorem SolvedRelation.jetAnalyticBound_nonneg
    (R : SolvedRelation) (c : ℤ) {U V : ℕ}
    (nu : R.Direction → ℕ) (eta : R.AuxiliaryColumn U V → 𝓞 R.CoefficientField)
    {radius : ℝ} (hradius : 0 ≤ radius) :
    0 ≤ R.jetAnalyticBound c nu eta radius := by
  unfold SolvedRelation.jetAnalyticBound
  refine Finset.sum_nonneg fun col _ => mul_nonneg (house_nonneg _) ?_
  refine mul_nonneg (house_nonneg _) (Finset.sum_nonneg fun k _ => ?_)
  exact mul_nonneg (house_nonneg _) (mul_nonneg (pow_nonneg hradius _) (Real.exp_nonneg _))

/-- On a closed disc the full component jet is bounded by its explicit finite house sum. -/
theorem SolvedRelation.norm_polynomialComponentJetAuxiliaryFunction_le
    (R : SolvedRelation) (c : ℤ) {U V : ℕ}
    (nu : R.Direction → ℕ) (eta : R.AuxiliaryColumn U V → 𝓞 R.CoefficientField)
    {radius : ℝ} {z : ℂ} (hz : ‖z‖ ≤ radius) :
    ‖R.polynomialComponentJetAuxiliaryFunction c nu eta z‖ ≤
      R.jetAnalyticBound c nu eta radius := by
  have hradius : 0 ≤ radius := le_trans (norm_nonneg _) hz
  rw [R.polynomialComponentJetAuxiliaryFunction_expansion]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun col _ => ?_)
  rw [norm_mul]
  refine mul_le_mul (norm_embedding_le_house _ R.embedding) ?_ (norm_nonneg _) (house_nonneg _)
  rw [norm_mul]
  refine mul_le_mul (norm_embedding_le_house _ R.embedding) ?_ (norm_nonneg _) (house_nonneg _)
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun k _ => ?_)
  rw [norm_mul, norm_mul, norm_pow]
  refine mul_le_mul (norm_embedding_le_house _ R.embedding) ?_
    (mul_nonneg (pow_nonneg (norm_nonneg _) _) (norm_nonneg _)) (house_nonneg _)
  refine mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hz _) ?_ (norm_nonneg _)
    (pow_nonneg hradius _)
  calc
    ‖Complex.exp (R.exponentialFrequency col.2 * z)‖ ≤
        Real.exp ‖R.exponentialFrequency col.2 * z‖ := Complex.norm_exp_le_exp_norm _
    _ ≤ Real.exp (‖R.exponentialFrequency col.2‖ * radius) := by
        refine Real.exp_le_exp.mpr ?_
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left hz (norm_nonneg _)

end GaloisForLFunctions.RHTower.BakerGeneralProof
