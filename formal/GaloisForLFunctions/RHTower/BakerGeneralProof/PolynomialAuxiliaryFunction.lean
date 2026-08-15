import GaloisForLFunctions.RHTower.BakerGeneralProof.PolynomialComponentJet

/-!
# Kernel transport for the full Baker auxiliary polynomial

The full additive--exponential Siegel matrix has algebraic-integer entries only after a
row-dependent clearing factor.  This module proves that factor is actually common to every
column of a fixed row, cancels it in the coefficient field, and identifies the resulting row
equation with genuine values of the component-jet auxiliary polynomial.  It then transports
those values through the selected complex embedding and records the scaled analytic derivative
recurrence needed for zero propagation.
-/

open scoped Classical
open BigOperators NumberField

namespace GaloisForLFunctions.RHTower.BakerGeneralProof

/-- Algebraic exponential part of a basis monomial at a natural sample. -/
noncomputable def SolvedRelation.baseSample
    (R : SolvedRelation) {V : ℕ} (sample : ℕ) (m : R.ExponentialColumn V) :
    R.CoefficientField :=
  ∏ i, R.baseLift i ^ ((m i : ℕ) * sample)

/-- Separate a scaled base sample into its common integer scale and algebraic base sample. -/
theorem SolvedRelation.scaledBaseSample_eq_scale_pow_mul_baseSample
    (R : SolvedRelation) (d : ℤ) {V S : ℕ}
    (sample : Fin S) (m : R.ExponentialColumn V) :
    R.scaledBaseSample d sample m =
      R.integerScalar d ^ ((sample : ℕ) * R.exponentialDegree m) *
        R.baseSample (sample : ℕ) m := by
  unfold SolvedRelation.scaledBaseSample SolvedRelation.baseSample
  simp_rw [R.scaledBase_eq_integerScalar_mul, mul_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  congr 2
  unfold SolvedRelation.exponentialDegree
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Every full auxiliary-matrix entry contains one fixed nonzero row scale. -/
theorem SolvedRelation.polynomialAuxiliaryEntry_eq_commonScale_mul
    (R : SolvedRelation) (c d : ℤ) {U V S T : ℕ}
    (row : R.AuxiliaryRow S T) (col : R.AuxiliaryColumn U V) :
    R.polynomialAuxiliaryEntry c d row col =
      R.integerScalar d ^ R.clearingBound S V *
        (R.additiveComponentJetCoefficient c (fun dir => (row.2 dir : ℕ))
          (col.1 : ℕ) (row.1 : ℕ) col.2 * R.baseSample (row.1 : ℕ) col.2) := by
  unfold SolvedRelation.polynomialAuxiliaryEntry
  rw [R.scaledBaseSample_eq_scale_pow_mul_baseSample]
  have hsum : R.clearingExponent row col.2 +
      (row.1 : ℕ) * R.exponentialDegree col.2 = R.clearingBound S V := by
    unfold SolvedRelation.clearingExponent
    exact Nat.sub_add_cancel (R.sample_degree_le_clearingBound row col.2)
  calc
    R.integerScalar d ^ R.clearingExponent row col.2 *
        R.additiveComponentJetCoefficient c (fun dir => (row.2 dir : ℕ))
          (col.1 : ℕ) (row.1 : ℕ) col.2 *
        (R.integerScalar d ^ ((row.1 : ℕ) * R.exponentialDegree col.2) *
          R.baseSample (row.1 : ℕ) col.2) =
        (R.integerScalar d ^ R.clearingExponent row col.2 *
          R.integerScalar d ^ ((row.1 : ℕ) * R.exponentialDegree col.2)) *
          (R.additiveComponentJetCoefficient c (fun dir => (row.2 dir : ℕ))
            (col.1 : ℕ) (row.1 : ℕ) col.2 * R.baseSample (row.1 : ℕ) col.2) := by
          ring
    _ = _ := by rw [← pow_add, hsum]

/-- Map one integral full-matrix kernel row into its coefficient field. -/
theorem SolvedRelation.mapped_polynomial_auxiliary_kernel
    (R : SolvedRelation) (c d : ℤ)
    (hcomp : ∀ dir, IsIntegral ℤ (R.scaledComponentCoeff c dir))
    (hbase : ∀ i, IsIntegral ℤ (R.scaledBase d i))
    {U V S T : ℕ} (eta : R.AuxiliaryColumn U V → 𝓞 R.CoefficientField)
    (hker : Matrix.mulVec (R.polynomialAuxiliaryMatrix c d hcomp hbase U V S T) eta = 0)
    (row : R.AuxiliaryRow S T) :
    ∑ col, R.polynomialAuxiliaryEntry c d row col *
      (algebraMap (𝓞 R.CoefficientField) R.CoefficientField) (eta col) = 0 := by
  have hrow := congrFun hker row
  apply_fun (algebraMap (𝓞 R.CoefficientField) R.CoefficientField) at hrow
  simpa [Matrix.mulVec, dotProduct, SolvedRelation.polynomialAuxiliaryMatrix,
    map_sum, map_mul] using hrow

/-- Cancelling the common nonzero denominator factor gives a genuine component row equation. -/
theorem SolvedRelation.polynomial_auxiliary_kernel_row_eq
    (R : SolvedRelation) (c d : ℤ)
    (hcomp : ∀ dir, IsIntegral ℤ (R.scaledComponentCoeff c dir))
    (hbase : ∀ i, IsIntegral ℤ (R.scaledBase d i))
    {U V S T : ℕ} (eta : R.AuxiliaryColumn U V → 𝓞 R.CoefficientField)
    (hker : Matrix.mulVec (R.polynomialAuxiliaryMatrix c d hcomp hbase U V S T) eta = 0)
    (hd : d ≠ 0) (row : R.AuxiliaryRow S T) :
    ∑ col, (R.additiveComponentJetCoefficient c (fun dir => (row.2 dir : ℕ))
      (col.1 : ℕ) (row.1 : ℕ) col.2 * R.baseSample (row.1 : ℕ) col.2) *
        (algebraMap (𝓞 R.CoefficientField) R.CoefficientField) (eta col) = 0 := by
  have h := R.mapped_polynomial_auxiliary_kernel c d hcomp hbase eta hker row
  have hfactor :
      ∑ col, R.polynomialAuxiliaryEntry c d row col *
        (algebraMap (𝓞 R.CoefficientField) R.CoefficientField) (eta col) =
        R.integerScalar d ^ R.clearingBound S V *
          ∑ col, (R.additiveComponentJetCoefficient c (fun dir => (row.2 dir : ℕ))
            (col.1 : ℕ) (row.1 : ℕ) col.2 * R.baseSample (row.1 : ℕ) col.2) *
              (algebraMap (𝓞 R.CoefficientField) R.CoefficientField) (eta col) := by
    simp_rw [R.polynomialAuxiliaryEntry_eq_commonScale_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro col hcol
    ring
  rw [hfactor] at h
  exact (mul_eq_zero.mp h).resolve_left
    (pow_ne_zero _ (R.integerScalar_ne_zero d hd))

/-- Polynomial whose values are the full solved-component jets of a Siegel vector. -/
noncomputable def SolvedRelation.polynomialComponentJetAuxiliaryPolynomial
    (R : SolvedRelation) (c : ℤ) {U V : ℕ}
    (nu : R.Direction → ℕ) (eta : R.AuxiliaryColumn U V → 𝓞 R.CoefficientField) :
    MvPolynomial R.Variable R.CoefficientField :=
  ∑ col, MvPolynomial.C ((algebraMap (𝓞 R.CoefficientField) R.CoefficientField) (eta col)) *
    R.componentJetMonomial c nu (col.1 : ℕ) col.2

/-- Evaluation of the polynomial jet is the corresponding finite matrix row expression. -/
theorem SolvedRelation.eval_algebraicSample_polynomialComponentJetAuxiliaryPolynomial
    (R : SolvedRelation) (c : ℤ) {U V : ℕ}
    (nu : R.Direction → ℕ) (eta : R.AuxiliaryColumn U V → 𝓞 R.CoefficientField)
    (sample : ℕ) :
    MvPolynomial.eval (R.algebraicSamplePoint sample)
      (R.polynomialComponentJetAuxiliaryPolynomial c nu eta) =
      ∑ col, (algebraMap (𝓞 R.CoefficientField) R.CoefficientField) (eta col) *
        (R.additiveComponentJetCoefficient c nu (col.1 : ℕ) sample col.2 *
          R.baseSample sample col.2) := by
  unfold SolvedRelation.polynomialComponentJetAuxiliaryPolynomial
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro col hcol
  rw [map_mul, MvPolynomial.eval_C,
    R.eval_algebraicSample_componentJetMonomial]
  simp only [SolvedRelation.baseSample]

/-- Every bounded component jet of a full Siegel auxiliary polynomial vanishes at its rows. -/
theorem SolvedRelation.eval_algebraicSample_polynomialComponentJetAuxiliaryPolynomial_eq_zero
    (R : SolvedRelation) (c d : ℤ)
    (hcomp : ∀ dir, IsIntegral ℤ (R.scaledComponentCoeff c dir))
    (hbase : ∀ i, IsIntegral ℤ (R.scaledBase d i))
    {U V S T : ℕ} (eta : R.AuxiliaryColumn U V → 𝓞 R.CoefficientField)
    (hker : Matrix.mulVec (R.polynomialAuxiliaryMatrix c d hcomp hbase U V S T) eta = 0)
    (hd : d ≠ 0) (row : R.AuxiliaryRow S T) :
    MvPolynomial.eval (R.algebraicSamplePoint (row.1 : ℕ))
      (R.polynomialComponentJetAuxiliaryPolynomial c (fun dir => (row.2 dir : ℕ)) eta) = 0 := by
  rw [R.eval_algebraicSample_polynomialComponentJetAuxiliaryPolynomial]
  have h := R.polynomial_auxiliary_kernel_row_eq c d hcomp hbase eta hker hd row
  simpa [mul_assoc, mul_left_comm, mul_comm] using h

/-- The algebraic natural sample maps exactly to the analytic auxiliary curve. -/
@[simp] theorem SolvedRelation.embedding_algebraicSamplePoint
    (R : SolvedRelation) (sample : ℕ) (v : R.Variable) :
    R.embedding (R.algebraicSamplePoint sample v) =
      R.auxiliaryPoint (sample : ℂ) v := by
  rcases v with _ | i
  · simp [SolvedRelation.algebraicSamplePoint, SolvedRelation.auxiliaryPoint]
  · simp [SolvedRelation.algebraicSamplePoint, SolvedRelation.auxiliaryPoint,
      ← Complex.exp_nat_mul, mul_comm]

/-- Evaluation commutes with the fixed coefficient-field embedding at algebraic samples. -/
theorem SolvedRelation.embedding_eval_algebraicSamplePoint
    (R : SolvedRelation) (sample : ℕ)
    (P : MvPolynomial R.Variable R.CoefficientField) :
    R.embedding (MvPolynomial.eval (R.algebraicSamplePoint sample) P) =
      MvPolynomial.eval (R.auxiliaryPoint (sample : ℂ)) (R.complexify P) := by
  have hpoint : R.embedding ∘ R.algebraicSamplePoint sample =
      R.auxiliaryPoint (sample : ℂ) := by
    funext v
    exact R.embedding_algebraicSamplePoint sample v
  simpa [SolvedRelation.complexify, hpoint] using
    (MvPolynomial.map_eval R.embedding (R.algebraicSamplePoint sample) P)

/-- A number-field auxiliary function at a natural sample is its embedded algebraic evaluation. -/
theorem SolvedRelation.auxiliaryFunction_nat_eq_embedding_eval
    (R : SolvedRelation) (sample : ℕ)
    (P : MvPolynomial R.Variable R.CoefficientField) :
    R.auxiliaryFunction P (sample : ℂ) =
      R.embedding (MvPolynomial.eval (R.algebraicSamplePoint sample) P) := by
  simpa [SolvedRelation.auxiliaryFunction] using
    (R.embedding_eval_algebraicSamplePoint sample P).symm

/-- Every full-matrix row is an exact analytic zero of its component-jet polynomial. -/
theorem SolvedRelation.auxiliaryFunction_polynomialComponentJet_eq_zero
    (R : SolvedRelation) (c d : ℤ)
    (hcomp : ∀ dir, IsIntegral ℤ (R.scaledComponentCoeff c dir))
    (hbase : ∀ i, IsIntegral ℤ (R.scaledBase d i))
    {U V S T : ℕ} (eta : R.AuxiliaryColumn U V → 𝓞 R.CoefficientField)
    (hker : Matrix.mulVec (R.polynomialAuxiliaryMatrix c d hcomp hbase U V S T) eta = 0)
    (hd : d ≠ 0) (row : R.AuxiliaryRow S T) :
    R.auxiliaryFunction
      (R.polynomialComponentJetAuxiliaryPolynomial c (fun dir => (row.2 dir : ℕ)) eta)
      ((row.1 : ℕ) : ℂ) = 0 := by
  rw [R.auxiliaryFunction_nat_eq_embedding_eval]
  rw [R.eval_algebraicSample_polynomialComponentJetAuxiliaryPolynomial_eq_zero
    c d hcomp hbase eta hker hd row]
  exact map_zero R.embedding

/-- A component derivation increments the corresponding index of the full jet polynomial. -/
theorem SolvedRelation.componentDerivation_polynomialComponentJetAuxiliaryPolynomial
    (R : SolvedRelation) (c : ℤ) {U V : ℕ} (dir : R.Direction)
    (nu : R.Direction → ℕ) (eta : R.AuxiliaryColumn U V → 𝓞 R.CoefficientField) :
    R.componentDerivation c dir (R.polynomialComponentJetAuxiliaryPolynomial c nu eta) =
      R.polynomialComponentJetAuxiliaryPolynomial c (R.componentBump nu dir) eta := by
  unfold SolvedRelation.polynomialComponentJetAuxiliaryPolynomial
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro col hcol
  rw [Derivation.leibniz, MvPolynomial.derivation_C]
  simp only [smul_eq_mul, mul_zero, add_zero]
  cases dir with
  | none => rw [R.componentDerivation_none_componentJetMonomial]
  | some j => rw [R.componentDerivation_some_componentJetMonomial]

/-- Evaluation of a scalar polynomial coefficient factors through the chosen embedding. -/
theorem SolvedRelation.auxiliaryFunction_C_mul
    (R : SolvedRelation) (x : R.CoefficientField)
    (P : MvPolynomial R.Variable R.CoefficientField) (z : ℂ) :
    R.auxiliaryFunction (MvPolynomial.C x * P) z =
      R.embedding x * R.auxiliaryFunction P z := by
  simp [SolvedRelation.auxiliaryFunction, SolvedRelation.complexify]

/-- Analytic evaluation reflects exactly the integral scale on a component derivation. -/
theorem SolvedRelation.auxiliaryFunction_componentDerivation_scale
    (R : SolvedRelation) (c : ℤ) (dir : R.Direction)
    (P : MvPolynomial R.Variable R.CoefficientField) (z : ℂ) :
    R.auxiliaryFunction (R.componentDerivation c dir P) z =
      (c : ℂ) * R.auxiliaryFunction (R.componentDerivation 1 dir P) z := by
  rw [R.componentDerivation_scale, R.auxiliaryFunction_C_mul]
  simp

/-- Analytic form of the full component-jet auxiliary polynomial. -/
noncomputable def SolvedRelation.polynomialComponentJetAuxiliaryFunction
    (R : SolvedRelation) (c : ℤ) {U V : ℕ}
    (nu : R.Direction → ℕ) (eta : R.AuxiliaryColumn U V → 𝓞 R.CoefficientField)
    (z : ℂ) : ℂ :=
  R.auxiliaryFunction (R.polynomialComponentJetAuxiliaryPolynomial c nu eta) z

/-- Applying a scaled component to a full auxiliary jet shifts its analytic index. -/
theorem SolvedRelation.auxiliaryFunction_componentDerivation_polynomialComponentJet
    (R : SolvedRelation) (c : ℤ) {U V : ℕ} (dir : R.Direction)
    (nu : R.Direction → ℕ) (eta : R.AuxiliaryColumn U V → 𝓞 R.CoefficientField)
    (z : ℂ) :
    R.auxiliaryFunction
      (R.componentDerivation c dir (R.polynomialComponentJetAuxiliaryPolynomial c nu eta)) z =
      R.polynomialComponentJetAuxiliaryFunction c (R.componentBump nu dir) eta z := by
  rw [R.componentDerivation_polynomialComponentJetAuxiliaryPolynomial]
  rfl

/-- Scaled ordinary derivative recurrence for the full component-jet auxiliary functions. -/
theorem SolvedRelation.polynomialComponentJetAuxiliaryFunction_scaled_deriv
    (R : SolvedRelation) (c : ℤ) {U V : ℕ}
    (nu : R.Direction → ℕ) (eta : R.AuxiliaryColumn U V → 𝓞 R.CoefficientField)
    (z : ℂ) :
    (c : ℂ) * deriv (R.polynomialComponentJetAuxiliaryFunction c nu eta) z =
      R.polynomialComponentJetAuxiliaryFunction c (R.componentBump nu none) eta z +
        ∑ i : R.NonPivot, R.lambda i *
          R.polynomialComponentJetAuxiliaryFunction c (R.componentBump nu (some i)) eta z := by
  rw [show R.polynomialComponentJetAuxiliaryFunction c nu eta =
      R.auxiliaryFunction (R.polynomialComponentJetAuxiliaryPolynomial c nu eta) by rfl]
  rw [R.deriv_auxiliaryFunction, mul_add, Finset.mul_sum]
  rw [← R.auxiliaryFunction_componentDerivation_scale c none
    (R.polynomialComponentJetAuxiliaryPolynomial c nu eta) z]
  rw [R.auxiliaryFunction_componentDerivation_polynomialComponentJet]
  apply congrArg (fun q =>
    R.polynomialComponentJetAuxiliaryFunction c (R.componentBump nu none) eta z + q)
  apply Finset.sum_congr rfl
  intro i hi
  calc
    (c : ℂ) * (R.lambda i * R.auxiliaryFunction
        (R.componentDerivation 1 (some i)
          (R.polynomialComponentJetAuxiliaryPolynomial c nu eta)) z) =
        R.lambda i * ((c : ℂ) * R.auxiliaryFunction
          (R.componentDerivation 1 (some i)
            (R.polynomialComponentJetAuxiliaryPolynomial c nu eta)) z) := by ring
    _ = R.lambda i * R.auxiliaryFunction
        (R.componentDerivation c (some i)
          (R.polynomialComponentJetAuxiliaryPolynomial c nu eta)) z := by
        rw [← R.auxiliaryFunction_componentDerivation_scale c (some i)
          (R.polynomialComponentJetAuxiliaryPolynomial c nu eta) z]
    _ = _ := by
        rw [R.auxiliaryFunction_componentDerivation_polynomialComponentJet]

end GaloisForLFunctions.RHTower.BakerGeneralProof
