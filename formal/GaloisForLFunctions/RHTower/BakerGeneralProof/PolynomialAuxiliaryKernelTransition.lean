import GaloisForLFunctions.RHTower.BakerGeneralProof.PolynomialAuxiliaryScalarStep

/-!
# Kernel transitions for the full Baker long extrapolation

A rectangular family of exact component-jet zeros is exactly a kernel vector of the corresponding
auxiliary matrix, so the stage state of the long extrapolation can be carried as a single kernel
statement.  Shrinking the component box or the sample range preserves it, and one scalar
extrapolation step trades half of the component box for a longer sample range.
-/

open scoped Classical
open BigOperators NumberField

namespace GaloisForLFunctions.RHTower.BakerGeneralProof

/-- A rectangular family of exact component-jet zeros is a kernel vector of the corresponding
auxiliary matrix. -/
theorem SolvedRelation.polynomialAuxiliaryMatrix_mulVec_eq_zero_of_component_box_zero
    (R : SolvedRelation) (c d : ℤ)
    (hcomp : ∀ dir, IsIntegral ℤ (R.scaledComponentCoeff c dir))
    (hbase : ∀ i, IsIntegral ℤ (R.scaledBase d i))
    {U V S T : ℕ} (eta : R.AuxiliaryColumn U V → 𝓞 R.CoefficientField)
    (hzero : ∀ (sample : Fin S) (nu : R.Direction → Fin T),
      R.polynomialComponentJetAuxiliaryFunction c (fun dir => (nu dir : ℕ)) eta
        ((sample : ℕ) : ℂ) = 0) :
    Matrix.mulVec (R.polynomialAuxiliaryMatrix c d hcomp hbase U V S T) eta = 0 := by
  funext row
  apply RingOfIntegers.coe_injective
  have heval : MvPolynomial.eval (R.algebraicSamplePoint (row.1 : ℕ))
      (R.polynomialComponentJetAuxiliaryPolynomial c (fun dir => (row.2 dir : ℕ)) eta) = 0 := by
    apply R.embedding.injective
    rw [map_zero, ← R.auxiliaryFunction_nat_eq_embedding_eval]
    exact hzero row.1 row.2
  have hinner : ∑ col : R.AuxiliaryColumn U V,
      (R.additiveComponentJetCoefficient c (fun dir => (row.2 dir : ℕ))
        (col.1 : ℕ) (row.1 : ℕ) col.2 * R.baseSample (row.1 : ℕ) col.2) *
        (algebraMap (𝓞 R.CoefficientField) R.CoefficientField) (eta col) = 0 := by
    rw [R.eval_algebraicSample_polynomialComponentJetAuxiliaryPolynomial] at heval
    calc
      _ = ∑ col : R.AuxiliaryColumn U V,
          (algebraMap (𝓞 R.CoefficientField) R.CoefficientField) (eta col) *
            (R.additiveComponentJetCoefficient c (fun dir => (row.2 dir : ℕ))
              (col.1 : ℕ) (row.1 : ℕ) col.2 * R.baseSample (row.1 : ℕ) col.2) := by
        exact Finset.sum_congr rfl fun col _ => by ring
      _ = 0 := heval
  change (algebraMap (𝓞 R.CoefficientField) R.CoefficientField)
      ((Matrix.mulVec (R.polynomialAuxiliaryMatrix c d hcomp hbase U V S T) eta) row) =
    (algebraMap (𝓞 R.CoefficientField) R.CoefficientField) 0
  rw [map_zero, Matrix.mulVec, dotProduct, map_sum]
  simp_rw [map_mul]
  change (∑ col, R.polynomialAuxiliaryEntry c d row col *
    (algebraMap (𝓞 R.CoefficientField) R.CoefficientField) (eta col)) = 0
  simp_rw [R.polynomialAuxiliaryEntry_eq_commonScale_mul]
  calc
    (∑ col : R.AuxiliaryColumn U V,
        R.integerScalar d ^ R.clearingBound S V *
          (R.additiveComponentJetCoefficient c (fun dir => (row.2 dir : ℕ))
            (col.1 : ℕ) (row.1 : ℕ) col.2 * R.baseSample (row.1 : ℕ) col.2) *
          (algebraMap (𝓞 R.CoefficientField) R.CoefficientField) (eta col)) =
        R.integerScalar d ^ R.clearingBound S V *
          ∑ col : R.AuxiliaryColumn U V,
            (R.additiveComponentJetCoefficient c (fun dir => (row.2 dir : ℕ))
              (col.1 : ℕ) (row.1 : ℕ) col.2 * R.baseSample (row.1 : ℕ) col.2) *
              (algebraMap (𝓞 R.CoefficientField) R.CoefficientField) (eta col) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun col _ => by ring
    _ = 0 := by rw [hinner, mul_zero]


/-- Restricting either the sample range or the component box preserves the auxiliary kernel. -/
theorem SolvedRelation.polynomialAuxiliaryMatrix_kernel_mono
    (R : SolvedRelation) (c d : ℤ)
    (hcomp : ∀ dir, IsIntegral ℤ (R.scaledComponentCoeff c dir))
    (hbase : ∀ i, IsIntegral ℤ (R.scaledBase d i))
    {U V S T : ℕ} (eta : R.AuxiliaryColumn U V → 𝓞 R.CoefficientField)
    (hker : Matrix.mulVec (R.polynomialAuxiliaryMatrix c d hcomp hbase U V S T) eta = 0)
    (hd : d ≠ 0) {S' T' : ℕ} (hS : S' ≤ S) (hT : T' ≤ T) :
    Matrix.mulVec (R.polynomialAuxiliaryMatrix c d hcomp hbase U V S' T') eta = 0 := by
  apply R.polynomialAuxiliaryMatrix_mulVec_eq_zero_of_component_box_zero
  intro sample nu
  exact R.polynomialComponentJetAuxiliaryFunction_eq_zero_of_box c d hcomp hbase eta hker hd
    ⟨(sample : ℕ), lt_of_lt_of_le sample.isLt hS⟩ (fun dir => (nu dir : ℕ))
      (fun dir => lt_of_lt_of_le (nu dir).isLt hT)

/-- One long-extrapolation transition: exact zeros of every jet in the new component box
reassemble into a kernel vector for the enlarged sample range. -/
theorem SolvedRelation.polynomialAuxiliaryMatrix_kernel_extrapolate
    (R : SolvedRelation) (c d : ℤ) (hc : c ≠ 0)
    (hcomp : ∀ dir, IsIntegral ℤ (R.scaledComponentCoeff c dir))
    (hbase : ∀ i, IsIntegral ℤ (R.scaledBase d i))
    {U V S T : ℕ} (hU : 1 ≤ U)
    (eta : R.AuxiliaryColumn U V → 𝓞 R.CoefficientField)
    (hker : Matrix.mulVec (R.polynomialAuxiliaryMatrix c d hcomp hbase U V S T) eta = 0)
    (hd : d ≠ 0) {Heta : ℝ} (hHeta : 0 ≤ Heta)
    (hEta : ∀ col, house ((algebraMap (𝓞 R.CoefficientField) R.CoefficientField) (eta col)) ≤
      Heta)
    (q : ℕ) (hqT : 2 * q ≤ T)
    {radius : ℝ} (hradius1 : 1 ≤ radius) (hradiusS : (S : ℝ) < radius)
    (S' : ℕ) (hsample : ∀ sample : Fin S', ((sample : ℕ) : ℝ) ≤ radius)
    (hsmall : ∀ (sample : Fin S') (nu : R.Direction → Fin q),
      (|(d : ℝ)| ^ ((sample : ℕ) * (R.n * V)) *
        ((((sample : ℕ) + S : ℕ) : ℝ) ^ (q * S) *
          (R.jetScalarBound c U V (fun dir => (nu dir : ℕ)) Heta radius /
            (radius - S) ^ (q * S)))) *
        R.jetHouseScalarBound c d U V (fun dir => (nu dir : ℕ)) Heta (sample : ℕ) ^
          (Module.finrank ℚ R.CoefficientField - 1) < 1) :
    Matrix.mulVec (R.polynomialAuxiliaryMatrix c d hcomp hbase U V S' q) eta = 0 := by
  apply R.polynomialAuxiliaryMatrix_mulVec_eq_zero_of_component_box_zero
  intro sample nu
  have hnuq : ∀ dir, (nu dir : ℕ) + q ≤ T := by
    intro dir
    have h1 : (nu dir : ℕ) + q < q + q := Nat.add_lt_add_right (nu dir).isLt q
    omega
  exact R.polynomialComponentJetAuxiliaryFunction_eq_zero_one_step_scalar
    c d hc hcomp hbase hU eta hker hd (fun dir => (nu dir : ℕ)) q hnuq hHeta hEta
    hradius1 hradiusS (sample : ℕ) (hsample sample) (hsmall sample nu)

end GaloisForLFunctions.RHTower.BakerGeneralProof
