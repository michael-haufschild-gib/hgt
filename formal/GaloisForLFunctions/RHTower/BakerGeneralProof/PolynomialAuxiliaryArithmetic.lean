import GaloisForLFunctions.RHTower.BakerGeneralProof.PolynomialAuxiliaryAnalytic
import GaloisForLFunctions.RHTower.BakerProof.AuxiliaryArithmetic

/-!
# Arithmetic full-jet values for the Baker auxiliary polynomial

Every component jet at a nonnegative integer sample is algebraic.  The exponential bases need
not themselves be algebraic integers, so this module clears their common denominator by the
exact exponent needed for the sample and exponential column.  The resulting finite sum is an
algebraic integer, and its distinguished embedding is exactly the corresponding scaled analytic
component jet.  This connects analytic extrapolation with the unconditional algebraic-integer
norm criterion.
-/

open scoped Classical
open BigOperators NumberField

namespace GaloisForLFunctions.RHTower.BakerGeneralProof

/-- Remaining common-base scale in one full component-jet value at `sample`. -/
noncomputable def SolvedRelation.polynomialComponentJetClearingExponent
    (R : SolvedRelation) {V : ℕ} (sample : ℕ) (m : R.ExponentialColumn V) : ℕ :=
  sample * (R.n * V) - sample * R.exponentialDegree m

/-- The algebraic-integer representative of a full jet value at a natural sample. -/
noncomputable def SolvedRelation.polynomialComponentJetInteger
    (R : SolvedRelation) (c d : ℤ)
    (hcomp : ∀ dir, IsIntegral ℤ (R.scaledComponentCoeff c dir))
    (hbase : ∀ i, IsIntegral ℤ (R.scaledBase d i))
    {U V : ℕ} (nu : R.Direction → ℕ)
    (eta : R.AuxiliaryColumn U V → 𝓞 R.CoefficientField) (sample : ℕ) :
    𝓞 R.CoefficientField := by
  let s : Fin (sample + 1) := ⟨sample, Nat.lt_add_one sample⟩
  refine ⟨∑ col,
    R.integerScalar d ^ R.polynomialComponentJetClearingExponent sample col.2 *
      R.additiveComponentJetCoefficient c nu (col.1 : ℕ) sample col.2 *
        (algebraMap (𝓞 R.CoefficientField) R.CoefficientField) (eta col) *
          R.scaledBaseSample d s col.2, ?_⟩
  apply IsIntegral.sum
  intro col hcol
  apply IsIntegral.mul
  · apply IsIntegral.mul
    · apply IsIntegral.mul
      · exact (R.integerScalar_isIntegral d).pow
          (R.polynomialComponentJetClearingExponent sample col.2)
      · exact R.additiveComponentJetCoefficient_isIntegral c hcomp nu
          (col.1 : ℕ) sample col.2
    · exact RingOfIntegers.isIntegral_coe (eta col)
  · exact R.scaledBaseSample_isIntegral d hbase s col.2

/-- The representative is the common scaled algebraic evaluation of the jet polynomial. -/
theorem SolvedRelation.polynomialComponentJetInteger_coe
    (R : SolvedRelation) (c d : ℤ)
    (hcomp : ∀ dir, IsIntegral ℤ (R.scaledComponentCoeff c dir))
    (hbase : ∀ i, IsIntegral ℤ (R.scaledBase d i))
    {U V : ℕ} (nu : R.Direction → ℕ)
    (eta : R.AuxiliaryColumn U V → 𝓞 R.CoefficientField) (sample : ℕ) :
    (algebraMap (𝓞 R.CoefficientField) R.CoefficientField)
      (R.polynomialComponentJetInteger c d hcomp hbase nu eta sample) =
      R.integerScalar d ^ (sample * (R.n * V)) *
        MvPolynomial.eval (R.algebraicSamplePoint sample)
          (R.polynomialComponentJetAuxiliaryPolynomial c nu eta) := by
  let s : Fin (sample + 1) := ⟨sample, Nat.lt_add_one sample⟩
  unfold SolvedRelation.polynomialComponentJetInteger
  change ∑ col,
      R.integerScalar d ^ R.polynomialComponentJetClearingExponent sample col.2 *
        R.additiveComponentJetCoefficient c nu (col.1 : ℕ) sample col.2 *
          (algebraMap (𝓞 R.CoefficientField) R.CoefficientField) (eta col) *
            R.scaledBaseSample d s col.2 = _
  rw [R.eval_algebraicSample_polynomialComponentJetAuxiliaryPolynomial,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro col hcol
  rw [R.scaledBaseSample_eq_scale_pow_mul_baseSample d s col.2]
  have hle : sample * R.exponentialDegree col.2 ≤ sample * (R.n * V) :=
    Nat.mul_le_mul_left sample (R.exponentialDegree_le col.2)
  have hsum : R.polynomialComponentJetClearingExponent sample col.2 +
      sample * R.exponentialDegree col.2 = sample * (R.n * V) := by
    unfold SolvedRelation.polynomialComponentJetClearingExponent
    exact Nat.sub_add_cancel hle
  calc
    R.integerScalar d ^ R.polynomialComponentJetClearingExponent sample col.2 *
        R.additiveComponentJetCoefficient c nu (col.1 : ℕ) sample col.2 *
        (algebraMap (𝓞 R.CoefficientField) R.CoefficientField) (eta col) *
        (R.integerScalar d ^ (sample * R.exponentialDegree col.2) *
          R.baseSample sample col.2) =
        (R.integerScalar d ^ R.polynomialComponentJetClearingExponent sample col.2 *
          R.integerScalar d ^ (sample * R.exponentialDegree col.2)) *
          ((algebraMap (𝓞 R.CoefficientField) R.CoefficientField) (eta col) *
            (R.additiveComponentJetCoefficient c nu (col.1 : ℕ) sample col.2 *
              R.baseSample sample col.2)) := by ring
    _ =
        R.integerScalar d ^
          (R.polynomialComponentJetClearingExponent sample col.2 +
            sample * R.exponentialDegree col.2) *
          ((algebraMap (𝓞 R.CoefficientField) R.CoefficientField) (eta col) *
            (R.additiveComponentJetCoefficient c nu (col.1 : ℕ) sample col.2 *
              R.baseSample sample col.2)) := by rw [← pow_add]
    _ = _ := by rw [hsum]

/-- At a natural sample, the distinguished embedding of the integral representative is the
exact scaled analytic full jet. -/
theorem SolvedRelation.integralCoeffEmbedding_polynomialComponentJetInteger
    (R : SolvedRelation) (c d : ℤ)
    (hcomp : ∀ dir, IsIntegral ℤ (R.scaledComponentCoeff c dir))
    (hbase : ∀ i, IsIntegral ℤ (R.scaledBase d i))
    {U V : ℕ} (nu : R.Direction → ℕ)
    (eta : R.AuxiliaryColumn U V → 𝓞 R.CoefficientField) (sample : ℕ) :
    R.embedding ((algebraMap (𝓞 R.CoefficientField) R.CoefficientField)
      (R.polynomialComponentJetInteger c d hcomp hbase nu eta sample)) =
      (d : ℂ) ^ (sample * (R.n * V)) *
        R.polynomialComponentJetAuxiliaryFunction c nu eta (sample : ℂ) := by
  rw [R.polynomialComponentJetInteger_coe, map_mul, map_pow,
    R.embedding_integerScalar]
  exact congrArg ((d : ℂ) ^ (sample * (R.n * V)) * ·)
    (R.auxiliaryFunction_nat_eq_embedding_eval sample
      (R.polynomialComponentJetAuxiliaryPolynomial c nu eta)).symm

/-- Norm discreteness for a full jet, after its exact base-denominator normalization. -/
theorem SolvedRelation.polynomialComponentJetAuxiliaryFunction_eq_zero_of_distinguished_mul_house_pow_lt_one
    (R : SolvedRelation) (c d : ℤ)
    (hcomp : ∀ dir, IsIntegral ℤ (R.scaledComponentCoeff c dir))
    (hbase : ∀ i, IsIntegral ℤ (R.scaledBase d i))
    {U V : ℕ} (nu : R.Direction → ℕ)
    (eta : R.AuxiliaryColumn U V → 𝓞 R.CoefficientField) (sample : ℕ) (hd : d ≠ 0)
    (hsmall :
      ‖(d : ℂ) ^ (sample * (R.n * V)) *
        R.polynomialComponentJetAuxiliaryFunction c nu eta (sample : ℂ)‖ *
        house ((algebraMap (𝓞 R.CoefficientField) R.CoefficientField)
          (R.polynomialComponentJetInteger c d hcomp hbase nu eta sample)) ^
          (Module.finrank ℚ R.CoefficientField - 1) < 1) :
    R.polynomialComponentJetAuxiliaryFunction c nu eta (sample : ℂ) = 0 := by
  let x := R.polynomialComponentJetInteger c d hcomp hbase nu eta sample
  have hx : x = 0 := by
    apply BakerProof.algebraicInteger_eq_zero_of_distinguished_mul_house_pow_lt_one R.embedding x
    rw [show R.embedding ((algebraMap (𝓞 R.CoefficientField) R.CoefficientField) x) =
      (d : ℂ) ^ (sample * (R.n * V)) *
        R.polynomialComponentJetAuxiliaryFunction c nu eta (sample : ℂ) by
      exact R.integralCoeffEmbedding_polynomialComponentJetInteger
        c d hcomp hbase nu eta sample]
    exact hsmall
  have hprod : (d : ℂ) ^ (sample * (R.n * V)) *
      R.polynomialComponentJetAuxiliaryFunction c nu eta (sample : ℂ) = 0 := by
    rw [← R.integralCoeffEmbedding_polynomialComponentJetInteger
      c d hcomp hbase nu eta sample]
    change R.embedding ((algebraMap (𝓞 R.CoefficientField) R.CoefficientField) x) = 0
    simp [hx]
  exact (mul_eq_zero.mp hprod).resolve_left
    (pow_ne_zero _ (Int.cast_ne_zero.mpr hd))

end GaloisForLFunctions.RHTower.BakerGeneralProof
