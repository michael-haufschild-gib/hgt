import GaloisForLFunctions.RHTower.BakerGeneralProof.PolynomialAuxiliaryExtrapolation

/-!
# Finite conjugate bounds for full Baker component jets

This module retains the complete finite full-jet expression while bounding its conjugates by
houses of the four algebraic factors: common base scale, component-jet coefficient, Siegel
coefficient, and scaled exponential sample.  No supremum or asymptotic quantity is introduced;
these are the finite arithmetic inputs for the later parameter inequalities.
-/

open scoped Classical
open BigOperators NumberField

namespace GaloisForLFunctions.RHTower.BakerGeneralProof

/-- Exact finite sum of the houses of the terms in a cleared full component-jet value. -/
noncomputable def SolvedRelation.polynomialComponentJetHouseBound
    (R : SolvedRelation) (c d : ℤ) {U V : ℕ}
    (nu : R.Direction → ℕ) (eta : R.AuxiliaryColumn U V → 𝓞 R.CoefficientField)
    (sample : ℕ) : ℝ :=
  ∑ col, house
    (R.integerScalar d ^ R.polynomialComponentJetClearingExponent sample col.2 *
      R.additiveComponentJetCoefficient c nu (col.1 : ℕ) sample col.2 *
        (algebraMap (𝓞 R.CoefficientField) R.CoefficientField) (eta col) *
          R.scaledBaseSample d ⟨sample, Nat.lt_add_one sample⟩ col.2)

theorem SolvedRelation.polynomialComponentJetHouseBound_nonneg
    (R : SolvedRelation) (c d : ℤ) {U V : ℕ}
    (nu : R.Direction → ℕ) (eta : R.AuxiliaryColumn U V → 𝓞 R.CoefficientField)
    (sample : ℕ) :
    0 ≤ R.polynomialComponentJetHouseBound c d nu eta sample := by
  unfold SolvedRelation.polynomialComponentJetHouseBound
  exact Finset.sum_nonneg fun _ _ => house_nonneg _

/-- The house of the cleared full-jet integer is bounded by its finite termwise house sum. -/
theorem SolvedRelation.polynomialComponentJetInteger_house_le
    (R : SolvedRelation) (c d : ℤ)
    (hcomp : ∀ dir, IsIntegral ℤ (R.scaledComponentCoeff c dir))
    (hbase : ∀ i, IsIntegral ℤ (R.scaledBase d i))
    {U V : ℕ} (nu : R.Direction → ℕ)
    (eta : R.AuxiliaryColumn U V → 𝓞 R.CoefficientField) (sample : ℕ) :
    house ((algebraMap (𝓞 R.CoefficientField) R.CoefficientField)
      (R.polynomialComponentJetInteger c d hcomp hbase nu eta sample)) ≤
      R.polynomialComponentJetHouseBound c d nu eta sample := by
  let s : Fin (sample + 1) := ⟨sample, Nat.lt_add_one sample⟩
  change house (∑ col,
    R.integerScalar d ^ R.polynomialComponentJetClearingExponent sample col.2 *
      R.additiveComponentJetCoefficient c nu (col.1 : ℕ) sample col.2 *
        (algebraMap (𝓞 R.CoefficientField) R.CoefficientField) (eta col) *
          R.scaledBaseSample d s col.2) ≤ _
  simpa [SolvedRelation.polynomialComponentJetHouseBound, s] using
    house_sum_le_sum_house (Finset.univ : Finset (R.AuxiliaryColumn U V))
      (fun col => R.integerScalar d ^ R.polynomialComponentJetClearingExponent sample col.2 *
        R.additiveComponentJetCoefficient c nu (col.1 : ℕ) sample col.2 *
          (algebraMap (𝓞 R.CoefficientField) R.CoefficientField) (eta col) *
            R.scaledBaseSample d s col.2)

/-- A uniform house bound on the Siegel vector propagates termwise to the full-jet value. -/
theorem SolvedRelation.polynomialComponentJetHouseBound_le_of_coefficient_house_le
    (R : SolvedRelation) (c d : ℤ) {U V : ℕ}
    (nu : R.Direction → ℕ) (eta : R.AuxiliaryColumn U V → 𝓞 R.CoefficientField)
    (sample : ℕ) (Heta : ℝ) (hEta : ∀ col,
      house ((algebraMap (𝓞 R.CoefficientField) R.CoefficientField) (eta col)) ≤ Heta) :
    R.polynomialComponentJetHouseBound c d nu eta sample ≤
      ∑ col : R.AuxiliaryColumn U V,
        house (R.integerScalar d) ^ R.polynomialComponentJetClearingExponent sample col.2 *
          house (R.additiveComponentJetCoefficient c nu (col.1 : ℕ) sample col.2) *
            Heta * house (R.scaledBaseSample d
              ⟨sample, Nat.lt_add_one sample⟩ col.2) := by
  unfold SolvedRelation.polynomialComponentJetHouseBound
  apply Finset.sum_le_sum
  intro col hcol
  calc
    house (R.integerScalar d ^ R.polynomialComponentJetClearingExponent sample col.2 *
        R.additiveComponentJetCoefficient c nu (col.1 : ℕ) sample col.2 *
          (algebraMap (𝓞 R.CoefficientField) R.CoefficientField) (eta col) *
            R.scaledBaseSample d ⟨sample, Nat.lt_add_one sample⟩ col.2) ≤
        house (R.integerScalar d ^ R.polynomialComponentJetClearingExponent sample col.2) *
          house (R.additiveComponentJetCoefficient c nu (col.1 : ℕ) sample col.2) *
            house ((algebraMap (𝓞 R.CoefficientField) R.CoefficientField) (eta col)) *
              house (R.scaledBaseSample d ⟨sample, Nat.lt_add_one sample⟩ col.2) := by
      calc
        house (R.integerScalar d ^ R.polynomialComponentJetClearingExponent sample col.2 *
            R.additiveComponentJetCoefficient c nu (col.1 : ℕ) sample col.2 *
              (algebraMap (𝓞 R.CoefficientField) R.CoefficientField) (eta col) *
                R.scaledBaseSample d ⟨sample, Nat.lt_add_one sample⟩ col.2) ≤
            house (R.integerScalar d ^ R.polynomialComponentJetClearingExponent sample col.2 *
              R.additiveComponentJetCoefficient c nu (col.1 : ℕ) sample col.2 *
                (algebraMap (𝓞 R.CoefficientField) R.CoefficientField) (eta col)) *
              house (R.scaledBaseSample d ⟨sample, Nat.lt_add_one sample⟩ col.2) :=
          house_mul_le _ _
        _ ≤ (house (R.integerScalar d ^ R.polynomialComponentJetClearingExponent sample col.2) *
              house (R.additiveComponentJetCoefficient c nu (col.1 : ℕ) sample col.2) *
                house ((algebraMap (𝓞 R.CoefficientField) R.CoefficientField) (eta col))) *
              house (R.scaledBaseSample d ⟨sample, Nat.lt_add_one sample⟩ col.2) := by
          apply mul_le_mul_of_nonneg_right _ (house_nonneg _)
          calc
            house (R.integerScalar d ^ R.polynomialComponentJetClearingExponent sample col.2 *
              R.additiveComponentJetCoefficient c nu (col.1 : ℕ) sample col.2 *
                (algebraMap (𝓞 R.CoefficientField) R.CoefficientField) (eta col)) ≤
                house (R.integerScalar d ^ R.polynomialComponentJetClearingExponent sample col.2 *
                  R.additiveComponentJetCoefficient c nu (col.1 : ℕ) sample col.2) *
                    house ((algebraMap (𝓞 R.CoefficientField) R.CoefficientField) (eta col)) :=
              house_mul_le _ _
            _ ≤ (house (R.integerScalar d ^ R.polynomialComponentJetClearingExponent sample col.2) *
                house (R.additiveComponentJetCoefficient c nu (col.1 : ℕ) sample col.2)) *
                house ((algebraMap (𝓞 R.CoefficientField) R.CoefficientField) (eta col)) := by
              exact mul_le_mul_of_nonneg_right (house_mul_le _ _) (house_nonneg _)
        _ = _ := by ring
    _ ≤ house (R.integerScalar d) ^ R.polynomialComponentJetClearingExponent sample col.2 *
          house (R.additiveComponentJetCoefficient c nu (col.1 : ℕ) sample col.2) *
            Heta * house (R.scaledBaseSample d
              ⟨sample, Nat.lt_add_one sample⟩ col.2) := by
      apply mul_le_mul_of_nonneg_right _ (house_nonneg _)
      calc
        house (R.integerScalar d ^ R.polynomialComponentJetClearingExponent sample col.2) *
            house (R.additiveComponentJetCoefficient c nu (col.1 : ℕ) sample col.2) *
              house ((algebraMap (𝓞 R.CoefficientField) R.CoefficientField) (eta col) ) ≤
            (house (R.integerScalar d) ^ R.polynomialComponentJetClearingExponent sample col.2 *
              house (R.additiveComponentJetCoefficient c nu (col.1 : ℕ) sample col.2)) *
                house ((algebraMap (𝓞 R.CoefficientField) R.CoefficientField) (eta col)) := by
          apply mul_le_mul_of_nonneg_right _ (house_nonneg _)
          exact mul_le_mul_of_nonneg_right (house_pow_le _ _) (house_nonneg _)
        _ ≤ (house (R.integerScalar d) ^ R.polynomialComponentJetClearingExponent sample col.2 *
              house (R.additiveComponentJetCoefficient c nu (col.1 : ℕ) sample col.2)) * Heta := by
          apply mul_le_mul_of_nonneg_left (hEta col)
          exact mul_nonneg (pow_nonneg (house_nonneg _) _) (house_nonneg _)
        _ = _ := by ring

end GaloisForLFunctions.RHTower.BakerGeneralProof
