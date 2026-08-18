import GaloisForLFunctions.RHTower.BakerGeneralProof.PolynomialAuxiliaryKernelTransition

/-!
# Matrix height and Siegel budget for the full Baker auxiliary system

Every entry of the full auxiliary matrix is a product of a base-denominator power, a component-jet
coefficient and an exponential sample, so its house is bounded by a closed product of powers of the
construction parameters.  Summing over the finite index sets bounds the matrix height, and the
exact two-to-one ratio between columns and rows turns the Siegel exponent into one, giving a linear
coefficient budget for the kernel vector.
-/

open scoped Classical
open BigOperators NumberField

namespace GaloisForLFunctions.RHTower.BakerGeneralProof

/-- Closed scalar majorant for a single entry of the full auxiliary matrix. -/
noncomputable def SolvedRelation.auxiliaryEntryScalarBound
    (R : SolvedRelation) (c d : ℤ) (U V S T : ℕ) : ℝ :=
  (1 + |(d : ℝ)|) ^ (S * (R.n * V)) *
    ((T : ℝ) * R.jetGrowthBase c U V ^ (R.n * T) * (1 + (S : ℝ)) ^ U) *
      R.baseHouseBound d ^ (R.n * V * S)

theorem SolvedRelation.auxiliaryEntryScalarBound_nonneg
    (R : SolvedRelation) (c d : ℤ) (U V S T : ℕ) :
    0 ≤ R.auxiliaryEntryScalarBound c d U V S T := by
  unfold SolvedRelation.auxiliaryEntryScalarBound
  have hG0 : (0 : ℝ) ≤ R.jetGrowthBase c U V :=
    le_trans zero_le_one (R.one_le_jetGrowthBase c U V)
  have hB0 : (0 : ℝ) ≤ R.baseHouseBound d :=
    le_trans zero_le_one (R.one_le_baseHouseBound d)
  have hd0 : (0 : ℝ) ≤ 1 + |(d : ℝ)| := by positivity
  have hs0 : (0 : ℝ) ≤ 1 + (S : ℝ) := by positivity
  have h1 : (0 : ℝ) ≤ (T : ℝ) * R.jetGrowthBase c U V ^ (R.n * T) * (1 + (S : ℝ)) ^ U :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hG0 _)) (pow_nonneg hs0 _)
  exact mul_nonneg (mul_nonneg (pow_nonneg hd0 _) h1) (pow_nonneg hB0 _)

theorem SolvedRelation.house_polynomialAuxiliaryEntry_le
    (R : SolvedRelation) (c d : ℤ) {U V S T : ℕ} (hU : 1 ≤ U) (hT : 1 ≤ T)
    (row : R.AuxiliaryRow S T) (col : R.AuxiliaryColumn U V) :
    house (R.polynomialAuxiliaryEntry c d row col) ≤
      R.auxiliaryEntryScalarBound c d U V S T := by
  have hG1 : (1 : ℝ) ≤ R.jetGrowthBase c U V := R.one_le_jetGrowthBase c U V
  have hG0 : (0 : ℝ) ≤ R.jetGrowthBase c U V := le_trans zero_le_one hG1
  have hB1 : (1 : ℝ) ≤ R.baseHouseBound d := R.one_le_baseHouseBound d
  have hd1 : (1 : ℝ) ≤ 1 + |(d : ℝ)| := by
    have := abs_nonneg ((d : ℝ)); linarith
  have hs1 : (1 : ℝ) ≤ 1 + (S : ℝ) := by
    have := Nat.cast_nonneg (α := ℝ) S; linarith
  have h1 : house (R.integerScalar d ^ R.clearingExponent row col.2) ≤
      (1 + |(d : ℝ)|) ^ (S * (R.n * V)) := by
    refine le_trans (house_pow_le _ _) ?_
    rw [R.house_integerScalar]
    have hdle : |(d : ℝ)| ≤ 1 + |(d : ℝ)| := by linarith
    refine le_trans (pow_le_pow_left₀ (abs_nonneg _) hdle _) ?_
    refine pow_le_pow_right₀ hd1 ?_
    unfold SolvedRelation.clearingExponent SolvedRelation.clearingBound
    exact Nat.sub_le _ _
  have h2 : house (R.additiveComponentJetCoefficient c (fun dir => (row.2 dir : ℕ))
      (col.1 : ℕ) (row.1 : ℕ) col.2) ≤
      (T : ℝ) * R.jetGrowthBase c U V ^ (R.n * T) * (1 + (S : ℝ)) ^ U := by
    refine le_trans (R.house_additiveComponentJetCoefficient_le c hU
      (fun dir => (row.2 dir : ℕ)) (col.1 : ℕ) (row.1 : ℕ) col.1.isLt.le col.2) ?_
    have hnu : ((((row.2 none : ℕ)) + 1 : ℕ) : ℝ) ≤ (T : ℝ) := by
      have : ((row.2 none : ℕ)) + 1 ≤ T := (row.2 none).isLt
      exact_mod_cast this
    have hsum : (∑ dir, ((row.2 dir : ℕ))) ≤ R.n * T := by
      calc
        (∑ dir : R.Direction, ((row.2 dir : ℕ))) ≤ ∑ _dir : R.Direction, T :=
          Finset.sum_le_sum fun dir _ => (row.2 dir).isLt.le
        _ = R.n * T := by simp [Finset.sum_const, R.card_direction, mul_comm]
    have hGpow : R.jetGrowthBase c U V ^ (∑ dir, ((row.2 dir : ℕ))) ≤
        R.jetGrowthBase c U V ^ (R.n * T) := pow_le_pow_right₀ hG1 hsum
    have hSpow : (1 + ((row.1 : ℕ) : ℝ)) ^ U ≤ (1 + (S : ℝ)) ^ U := by
      refine pow_le_pow_left₀ (by positivity) ?_ _
      have : ((row.1 : ℕ) : ℝ) ≤ (S : ℝ) := by exact_mod_cast row.1.isLt.le
      linarith
    refine mul_le_mul (mul_le_mul hnu hGpow (pow_nonneg hG0 _) (Nat.cast_nonneg _)) hSpow
      (by positivity) (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hG0 _))
  have h3 : house (R.scaledBaseSample d row.1 col.2) ≤
      R.baseHouseBound d ^ (R.n * V * S) := by
    refine le_trans (R.house_scaledBaseSample_le d row.1 col.2) ?_
    exact pow_le_pow_right₀ hB1 (Nat.mul_le_mul_left _ row.1.isLt.le)
  unfold SolvedRelation.polynomialAuxiliaryEntry SolvedRelation.auxiliaryEntryScalarBound
  refine le_trans (house_mul_le _ _) ?_
  refine mul_le_mul ?_ h3 (house_nonneg _) (by positivity)
  refine le_trans (house_mul_le _ _) ?_
  exact mul_le_mul h1 h2 (house_nonneg _) (by positivity)

theorem SolvedRelation.polynomialAuxiliaryHeight_le
    (R : SolvedRelation) (c d : ℤ)
    (hcomp : ∀ dir, IsIntegral ℤ (R.scaledComponentCoeff c dir))
    (hbase : ∀ i, IsIntegral ℤ (R.scaledBase d i))
    {U V S T : ℕ} (hU : 1 ≤ U) (hT : 1 ≤ T) :
    R.polynomialAuxiliaryHeight c d hcomp hbase U V S T ≤
      (((S * T ^ R.n) * (U * V ^ R.n) : ℕ) : ℝ) *
        R.auxiliaryEntryScalarBound c d U V S T := by
  unfold SolvedRelation.polynomialAuxiliaryHeight
  have hbound : ∀ row : R.AuxiliaryRow S T, ∀ col : R.AuxiliaryColumn U V,
      house ((algebraMap (𝓞 R.CoefficientField) R.CoefficientField)
        (R.polynomialAuxiliaryMatrix c d hcomp hbase U V S T row col)) ≤
        R.auxiliaryEntryScalarBound c d U V S T := by
    intro row col
    exact R.house_polynomialAuxiliaryEntry_le c d hU hT row col
  calc
    (∑ row : R.AuxiliaryRow S T, ∑ col : R.AuxiliaryColumn U V,
        house ((algebraMap (𝓞 R.CoefficientField) R.CoefficientField)
          (R.polynomialAuxiliaryMatrix c d hcomp hbase U V S T row col))) ≤
        ∑ _row : R.AuxiliaryRow S T, ∑ _col : R.AuxiliaryColumn U V,
          R.auxiliaryEntryScalarBound c d U V S T := by
      refine Finset.sum_le_sum fun row _ => Finset.sum_le_sum fun col _ => hbound row col
    _ = (((S * T ^ R.n) * (U * V ^ R.n) : ℕ) : ℝ) *
        R.auxiliaryEntryScalarBound c d U V S T := by
      rw [Finset.sum_const, Finset.sum_const]
      simp only [nsmul_eq_mul, Finset.card_univ, R.card_auxiliaryRow, R.card_auxiliaryColumn]
      push_cast
      ring


theorem one_le_siegelConstant (K : Type*) [Field K] [NumberField K]
    [DecidableEq (K →+* ℂ)] : 1 ≤ GelfondSchneiderSiegel.c₁ K := by
  have hbasis : 1 ≤ GelfondSchneiderSiegel.supOfBasis K :=
    GelfondSchneiderSiegel.one_le_supOfBasis K
  have hmax : (1 : ℝ) ≤ max 1 (GelfondSchneiderSiegel.c K) := le_max_left _ _
  have hc₂ : (1 : ℝ) ≤ GelfondSchneiderSiegel.c₂ K := by
    unfold GelfondSchneiderSiegel.c₂
    nlinarith
  have hrank : (1 : ℝ) ≤ (Module.finrank ℚ K : ℝ) := by
    have : 0 < Module.finrank ℚ K := Module.finrank_pos
    exact_mod_cast this
  unfold GelfondSchneiderSiegel.c₁
  nlinarith

/-- Siegel coefficient budget at the exact two-to-one column count. -/
noncomputable def SolvedRelation.coefficientBudget
    (R : SolvedRelation) (c d : ℤ)
    (hcomp : ∀ dir, IsIntegral ℤ (R.scaledComponentCoeff c dir))
    (hbase : ∀ i, IsIntegral ℤ (R.scaledBase d i))
    (U V S T : ℕ) : ℝ :=
  GelfondSchneiderSiegel.c₁ R.CoefficientField *
    (GelfondSchneiderSiegel.c₁ R.CoefficientField * ((U * V ^ R.n : ℕ) : ℝ) *
      R.polynomialAuxiliaryHeight c d hcomp hbase U V S T)

theorem SolvedRelation.coefficientBudget_nonneg
    (R : SolvedRelation) (c d : ℤ)
    (hcomp : ∀ dir, IsIntegral ℤ (R.scaledComponentCoeff c dir))
    (hbase : ∀ i, IsIntegral ℤ (R.scaledBase d i))
    (U V S T : ℕ) :
    0 ≤ R.coefficientBudget c d hcomp hbase U V S T := by
  have hc := one_le_siegelConstant R.CoefficientField
  have hH := R.polynomialAuxiliaryHeight_nonneg c d hcomp hbase U V S T
  unfold SolvedRelation.coefficientBudget
  have h0 : (0 : ℝ) ≤ GelfondSchneiderSiegel.c₁ R.CoefficientField := by linarith
  exact mul_nonneg h0 (mul_nonneg (mul_nonneg h0 (Nat.cast_nonneg _)) hH)

/-- At the exact two-to-one column count the Siegel exponent is one, so the kernel vector obeys
the linear coefficient budget. -/
theorem SolvedRelation.exists_polynomial_auxiliary_coefficients_budget
    (R : SolvedRelation) (c d : ℤ)
    (hcomp : ∀ dir, IsIntegral ℤ (R.scaledComponentCoeff c dir))
    (hbase : ∀ i, IsIntegral ℤ (R.scaledBase d i))
    (U V S T : ℕ) (hU : 0 < U) (hV : 0 < V) (hS : 0 < S) (hT : 0 < T)
    (hd : d ≠ 0) (hdouble : 2 * (S * T ^ R.n) = U * V ^ R.n) :
    ∃ eta : R.AuxiliaryColumn U V → 𝓞 R.CoefficientField, eta ≠ 0 ∧
      Matrix.mulVec (R.polynomialAuxiliaryMatrix c d hcomp hbase U V S T) eta = 0 ∧
      ∀ col, house ((algebraMap (𝓞 R.CoefficientField) R.CoefficientField) (eta col)) ≤
        R.coefficientBudget c d hcomp hbase U V S T := by
  have hrowpos : 0 < S * T ^ R.n := Nat.mul_pos hS (pow_pos hT _)
  have hcard : Fintype.card (R.AuxiliaryRow S T) < Fintype.card (R.AuxiliaryColumn U V) := by
    rw [R.card_auxiliaryRow, R.card_auxiliaryColumn, ← hdouble]
    omega
  obtain ⟨eta, heta, hker, hbound⟩ :=
    R.exists_polynomial_auxiliary_coefficients c d hcomp hbase U V S T hU hV hS hT hd hcard
  refine ⟨eta, heta, hker, fun col => ?_⟩
  refine le_trans (hbound col) (le_of_eq ?_)
  have hexp : ((Fintype.card (R.AuxiliaryRow S T) : ℝ) /
      ((Fintype.card (R.AuxiliaryColumn U V) : ℝ) -
        (Fintype.card (R.AuxiliaryRow S T) : ℝ))) = 1 := by
    rw [R.card_auxiliaryRow, R.card_auxiliaryColumn, ← hdouble]
    have hr : (0 : ℝ) < ((S * T ^ R.n : ℕ) : ℝ) := by exact_mod_cast hrowpos
    push_cast
    field_simp
    norm_num
  rw [hexp, Real.rpow_one]
  unfold SolvedRelation.coefficientBudget
  rw [R.card_auxiliaryColumn]

end GaloisForLFunctions.RHTower.BakerGeneralProof
