import GaloisForLFunctions.RHTower.BakerGeneralProof.PolynomialAuxiliaryMonomial
import GaloisForLFunctions.RHTower.BakerGeneralProof.AuxiliaryMatrix

/-!
# Full integral auxiliary matrix for Baker's theorem

The exponential-only matrix is a valid supporting construction but cannot meet the parameter
inequalities in Baker's long extrapolation.  This module adds the additive-degree coordinate.
Its closed-form entries are the component-jet values of monomials
`Y₀^a ∏ᵢ Yᵢ^mᵢ`: nonconstant components are diagonal, while the constant component contributes
the binomial sum of its lowering and diagonal parts.  A later transport module identifies the
closed formula with iterated component derivations on the analytic auxiliary polynomial.

The present algebraic layer proves integrality, finite height control, nonzeroness, and the
unconditional number-field Siegel kernel in exactly the full column cardinality
`U * V ^ n` required by the paper proof.
-/

open scoped Classical
open BigOperators NumberField

namespace GaloisForLFunctions.RHTower.BakerGeneralProof

/-- Product of the diagonal eigenvalues for all nonconstant component directions. -/
noncomputable def SolvedRelation.nonconstantEigenProduct
    (R : SolvedRelation) (c : ℤ) {V : ℕ}
    (nu : R.Direction → ℕ) (m : R.ExponentialColumn V) : R.CoefficientField :=
  ∏ i : R.NonPivot, R.componentEigenvalue c (some i) m ^ nu (some i)

/-- The `k`-th lowering contribution to an iterated constant-component jet. -/
noncomputable def SolvedRelation.constantJetTerm
    (R : SolvedRelation) (c : ℤ) {V : ℕ}
    (r a sample k : ℕ) (m : R.ExponentialColumn V) : R.CoefficientField :=
  (Nat.choose r k : R.CoefficientField) *
    (a.descFactorial k : R.CoefficientField) *
      R.integerScalar c ^ k * R.componentEigenvalue c none m ^ (r - k) *
        (sample : R.CoefficientField) ^ (a - k)

/-- Closed-form value of the `r`-fold constant-component jet at an integer sample. -/
noncomputable def SolvedRelation.constantJetCoefficient
    (R : SolvedRelation) (c : ℤ) {V : ℕ}
    (r a sample : ℕ) (m : R.ExponentialColumn V) : R.CoefficientField :=
  ∑ k ∈ Finset.range (r + 1), R.constantJetTerm c r a sample k m

/-- Closed-form full component-jet coefficient at an integer sample. -/
noncomputable def SolvedRelation.additiveComponentJetCoefficient
    (R : SolvedRelation) (c : ℤ) {V : ℕ}
    (nu : R.Direction → ℕ) (a sample : ℕ) (m : R.ExponentialColumn V) :
    R.CoefficientField :=
  R.nonconstantEigenProduct c nu m *
    R.constantJetCoefficient c (nu none) a sample m

@[simp] theorem SolvedRelation.nonconstantEigenProduct_zero
    (R : SolvedRelation) (c : ℤ) {V : ℕ} (m : R.ExponentialColumn V) :
    R.nonconstantEigenProduct c (fun _ => 0) m = 1 := by
  simp [SolvedRelation.nonconstantEigenProduct]

@[simp] theorem SolvedRelation.constantJetCoefficient_zero
    (R : SolvedRelation) (c : ℤ) {V : ℕ} (m : R.ExponentialColumn V) :
    R.constantJetCoefficient c 0 0 0 m = 1 := by
  simp [SolvedRelation.constantJetCoefficient, SolvedRelation.constantJetTerm]

theorem SolvedRelation.constantJetTerm_isIntegral
    (R : SolvedRelation) (c : ℤ)
    (hcomp : ∀ dir, IsIntegral ℤ (R.scaledComponentCoeff c dir))
    {V : ℕ} (r a sample k : ℕ) (m : R.ExponentialColumn V) :
    IsIntegral ℤ (R.constantJetTerm c r a sample k m) := by
  have hchoose : IsIntegral ℤ ((Nat.choose r k : ℕ) • (1 : R.CoefficientField)) :=
    isIntegral_one.nsmul _
  have hdesc : IsIntegral ℤ ((a.descFactorial k : ℕ) • (1 : R.CoefficientField)) :=
    isIntegral_one.nsmul _
  have hsample : IsIntegral ℤ (sample • (1 : R.CoefficientField)) :=
    isIntegral_one.nsmul _
  simpa [SolvedRelation.constantJetTerm] using
    ((((hchoose.mul hdesc).mul ((R.integerScalar_isIntegral c).pow k)).mul
      ((R.componentEigenvalue_isIntegral c hcomp none m).pow (r - k))).mul
        (hsample.pow (a - k)))

theorem SolvedRelation.constantJetCoefficient_isIntegral
    (R : SolvedRelation) (c : ℤ)
    (hcomp : ∀ dir, IsIntegral ℤ (R.scaledComponentCoeff c dir))
    {V : ℕ} (r a sample : ℕ) (m : R.ExponentialColumn V) :
    IsIntegral ℤ (R.constantJetCoefficient c r a sample m) := by
  unfold SolvedRelation.constantJetCoefficient
  apply IsIntegral.sum
  intro k _
  exact R.constantJetTerm_isIntegral c hcomp r a sample k m

theorem SolvedRelation.nonconstantEigenProduct_isIntegral
    (R : SolvedRelation) (c : ℤ)
    (hcomp : ∀ dir, IsIntegral ℤ (R.scaledComponentCoeff c dir))
    {V : ℕ} (nu : R.Direction → ℕ) (m : R.ExponentialColumn V) :
    IsIntegral ℤ (R.nonconstantEigenProduct c nu m) := by
  unfold SolvedRelation.nonconstantEigenProduct
  apply IsIntegral.prod
  intro i _
  exact (R.componentEigenvalue_isIntegral c hcomp (some i) m).pow _

theorem SolvedRelation.additiveComponentJetCoefficient_isIntegral
    (R : SolvedRelation) (c : ℤ)
    (hcomp : ∀ dir, IsIntegral ℤ (R.scaledComponentCoeff c dir))
    {V : ℕ} (nu : R.Direction → ℕ) (a sample : ℕ) (m : R.ExponentialColumn V) :
    IsIntegral ℤ (R.additiveComponentJetCoefficient c nu a sample m) := by
  unfold SolvedRelation.additiveComponentJetCoefficient
  exact (R.nonconstantEigenProduct_isIntegral c hcomp nu m).mul
    (R.constantJetCoefficient_isIntegral c hcomp (nu none) a sample m)

/-- One denominator-cleared full additive--exponential component/sample constraint. -/
noncomputable def SolvedRelation.polynomialAuxiliaryEntry
    (R : SolvedRelation) (c d : ℤ) {U V S T : ℕ}
    (row : R.AuxiliaryRow S T) (col : R.AuxiliaryColumn U V) :
    R.CoefficientField :=
  R.integerScalar d ^ R.clearingExponent row col.2 *
    R.additiveComponentJetCoefficient c (fun dir => (row.2 dir : ℕ))
      (col.1 : ℕ) (row.1 : ℕ) col.2 *
      R.scaledBaseSample d row.1 col.2

theorem SolvedRelation.polynomialAuxiliaryEntry_isIntegral
    (R : SolvedRelation) (c d : ℤ)
    (hcomp : ∀ dir, IsIntegral ℤ (R.scaledComponentCoeff c dir))
    (hbase : ∀ i, IsIntegral ℤ (R.scaledBase d i))
    {U V S T : ℕ} (row : R.AuxiliaryRow S T) (col : R.AuxiliaryColumn U V) :
    IsIntegral ℤ (R.polynomialAuxiliaryEntry c d row col) := by
  unfold SolvedRelation.polynomialAuxiliaryEntry
  simpa [mul_assoc] using ((R.integerScalar_isIntegral d).pow
    (R.clearingExponent row col.2)).mul
    ((R.additiveComponentJetCoefficient_isIntegral c hcomp
      (fun dir => (row.2 dir : ℕ)) (col.1 : ℕ) (row.1 : ℕ) col.2).mul
      (R.scaledBaseSample_isIntegral d hbase row.1 col.2))

/-- Integral full auxiliary matrix used by the general number-field Siegel lemma. -/
noncomputable def SolvedRelation.polynomialAuxiliaryMatrix
    (R : SolvedRelation) (c d : ℤ)
    (hcomp : ∀ dir, IsIntegral ℤ (R.scaledComponentCoeff c dir))
    (hbase : ∀ i, IsIntegral ℤ (R.scaledBase d i))
    (U V S T : ℕ) : Matrix (R.AuxiliaryRow S T) (R.AuxiliaryColumn U V)
      (𝓞 R.CoefficientField) :=
  fun row col => ⟨R.polynomialAuxiliaryEntry c d row col,
    R.polynomialAuxiliaryEntry_isIntegral c d hcomp hbase row col⟩

/-- Finite entrywise house sum for the full auxiliary matrix. -/
noncomputable def SolvedRelation.polynomialAuxiliaryHeight
    (R : SolvedRelation) (c d : ℤ)
    (hcomp : ∀ dir, IsIntegral ℤ (R.scaledComponentCoeff c dir))
    (hbase : ∀ i, IsIntegral ℤ (R.scaledBase d i))
    (U V S T : ℕ) : ℝ :=
  ∑ row : R.AuxiliaryRow S T, ∑ col : R.AuxiliaryColumn U V,
    house ((algebraMap (𝓞 R.CoefficientField) R.CoefficientField)
      (R.polynomialAuxiliaryMatrix c d hcomp hbase U V S T row col))

theorem SolvedRelation.polynomialAuxiliaryHeight_nonneg
    (R : SolvedRelation) (c d : ℤ)
    (hcomp : ∀ dir, IsIntegral ℤ (R.scaledComponentCoeff c dir))
    (hbase : ∀ i, IsIntegral ℤ (R.scaledBase d i))
    (U V S T : ℕ) :
    0 ≤ R.polynomialAuxiliaryHeight c d hcomp hbase U V S T := by
  unfold SolvedRelation.polynomialAuxiliaryHeight
  exact Finset.sum_nonneg fun row hrow =>
    Finset.sum_nonneg fun col hcol => house_nonneg _

theorem SolvedRelation.polynomialAuxiliaryEntry_house_le_height
    (R : SolvedRelation) (c d : ℤ)
    (hcomp : ∀ dir, IsIntegral ℤ (R.scaledComponentCoeff c dir))
    (hbase : ∀ i, IsIntegral ℤ (R.scaledBase d i))
    (U V S T : ℕ) (row : R.AuxiliaryRow S T) (col : R.AuxiliaryColumn U V) :
    house ((algebraMap (𝓞 R.CoefficientField) R.CoefficientField)
      (R.polynomialAuxiliaryMatrix c d hcomp hbase U V S T row col)) ≤
      R.polynomialAuxiliaryHeight c d hcomp hbase U V S T := by
  unfold SolvedRelation.polynomialAuxiliaryHeight
  apply le_trans (Finset.single_le_sum (fun col' _ => house_nonneg _) (Finset.mem_univ col))
  exact Finset.single_le_sum
    (f := fun row' : R.AuxiliaryRow S T => ∑ col' : R.AuxiliaryColumn U V,
      house ((algebraMap (𝓞 R.CoefficientField) R.CoefficientField)
        (R.polynomialAuxiliaryMatrix c d hcomp hbase U V S T row' col')))
    (fun row' _ => Finset.sum_nonneg fun col' _ => house_nonneg _) (Finset.mem_univ row)

@[simp] theorem SolvedRelation.card_auxiliaryColumn (R : SolvedRelation) (U V : ℕ) :
    Fintype.card (R.AuxiliaryColumn U V) = U * V ^ R.n := by
  change Fintype.card (Fin U × (Fin R.n → Fin V)) = U * V ^ R.n
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_fun]

/-- The full matrix has a nonzero zero-jet/zero-monomial entry. -/
theorem SolvedRelation.polynomialAuxiliaryMatrix_ne_zero
    (R : SolvedRelation) (c d : ℤ)
    (hcomp : ∀ dir, IsIntegral ℤ (R.scaledComponentCoeff c dir))
    (hbase : ∀ i, IsIntegral ℤ (R.scaledBase d i))
    (U V S T : ℕ) (hU : 0 < U) (hV : 0 < V) (hS : 0 < S) (hT : 0 < T)
    (hd : d ≠ 0) :
    R.polynomialAuxiliaryMatrix c d hcomp hbase U V S T ≠ 0 := by
  let row0 : R.AuxiliaryRow S T := ⟨⟨0, hS⟩, fun _ => ⟨0, hT⟩⟩
  let col0 : R.AuxiliaryColumn U V := ⟨⟨0, hU⟩, fun _ => ⟨0, hV⟩⟩
  intro hzero
  have hentry := congrFun (congrFun hzero row0) col0
  have hval := congrArg Subtype.val hentry
  change R.polynomialAuxiliaryEntry c d row0 col0 = 0 at hval
  have hscalar : R.integerScalar d ^ R.clearingBound S V ≠ 0 :=
    pow_ne_zero _ (R.integerScalar_ne_zero d hd)
  have hz : R.integerScalar d ^ R.clearingBound S V = 0 := by
    simpa [SolvedRelation.polynomialAuxiliaryEntry,
      SolvedRelation.additiveComponentJetCoefficient,
      SolvedRelation.scaledBaseSample, SolvedRelation.clearingExponent,
      SolvedRelation.exponentialDegree, row0, col0] using hval
  exact hscalar hz

/-- Siegel's lemma gives a nonzero integral full auxiliary coefficient vector. -/
theorem SolvedRelation.exists_polynomial_auxiliary_coefficients
    (R : SolvedRelation) (c d : ℤ)
    (hcomp : ∀ dir, IsIntegral ℤ (R.scaledComponentCoeff c dir))
    (hbase : ∀ i, IsIntegral ℤ (R.scaledBase d i))
    (U V S T : ℕ) (hU : 0 < U) (hV : 0 < V) (hS : 0 < S) (hT : 0 < T)
    (hd : d ≠ 0)
    (hcard : Fintype.card (R.AuxiliaryRow S T) < Fintype.card (R.AuxiliaryColumn U V)) :
    ∃ eta : R.AuxiliaryColumn U V → 𝓞 R.CoefficientField, eta ≠ 0 ∧
      Matrix.mulVec (R.polynomialAuxiliaryMatrix c d hcomp hbase U V S T) eta = 0 ∧
      ∀ col, house ((algebraMap (𝓞 R.CoefficientField) R.CoefficientField) (eta col)) ≤
        GelfondSchneiderSiegel.c₁ R.CoefficientField *
          (GelfondSchneiderSiegel.c₁ R.CoefficientField *
            (Fintype.card (R.AuxiliaryColumn U V) : ℝ) *
            R.polynomialAuxiliaryHeight c d hcomp hbase U V S T) ^
              ((Fintype.card (R.AuxiliaryRow S T) : ℝ) /
                ((Fintype.card (R.AuxiliaryColumn U V) : ℝ) -
                  (Fintype.card (R.AuxiliaryRow S T) : ℝ))) := by
  let A := R.polynomialAuxiliaryMatrix c d hcomp hbase U V S T
  have hrow : 0 < Fintype.card (R.AuxiliaryRow S T) :=
    Fintype.card_pos_iff.mpr ⟨⟨⟨0, hS⟩, fun _ => ⟨0, hT⟩⟩⟩
  obtain ⟨eta, heta, hker, hbound⟩ :=
    GelfondSchneiderSiegel.exists_ne_zero_int_vec_house_le R.CoefficientField A
      (R.polynomialAuxiliaryMatrix_ne_zero c d hcomp hbase U V S T hU hV hS hT hd) hrow
      hcard rfl (R.polynomialAuxiliaryEntry_house_le_height c d hcomp hbase U V S T) rfl
  refine ⟨eta, heta, hker, ?_⟩
  simpa using! hbound

/-- Simultaneously choose both integral scales and a nonzero full Siegel-kernel vector. -/
theorem SolvedRelation.exists_scaled_polynomial_auxiliary_coefficients
    (R : SolvedRelation) (U V S T : ℕ)
    (hU : 0 < U) (hV : 0 < V) (hS : 0 < S) (hT : 0 < T)
    (hcard : S * T ^ R.n < U * V ^ R.n) :
    ∃ c : ℤ, c ≠ 0 ∧ ∃ d : ℤ, d ≠ 0 ∧
      ∃ hcomp : ∀ dir, IsIntegral ℤ (R.scaledComponentCoeff c dir),
      ∃ hbase : ∀ i, IsIntegral ℤ (R.scaledBase d i),
      ∃ eta : R.AuxiliaryColumn U V → 𝓞 R.CoefficientField, eta ≠ 0 ∧
        Matrix.mulVec (R.polynomialAuxiliaryMatrix c d hcomp hbase U V S T) eta = 0 := by
  obtain ⟨c, hc, hcomp0⟩ := R.exists_component_common_integer_scale
  obtain ⟨d, hd, hbase0⟩ := R.exists_base_common_integer_scale
  have hcomp : ∀ dir, IsIntegral ℤ (R.scaledComponentCoeff c dir) := by
    simpa [SolvedRelation.scaledComponentCoeff] using hcomp0
  have hbase : ∀ i, IsIntegral ℤ (R.scaledBase d i) := by
    simpa [SolvedRelation.scaledBase] using hbase0
  have hcard' : Fintype.card (R.AuxiliaryRow S T) < Fintype.card (R.AuxiliaryColumn U V) := by
    rw [R.card_auxiliaryRow, R.card_auxiliaryColumn]
    exact hcard
  obtain ⟨eta, heta, hker, _⟩ :=
    R.exists_polynomial_auxiliary_coefficients c d hcomp hbase U V S T hU hV hS hT hd hcard'
  exact ⟨c, hc, d, hd, hcomp, hbase, eta, heta, hker⟩

end GaloisForLFunctions.RHTower.BakerGeneralProof
