import GaloisForLFunctions.RHTower.BakerGeneralProof.ExponentialMonomial
import GaloisForLFunctions.RHTower.GelfondSchneiderSiegel

/-!
# Integral auxiliary matrix for the general Baker theorem

Columns are exponential monomials and rows consist of a nonnegative integer sample together with
a bounded multi-index in all solved component directions.  The exponential bases need not be
algebraic integers.  A single global denominator-clearing power of their common integer scale is
therefore included in every entry.  At a fixed row it becomes a common nonzero factor of the
uncleared analytic constraint; this is what allows the eventual Siegel kernel to give genuine
auxiliary-function zeros rather than merely rescaled equations.
-/

open scoped Classical
open BigOperators NumberField

namespace GaloisForLFunctions.RHTower.BakerGeneralProof

/-- A sample index and a bounded multi-index in every component direction. -/
abbrev SolvedRelation.AuxiliaryRow (R : SolvedRelation) (S T : ℕ) :=
  Fin S × (R.Direction → Fin T)

/-- Total exponential degree of a bounded exponent vector. -/
def SolvedRelation.exponentialDegree {L : ℕ}
    (R : SolvedRelation) (m : R.ExponentialColumn L) : ℕ :=
  ∑ i, (m i : ℕ)

/-- Uniform exponent that clears all base denominators in the sample box. -/
def SolvedRelation.clearingBound (R : SolvedRelation) (S L : ℕ) : ℕ :=
  S * (R.n * L)

/-- Remaining power of the common base scale in one matrix entry. -/
def SolvedRelation.clearingExponent (R : SolvedRelation) {L S T : ℕ}
    (row : R.AuxiliaryRow S T) (m : R.ExponentialColumn L) : ℕ :=
  R.clearingBound S L - (row.1 : ℕ) * R.exponentialDegree m

/-- An exponential base after multiplying by the common integral base scale. -/
noncomputable def SolvedRelation.scaledBase
    (R : SolvedRelation) (d : ℤ) (i : Fin R.n) : R.CoefficientField :=
  d • R.baseLift i

/-- Product of component eigenvalues selected by a row multi-index. -/
noncomputable def SolvedRelation.componentEigenProduct
    (R : SolvedRelation) (c : ℤ) {L T : ℕ}
    (nu : R.Direction → Fin T) (m : R.ExponentialColumn L) : R.CoefficientField :=
  ∏ dir, R.componentEigenvalue c dir m ^ (nu dir : ℕ)

/-- Integral version of the exponential monomial at a nonnegative integer sample. -/
noncomputable def SolvedRelation.scaledBaseSample
    (R : SolvedRelation) (d : ℤ) {L S : ℕ}
    (sample : Fin S) (m : R.ExponentialColumn L) : R.CoefficientField :=
  ∏ i, R.scaledBase d i ^ ((m i : ℕ) * (sample : ℕ))

/-- One denominator-cleared component/sample constraint. -/
noncomputable def SolvedRelation.auxiliaryEntry
    (R : SolvedRelation) (c d : ℤ) {L S T : ℕ}
    (row : R.AuxiliaryRow S T) (m : R.ExponentialColumn L) : R.CoefficientField :=
  R.integerScalar d ^ R.clearingExponent row m *
    R.componentEigenProduct c row.2 m * R.scaledBaseSample d row.1 m

theorem SolvedRelation.exponentialDegree_le
    (R : SolvedRelation) {L : ℕ} (m : R.ExponentialColumn L) :
    R.exponentialDegree m ≤ R.n * L := by
  unfold SolvedRelation.exponentialDegree
  calc
    (∑ i, (m i : ℕ)) ≤ ∑ _i : Fin R.n, L := by
      apply Finset.sum_le_sum
      intro i _
      exact (m i).isLt.le
    _ = R.n * L := by simp [mul_comm]

/-- The denominator-clearing exponent is nonnegative before truncating subtraction. -/
theorem SolvedRelation.sample_degree_le_clearingBound
    (R : SolvedRelation) {L S T : ℕ}
    (row : R.AuxiliaryRow S T) (m : R.ExponentialColumn L) :
    (row.1 : ℕ) * R.exponentialDegree m ≤ R.clearingBound S L := by
  unfold SolvedRelation.clearingBound
  exact Nat.mul_le_mul row.1.isLt.le (R.exponentialDegree_le m)

theorem SolvedRelation.integerScalar_isIntegral (R : SolvedRelation) (d : ℤ) :
    IsIntegral ℤ (R.integerScalar d) := by
  unfold SolvedRelation.integerScalar
  exact isIntegral_one.zsmul d

theorem SolvedRelation.integerScalar_ne_zero (R : SolvedRelation) (d : ℤ) (hd : d ≠ 0) :
    R.integerScalar d ≠ 0 := by
  unfold SolvedRelation.integerScalar
  rw [zsmul_eq_mul, mul_one]
  exact_mod_cast hd

theorem SolvedRelation.scaledBase_eq_integerScalar_mul
    (R : SolvedRelation) (d : ℤ) (i : Fin R.n) :
    R.scaledBase d i = R.integerScalar d * R.baseLift i := by
  simp [SolvedRelation.scaledBase, SolvedRelation.integerScalar, zsmul_eq_mul]

theorem SolvedRelation.componentEigenProduct_isIntegral
    (R : SolvedRelation) (c : ℤ)
    (hcomp : ∀ dir, IsIntegral ℤ (R.scaledComponentCoeff c dir))
    {L T : ℕ} (nu : R.Direction → Fin T) (m : R.ExponentialColumn L) :
    IsIntegral ℤ (R.componentEigenProduct c nu m) := by
  unfold SolvedRelation.componentEigenProduct
  apply IsIntegral.prod
  intro dir _
  exact (R.componentEigenvalue_isIntegral c hcomp dir m).pow _

theorem SolvedRelation.scaledBaseSample_isIntegral
    (R : SolvedRelation) (d : ℤ)
    (hbase : ∀ i, IsIntegral ℤ (R.scaledBase d i))
    {L S : ℕ} (sample : Fin S) (m : R.ExponentialColumn L) :
    IsIntegral ℤ (R.scaledBaseSample d sample m) := by
  unfold SolvedRelation.scaledBaseSample
  apply IsIntegral.prod
  intro i _
  exact (hbase i).pow _

/-- Every denominator-cleared component/sample constraint is an algebraic integer. -/
theorem SolvedRelation.auxiliaryEntry_isIntegral
    (R : SolvedRelation) (c d : ℤ)
    (hcomp : ∀ dir, IsIntegral ℤ (R.scaledComponentCoeff c dir))
    (hbase : ∀ i, IsIntegral ℤ (R.scaledBase d i))
    {L S T : ℕ} (row : R.AuxiliaryRow S T) (m : R.ExponentialColumn L) :
    IsIntegral ℤ (R.auxiliaryEntry c d row m) := by
  unfold SolvedRelation.auxiliaryEntry
  simpa [mul_assoc] using ((R.integerScalar_isIntegral d).pow
    (R.clearingExponent row m)).mul
    ((R.componentEigenProduct_isIntegral c hcomp row.2 m).mul
      (R.scaledBaseSample_isIntegral d hbase row.1 m))

/-- The integral constraint matrix used by the number-field Siegel lemma. -/
noncomputable def SolvedRelation.auxiliaryMatrix
    (R : SolvedRelation) (c d : ℤ)
    (hcomp : ∀ dir, IsIntegral ℤ (R.scaledComponentCoeff c dir))
    (hbase : ∀ i, IsIntegral ℤ (R.scaledBase d i))
    (L S T : ℕ) : Matrix (R.AuxiliaryRow S T) (R.ExponentialColumn L)
      (𝓞 R.CoefficientField) :=
  fun row m => ⟨R.auxiliaryEntry c d row m,
    R.auxiliaryEntry_isIntegral c d hcomp hbase row m⟩

/-- Finite entrywise house sum, sufficient for the explicit number-field Siegel lemma. -/
noncomputable def SolvedRelation.auxiliaryHeight
    (R : SolvedRelation) (c d : ℤ)
    (hcomp : ∀ dir, IsIntegral ℤ (R.scaledComponentCoeff c dir))
    (hbase : ∀ i, IsIntegral ℤ (R.scaledBase d i))
    (L S T : ℕ) : ℝ :=
  ∑ row : R.AuxiliaryRow S T, ∑ m : R.ExponentialColumn L,
    house ((algebraMap (𝓞 R.CoefficientField) R.CoefficientField)
      (R.auxiliaryMatrix c d hcomp hbase L S T row m))

theorem SolvedRelation.auxiliaryHeight_nonneg
    (R : SolvedRelation) (c d : ℤ)
    (hcomp : ∀ dir, IsIntegral ℤ (R.scaledComponentCoeff c dir))
    (hbase : ∀ i, IsIntegral ℤ (R.scaledBase d i))
    (L S T : ℕ) : 0 ≤ R.auxiliaryHeight c d hcomp hbase L S T := by
  unfold SolvedRelation.auxiliaryHeight
  exact Finset.sum_nonneg fun row hrow =>
    Finset.sum_nonneg fun m hm => house_nonneg _

theorem SolvedRelation.auxiliaryEntry_house_le_height
    (R : SolvedRelation) (c d : ℤ)
    (hcomp : ∀ dir, IsIntegral ℤ (R.scaledComponentCoeff c dir))
    (hbase : ∀ i, IsIntegral ℤ (R.scaledBase d i))
    (L S T : ℕ) (row : R.AuxiliaryRow S T) (m : R.ExponentialColumn L) :
    house ((algebraMap (𝓞 R.CoefficientField) R.CoefficientField)
      (R.auxiliaryMatrix c d hcomp hbase L S T row m)) ≤
      R.auxiliaryHeight c d hcomp hbase L S T := by
  unfold SolvedRelation.auxiliaryHeight
  apply le_trans (Finset.single_le_sum (fun m' _ => house_nonneg _) (Finset.mem_univ m))
  exact Finset.single_le_sum
    (f := fun row' : R.AuxiliaryRow S T => ∑ m' : R.ExponentialColumn L,
      house ((algebraMap (𝓞 R.CoefficientField) R.CoefficientField)
        (R.auxiliaryMatrix c d hcomp hbase L S T row' m')))
    (fun row' _ => Finset.sum_nonneg fun m' _ => house_nonneg _) (Finset.mem_univ row)

@[simp] theorem SolvedRelation.card_exponentialColumn (R : SolvedRelation) (L : ℕ) :
    Fintype.card (R.ExponentialColumn L) = L ^ R.n := by
  simp [SolvedRelation.ExponentialColumn]

@[simp] theorem SolvedRelation.card_direction (R : SolvedRelation) :
    Fintype.card R.Direction = R.n := by
  have hnonpivot : Fintype.card R.NonPivot = R.n - 1 := by
    simp [SolvedRelation.NonPivot]
  have hn : 0 < R.n := Fin.pos R.pivot
  calc
    Fintype.card R.Direction = Fintype.card R.NonPivot + 1 := by
      simp only [SolvedRelation.Direction, Fintype.card_option]
    _ = R.n - 1 + 1 := by rw [hnonpivot]
    _ = R.n := Nat.sub_add_cancel (by omega)

@[simp] theorem SolvedRelation.card_auxiliaryRow (R : SolvedRelation) (S T : ℕ) :
    Fintype.card (R.AuxiliaryRow S T) = S * T ^ R.n := by
  change Fintype.card (Fin S × (R.Direction → Fin T)) = S * T ^ R.n
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_fun]
  rw [R.card_direction]

/-- The matrix has a nonzero zero-jet/zero-exponent entry whenever the base scale is nonzero. -/
theorem SolvedRelation.auxiliaryMatrix_ne_zero
    (R : SolvedRelation) (c d : ℤ)
    (hcomp : ∀ dir, IsIntegral ℤ (R.scaledComponentCoeff c dir))
    (hbase : ∀ i, IsIntegral ℤ (R.scaledBase d i))
    (L S T : ℕ) (hL : 0 < L) (hS : 0 < S) (hT : 0 < T) (hd : d ≠ 0) :
    R.auxiliaryMatrix c d hcomp hbase L S T ≠ 0 := by
  let row0 : R.AuxiliaryRow S T := ⟨⟨0, hS⟩, fun _ => ⟨0, hT⟩⟩
  let col0 : R.ExponentialColumn L := fun _ => ⟨0, hL⟩
  intro hzero
  have hentry := congrFun (congrFun hzero row0) col0
  have hval := congrArg Subtype.val hentry
  change R.auxiliaryEntry c d row0 col0 = 0 at hval
  have hscalar : R.integerScalar d ^ R.clearingBound S L ≠ 0 :=
    pow_ne_zero _ (R.integerScalar_ne_zero d hd)
  have hz : R.integerScalar d ^ R.clearingBound S L = 0 := by
    simpa only [SolvedRelation.auxiliaryEntry,
      SolvedRelation.componentEigenProduct, SolvedRelation.scaledBaseSample,
      SolvedRelation.clearingExponent, SolvedRelation.exponentialDegree,
      row0, col0, Finset.prod_const_one, Finset.sum_const_zero, zero_mul,
      Nat.zero_mul, Nat.zero_sub, Nat.sub_zero, pow_zero, mul_one, one_mul] using hval
  exact hscalar hz

/-- Siegel's lemma supplies a nonzero integral auxiliary coefficient vector. -/
theorem SolvedRelation.exists_auxiliary_coefficients
    (R : SolvedRelation) (c d : ℤ)
    (hcomp : ∀ dir, IsIntegral ℤ (R.scaledComponentCoeff c dir))
    (hbase : ∀ i, IsIntegral ℤ (R.scaledBase d i))
    (L S T : ℕ) (hL : 0 < L) (hS : 0 < S) (hT : 0 < T) (hd : d ≠ 0)
    (hcard : Fintype.card (R.AuxiliaryRow S T) < Fintype.card (R.ExponentialColumn L)) :
    ∃ eta : R.ExponentialColumn L → 𝓞 R.CoefficientField, eta ≠ 0 ∧
      Matrix.mulVec (R.auxiliaryMatrix c d hcomp hbase L S T) eta = 0 ∧
      ∀ m, house ((algebraMap (𝓞 R.CoefficientField) R.CoefficientField) (eta m)) ≤
        GelfondSchneiderSiegel.c₁ R.CoefficientField *
          (GelfondSchneiderSiegel.c₁ R.CoefficientField *
            (Fintype.card (R.ExponentialColumn L) : ℝ) *
            R.auxiliaryHeight c d hcomp hbase L S T) ^
              ((Fintype.card (R.AuxiliaryRow S T) : ℝ) /
                ((Fintype.card (R.ExponentialColumn L) : ℝ) -
                  (Fintype.card (R.AuxiliaryRow S T) : ℝ))) := by
  let A := R.auxiliaryMatrix c d hcomp hbase L S T
  have hrow : 0 < Fintype.card (R.AuxiliaryRow S T) :=
    Fintype.card_pos_iff.mpr ⟨⟨⟨0, hS⟩, fun _ => ⟨0, hT⟩⟩⟩
  obtain ⟨eta, heta, hker, hbound⟩ :=
    GelfondSchneiderSiegel.exists_ne_zero_int_vec_house_le R.CoefficientField A
      (R.auxiliaryMatrix_ne_zero c d hcomp hbase L S T hL hS hT hd) hrow hcard rfl
      (R.auxiliaryEntry_house_le_height c d hcomp hbase L S T) rfl
  refine ⟨eta, heta, hker, ?_⟩
  simpa using! hbound

/-- Both common scales and a nonzero Siegel-kernel vector are produced from a solved relation. -/
theorem SolvedRelation.exists_scaled_auxiliary_coefficients
    (R : SolvedRelation) (L S T : ℕ) (hL : 0 < L) (hS : 0 < S) (hT : 0 < T)
    (hcard : S * T ^ R.n < L ^ R.n) :
    ∃ c : ℤ, c ≠ 0 ∧ ∃ d : ℤ, d ≠ 0 ∧
      ∃ hcomp : ∀ dir, IsIntegral ℤ (R.scaledComponentCoeff c dir),
      ∃ hbase : ∀ i, IsIntegral ℤ (R.scaledBase d i),
      ∃ eta : R.ExponentialColumn L → 𝓞 R.CoefficientField, eta ≠ 0 ∧
        Matrix.mulVec (R.auxiliaryMatrix c d hcomp hbase L S T) eta = 0 := by
  obtain ⟨c, hc, hcomp0⟩ := R.exists_component_common_integer_scale
  obtain ⟨d, hd, hbase0⟩ := R.exists_base_common_integer_scale
  have hcomp : ∀ dir, IsIntegral ℤ (R.scaledComponentCoeff c dir) := by
    simpa [SolvedRelation.scaledComponentCoeff] using hcomp0
  have hbase : ∀ i, IsIntegral ℤ (R.scaledBase d i) := by
    simpa [SolvedRelation.scaledBase] using hbase0
  have hcard' : Fintype.card (R.AuxiliaryRow S T) < Fintype.card (R.ExponentialColumn L) := by
    rw [R.card_auxiliaryRow, R.card_exponentialColumn]
    exact hcard
  obtain ⟨eta, heta, hker, _⟩ :=
    R.exists_auxiliary_coefficients c d hcomp hbase L S T hL hS hT hd hcard'
  exact ⟨c, hc, d, hd, hcomp, hbase, eta, heta, hker⟩

end GaloisForLFunctions.RHTower.BakerGeneralProof
