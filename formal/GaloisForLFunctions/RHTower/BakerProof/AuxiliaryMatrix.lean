import GaloisForLFunctions.RHTower.BakerProof.NormalizedRelation
import GaloisForLFunctions.RHTower.GelfondSchneiderSiegel

/-!
# The first several-variable Baker auxiliary matrix

Columns are bounded exponent vectors.  Rows consist of an integer sample point and a multi-index in
the non-pivot logarithmic directions.  After a common integer scaling of the algebraic coefficients,
every matrix entry is an algebraic integer.  The explicit-constant number-field Siegel theorem then
produces a nonzero kernel vector whenever there are more columns than rows.
-/

open scoped Classical
open BigOperators NumberField

namespace GaloisForLFunctions.RHTower.BakerProof

abbrev Relation.NonPivot (R : Relation) (pivot : Fin R.n) := {i : Fin R.n // i ≠ pivot}
abbrev Relation.Column (R : Relation) (L : ℕ) := Fin R.n → Fin L
abbrev Relation.Row (R : Relation) (pivot : Fin R.n) (S T : ℕ) :=
  Fin S × (R.NonPivot pivot → Fin T)

noncomputable def Relation.scaledCoeff (R : Relation) (c : ℤ) (i : Fin R.n) :
    R.CoefficientField := c • R.coeffLift i

/-- The integral direction coefficient obtained after eliminating the pivot logarithm and clearing
the common coefficient denominator. -/
noncomputable def Relation.scaledDirection (R : Relation) (c : ℤ) (pivot : Fin R.n)
    {L : ℕ} (m : R.Column L) (i : Fin R.n) : R.CoefficientField :=
  R.scaledCoeff c pivot * ((m i : ℕ) : R.CoefficientField) -
    ((m pivot : ℕ) : R.CoefficientField) * R.scaledCoeff c i

private theorem isIntegral_natCast_coefficientField (R : Relation) (a : ℕ) :
    IsIntegral ℤ (a : R.CoefficientField) := by
  rw [show (a : R.CoefficientField) = algebraMap ℤ R.CoefficientField (a : ℤ) by simp]
  exact isIntegral_algebraMap

theorem Relation.scaledDirection_isIntegral (R : Relation) (c : ℤ)
    (hint : ∀ i, IsIntegral ℤ (R.scaledCoeff c i)) (pivot : Fin R.n)
    {L : ℕ} (m : R.Column L) (i : Fin R.n) :
    IsIntegral ℤ (R.scaledDirection c pivot m i) := by
  exact (hint pivot).mul (isIntegral_natCast_coefficientField R (m i)) |>.sub
    ((isIntegral_natCast_coefficientField R (m pivot)).mul (hint i))

/-- The total coefficient house used to control every eliminated direction uniformly. -/
noncomputable def Relation.scaledCoefficientHouseSum (R : Relation) (c : ℤ) : ℝ :=
  ∑ i, house (R.scaledCoeff c i)

/-- Every eliminated direction has house at most linear in the exponent-box width. -/
theorem Relation.scaledDirection_house_le (R : Relation) (c : ℤ) (pivot : Fin R.n)
    {L : ℕ} (m : R.Column L) (i : Fin R.n) :
    house (R.scaledDirection c pivot m i) ≤
      2 * L * R.scaledCoefficientHouseSum c := by
  have hp : house (R.scaledCoeff c pivot) ≤ R.scaledCoefficientHouseSum c := by
    unfold Relation.scaledCoefficientHouseSum
    exact Finset.single_le_sum (fun j hj => house_nonneg _) (Finset.mem_univ pivot)
  have hi : house (R.scaledCoeff c i) ≤ R.scaledCoefficientHouseSum c := by
    unfold Relation.scaledCoefficientHouseSum
    exact Finset.single_le_sum (fun j hj => house_nonneg _) (Finset.mem_univ i)
  have hmi : ((m i : ℕ) : ℝ) ≤ L := by
    exact_mod_cast (m i).isLt.le
  have hmp : ((m pivot : ℕ) : ℝ) ≤ L := by
    exact_mod_cast (m pivot).isLt.le
  rw [Relation.scaledDirection]
  calc
    house (R.scaledCoeff c pivot * (m i : ℕ) -
        (m pivot : ℕ) * R.scaledCoeff c i) ≤
        house (R.scaledCoeff c pivot * (m i : ℕ)) +
          house (-((m pivot : ℕ) * R.scaledCoeff c i)) := by
      simpa [sub_eq_add_neg] using house_add_le
        (R.scaledCoeff c pivot * ((m i : ℕ) : R.CoefficientField))
        (-(((m pivot : ℕ) : R.CoefficientField) * R.scaledCoeff c i))
    _ = (m i : ℕ) * house (R.scaledCoeff c pivot) +
          (m pivot : ℕ) * house (R.scaledCoeff c i) := by
      rw [mul_comm (R.scaledCoeff c pivot)]
      rw [house_nat_mul]
      rw [show house (-(((m pivot : ℕ) : R.CoefficientField) * R.scaledCoeff c i)) =
          house (((m pivot : ℕ) : R.CoefficientField) * R.scaledCoeff c i) by
        simp [house]]
      rw [house_nat_mul]
    _ ≤ L * R.scaledCoefficientHouseSum c +
          L * R.scaledCoefficientHouseSum c := by
      apply add_le_add
      · exact mul_le_mul hmi hp (house_nonneg _) (Nat.cast_nonneg _)
      · exact mul_le_mul hmp hi (house_nonneg _) (Nat.cast_nonneg _)
    _ = 2 * L * R.scaledCoefficientHouseSum c := by ring

/-- The complete shifted-direction monomial is controlled by the total multiindex degree. -/
theorem Relation.scaledDirection_house_prod_pow_le (R : Relation) (c : ℤ)
    (pivot : Fin R.n) {L : ℕ} (m : R.Column L) (ν : R.NonPivot pivot → ℕ) :
    (∏ i : R.NonPivot pivot,
      house (R.scaledDirection c pivot m i) ^ ν i) ≤
      (2 * L * R.scaledCoefficientHouseSum c) ^ (∑ i, ν i) := by
  calc
    (∏ i : R.NonPivot pivot,
      house (R.scaledDirection c pivot m i) ^ ν i) ≤
        ∏ i : R.NonPivot pivot,
          (2 * L * R.scaledCoefficientHouseSum c) ^ ν i := by
      apply Finset.prod_le_prod
      · intro i hi
        exact pow_nonneg (house_nonneg _) _
      · intro i hi
        exact pow_le_pow_left₀ (house_nonneg _)
          (R.scaledDirection_house_le c pivot m i) _
    _ = (2 * L * R.scaledCoefficientHouseSum c) ^ (∑ i, ν i) := by
      simpa using Finset.prod_pow_eq_pow_sum
        (Finset.univ : Finset (R.NonPivot pivot)) ν
          (2 * L * R.scaledCoefficientHouseSum c)

/-- The algebraic prime-power evaluation factor at an integer sample. -/
noncomputable def Relation.sampleFactor (R : Relation) {L S : ℕ}
    (sample : Fin S) (m : R.Column L) : R.CoefficientField :=
  ∏ i, ((R.p i : ℕ) : R.CoefficientField) ^ ((m i : ℕ) * (sample : ℕ))

theorem Relation.sampleFactor_isIntegral (R : Relation) {L S : ℕ}
    (sample : Fin S) (m : R.Column L) : IsIntegral ℤ (R.sampleFactor sample m) := by
  apply IsIntegral.prod
  intro i hi
  exact (isIntegral_natCast_coefficientField R (R.p i)).pow _

/-- The fixed product of all primes in a reduced relation. -/
def Relation.primeProduct (R : Relation) : ℕ := ∏ i, R.p i

/-- The house of an integer sample factor is its ordinary real value. -/
theorem Relation.sampleFactor_house_eq (R : Relation) {L S : ℕ}
    (sample : Fin S) (m : R.Column L) :
    house (R.sampleFactor sample m) =
      ∏ i, ((R.p i : ℕ) : ℝ) ^ ((m i : ℕ) * (sample : ℕ)) := by
  rw [show R.sampleFactor sample m =
      ((∏ i, (R.p i) ^ ((m i : ℕ) * (sample : ℕ)) : ℕ) : R.CoefficientField) by
    simp [Relation.sampleFactor]]
  rw [show ((∏ i, (R.p i) ^ ((m i : ℕ) * (sample : ℕ)) : ℕ) :
      R.CoefficientField) =
      (((∏ i, (R.p i) ^ ((m i : ℕ) * (sample : ℕ)) : ℕ) : ℤ) :
        R.CoefficientField) by norm_num]
  rw [house_intCast]
  simp
  positivity

/-- Sample-factor houses grow at most like the fixed prime product to `L * sample`. -/
theorem Relation.sampleFactor_house_le (R : Relation) {L S : ℕ}
    (sample : Fin S) (m : R.Column L) :
    house (R.sampleFactor sample m) ≤
      (R.primeProduct : ℝ) ^ (L * (sample : ℕ)) := by
  rw [R.sampleFactor_house_eq sample m]
  unfold Relation.primeProduct
  push_cast
  rw [← Finset.prod_pow]
  apply Finset.prod_le_prod
  · intro i hi
    positivity
  · intro i hi
    norm_cast
    exact Nat.pow_le_pow_right (R.p_prime i).pos
      (Nat.mul_le_mul_right (sample : ℕ) (m i).isLt.le)

/-- One coefficient of the derivative/sample constraint matrix. -/
noncomputable def Relation.auxiliaryEntry (R : Relation) (c : ℤ) (pivot : Fin R.n)
    {L S T : ℕ} (row : R.Row pivot S T) (m : R.Column L) : R.CoefficientField :=
  (∏ i : R.NonPivot pivot, R.scaledDirection c pivot m i ^ (row.2 i : ℕ)) *
    R.sampleFactor row.1 m

theorem Relation.auxiliaryEntry_isIntegral (R : Relation) (c : ℤ)
    (hint : ∀ i, IsIntegral ℤ (R.scaledCoeff c i)) (pivot : Fin R.n)
    {L S T : ℕ} (row : R.Row pivot S T) (m : R.Column L) :
    IsIntegral ℤ (R.auxiliaryEntry c pivot row m) := by
  apply IsIntegral.mul
  · apply IsIntegral.prod
    intro i hi
    exact (R.scaledDirection_isIntegral c hint pivot m i).pow _
  · exact R.sampleFactor_isIntegral row.1 m

noncomputable def Relation.auxiliaryMatrix (R : Relation) (c : ℤ)
    (hint : ∀ i, IsIntegral ℤ (R.scaledCoeff c i)) (pivot : Fin R.n)
    (L S T : ℕ) : Matrix (R.Row pivot S T) (R.Column L) (𝓞 R.CoefficientField) :=
  fun row m => ⟨R.auxiliaryEntry c pivot row m,
    R.auxiliaryEntry_isIntegral c hint pivot row m⟩

/-- A finite, explicit house bound for every entry of the auxiliary matrix. -/
noncomputable def Relation.auxiliaryHeight (R : Relation) (c : ℤ)
    (hint : ∀ i, IsIntegral ℤ (R.scaledCoeff c i)) (pivot : Fin R.n)
    (L S T : ℕ) : ℝ :=
  ∑ row : R.Row pivot S T, ∑ m : R.Column L,
    house ((algebraMap (𝓞 R.CoefficientField) R.CoefficientField)
      (R.auxiliaryMatrix c hint pivot L S T row m))

theorem Relation.auxiliaryHeight_nonneg (R : Relation) (c : ℤ)
    (hint : ∀ i, IsIntegral ℤ (R.scaledCoeff c i)) (pivot : Fin R.n)
    (L S T : ℕ) : 0 ≤ R.auxiliaryHeight c hint pivot L S T := by
  unfold Relation.auxiliaryHeight
  exact Finset.sum_nonneg fun row hrow =>
    Finset.sum_nonneg fun m hm => house_nonneg _

theorem Relation.auxiliaryEntry_house_le_height (R : Relation) (c : ℤ)
    (hint : ∀ i, IsIntegral ℤ (R.scaledCoeff c i)) (pivot : Fin R.n)
    (L S T : ℕ) (row : R.Row pivot S T) (m : R.Column L) :
    house ((algebraMap (𝓞 R.CoefficientField) R.CoefficientField)
      (R.auxiliaryMatrix c hint pivot L S T row m)) ≤
      R.auxiliaryHeight c hint pivot L S T := by
  unfold Relation.auxiliaryHeight
  apply le_trans (Finset.single_le_sum (fun m' _ => house_nonneg _) (Finset.mem_univ m))
  exact Finset.single_le_sum
    (f := fun row' : R.Row pivot S T => ∑ m' : R.Column L,
      house ((algebraMap (𝓞 R.CoefficientField) R.CoefficientField)
        (R.auxiliaryMatrix c hint pivot L S T row' m')))
    (fun row' _ => Finset.sum_nonneg fun m' _ => house_nonneg _) (Finset.mem_univ row)

theorem Relation.auxiliaryMatrix_ne_zero (R : Relation) (c : ℤ)
    (hint : ∀ i, IsIntegral ℤ (R.scaledCoeff c i)) (pivot : Fin R.n)
    (L S T : ℕ) (hL : 0 < L) (hS : 0 < S) (hT : 0 < T) :
    R.auxiliaryMatrix c hint pivot L S T ≠ 0 := by
  let row0 : R.Row pivot S T := ⟨⟨0, hS⟩, fun _ => ⟨0, hT⟩⟩
  let col0 : R.Column L := fun _ => ⟨0, hL⟩
  intro hzero
  have hentry := congrFun (congrFun hzero row0) col0
  have hval := congrArg Subtype.val hentry
  simp [Relation.auxiliaryMatrix, Relation.auxiliaryEntry, Relation.sampleFactor,
    Relation.scaledDirection, row0, col0] at hval
  exact one_ne_zero hval

@[simp] theorem Relation.card_column (R : Relation) (L : ℕ) :
    Fintype.card (R.Column L) = L ^ R.n := by
  simp [Relation.Column]

@[simp] theorem Relation.card_nonPivot (R : Relation) (pivot : Fin R.n) :
    Fintype.card (R.NonPivot pivot) = R.n - 1 := by
  simp [Relation.NonPivot]

@[simp] theorem Relation.card_row (R : Relation) (pivot : Fin R.n) (S T : ℕ) :
    Fintype.card (R.Row pivot S T) = S * T ^ (R.n - 1) := by
  simp [Relation.Row, Relation.NonPivot]

/-- The explicit Siegel-lemma house bound for every coefficient of an auxiliary kernel vector. -/
noncomputable def Relation.auxiliaryCoefficientBound (R : Relation) (c : ℤ)
    (hint : ∀ i, IsIntegral ℤ (R.scaledCoeff c i)) (pivot : Fin R.n)
    (L S T : ℕ) : ℝ :=
  GelfondSchneiderSiegel.c₁ R.CoefficientField *
    (GelfondSchneiderSiegel.c₁ R.CoefficientField *
      (Fintype.card (R.Column L) : ℝ) * R.auxiliaryHeight c hint pivot L S T) ^
      ((Fintype.card (R.Row pivot S T) : ℝ) /
        ((Fintype.card (R.Column L) : ℝ) -
          (Fintype.card (R.Row pivot S T) : ℝ)))

theorem Relation.auxiliaryCoefficientBound_nonneg (R : Relation) (c : ℤ)
    (hint : ∀ i, IsIntegral ℤ (R.scaledCoeff c i)) (pivot : Fin R.n)
    (L S T : ℕ) : 0 ≤ R.auxiliaryCoefficientBound c hint pivot L S T := by
  have hc1 : 0 ≤ GelfondSchneiderSiegel.c₁ R.CoefficientField := by
    unfold GelfondSchneiderSiegel.c₁ GelfondSchneiderSiegel.c₂
    exact mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (le_trans (by norm_num) (le_max_left 1 _))
        (le_trans (by norm_num) (GelfondSchneiderSiegel.one_le_supOfBasis _)))
  unfold Relation.auxiliaryCoefficientBound
  apply mul_nonneg hc1
  apply Real.rpow_nonneg
  exact mul_nonneg (mul_nonneg hc1 (Nat.cast_nonneg _))
    (R.auxiliaryHeight_nonneg c hint pivot L S T)

/-- **Baker auxiliary Siegel bridge.**  If the derivative/sample system has fewer rows than exponent
columns, it has a nonzero algebraic-integer coefficient vector annihilating every row, with the
explicit coefficient-height bound required by extrapolation. -/
theorem Relation.exists_auxiliary_coefficients (R : Relation) (c : ℤ)
    (hint : ∀ i, IsIntegral ℤ (R.scaledCoeff c i)) (pivot : Fin R.n)
    (L S T : ℕ) (hL : 0 < L) (hS : 0 < S) (hT : 0 < T)
    (hcard : Fintype.card (R.Row pivot S T) < Fintype.card (R.Column L)) :
    ∃ η : R.Column L → 𝓞 R.CoefficientField, η ≠ 0 ∧
      Matrix.mulVec (R.auxiliaryMatrix c hint pivot L S T) η = 0 ∧
      ∀ m, house ((algebraMap (𝓞 R.CoefficientField) R.CoefficientField) (η m)) ≤
        R.auxiliaryCoefficientBound c hint pivot L S T := by
  let A := R.auxiliaryMatrix c hint pivot L S T
  have hrow : 0 < Fintype.card (R.Row pivot S T) :=
    Fintype.card_pos_iff.mpr ⟨⟨⟨0, hS⟩, fun _ => ⟨0, hT⟩⟩⟩
  obtain ⟨η, hη, hker, hbound⟩ :=
    GelfondSchneiderSiegel.exists_ne_zero_int_vec_house_le R.CoefficientField A
      (R.auxiliaryMatrix_ne_zero c hint pivot L S T hL hS hT) hrow hcard rfl
      (R.auxiliaryEntry_house_le_height c hint pivot L S T) rfl
  refine ⟨η, hη, hker, ?_⟩
  simpa [Relation.auxiliaryCoefficientBound] using hbound

/-- The fully discharged construction: the common integral scale and the nonzero auxiliary
coefficient vector are both produced from the reduced relation itself. -/
theorem Relation.exists_scaled_auxiliary_coefficients (R : Relation) (pivot : Fin R.n)
    (L S T : ℕ) (hL : 0 < L) (hS : 0 < S) (hT : 0 < T)
    (hcard : S * T ^ (R.n - 1) < L ^ R.n) :
    ∃ c : ℤ, c ≠ 0 ∧
      ∃ (hint : ∀ i, IsIntegral ℤ (R.scaledCoeff c i))
        (η : R.Column L → 𝓞 R.CoefficientField),
        η ≠ 0 ∧ Matrix.mulVec (R.auxiliaryMatrix c hint pivot L S T) η = 0 ∧
          ∀ m, house ((algebraMap (𝓞 R.CoefficientField) R.CoefficientField) (η m)) ≤
            R.auxiliaryCoefficientBound c hint pivot L S T := by
  obtain ⟨c, hc, hint⟩ := R.exists_common_integer_scale
  have hint' : ∀ i, IsIntegral ℤ (R.scaledCoeff c i) := by
    simpa [Relation.scaledCoeff] using hint
  have hcard' : Fintype.card (R.Row pivot S T) < Fintype.card (R.Column L) := by
    simpa using hcard
  obtain ⟨η, hη, hker, hbound⟩ :=
    R.exists_auxiliary_coefficients c hint' pivot L S T hL hS hT hcard'
  exact ⟨c, hc, hint', η, hη, hker, hbound⟩

end GaloisForLFunctions.RHTower.BakerProof
