import GaloisForLFunctions.RHTower.BakerProof.AuxiliaryComponents

/-!
# Arithmetic values of Baker's shifted components

At every natural-number sample, each shifted component is the chosen complex embedding of an
algebraic integer in the common coefficient field.  This is the arithmetic half of extrapolation:
analytic smallness can later be compared across embeddings with algebraic-integer discreteness.
-/

open scoped Classical
open BigOperators NumberField

namespace GaloisForLFunctions.RHTower.BakerProof

noncomputable def Relation.auxiliaryComponentInteger (R : Relation) (c : ℤ)
    (hint : ∀ i, IsIntegral ℤ (R.scaledCoeff c i)) (pivot : Fin R.n)
    (ν : R.NonPivot pivot → ℕ) {L : ℕ}
    (η : R.Column L → 𝓞 R.CoefficientField) (sample : ℕ) :
    𝓞 R.CoefficientField := by
  let s : Fin (sample + 1) := ⟨sample, Nat.lt_add_one sample⟩
  refine ⟨∑ m, (∏ i : R.NonPivot pivot,
      R.scaledDirection c pivot m i ^ ν i) *
      algebraMap (𝓞 R.CoefficientField) R.CoefficientField (η m) *
      R.sampleFactor s m, ?_⟩
  apply IsIntegral.sum
  intro m hm
  apply IsIntegral.mul
  · apply IsIntegral.mul
    · apply IsIntegral.prod
      intro i hi
      exact (R.scaledDirection_isIntegral c hint pivot m i).pow _
    · exact RingOfIntegers.isIntegral_coe (η m)
  · exact R.sampleFactor_isIntegral s m

/-- A shifted component at a natural sample is exactly the distinguished complex embedding of its
canonical algebraic-integer value. -/
@[simp] theorem Relation.integralCoeffEmbedding_auxiliaryComponentInteger
    (R : Relation) (c : ℤ) (hint : ∀ i, IsIntegral ℤ (R.scaledCoeff c i))
    (pivot : Fin R.n) (ν : R.NonPivot pivot → ℕ) {L : ℕ}
    (η : R.Column L → 𝓞 R.CoefficientField) (sample : ℕ) :
    R.integralCoeffEmbedding
        (R.auxiliaryComponentInteger c hint pivot ν η sample) =
      R.auxiliaryComponent c pivot ν η sample := by
  let s : Fin (sample + 1) := ⟨sample, Nat.lt_add_one sample⟩
  unfold Relation.auxiliaryComponentInteger Relation.auxiliaryComponent
  change R.coeffEmbedding (∑ m, (∏ i : R.NonPivot pivot,
      R.scaledDirection c pivot m i ^ ν i) *
      algebraMap (𝓞 R.CoefficientField) R.CoefficientField (η m) *
      R.sampleFactor s m) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro m hm
  simp only [map_mul, map_prod, map_pow, Relation.integralCoeffEmbedding]
  rw [R.coeffEmbedding_sampleFactor s m, R.exp_frequency_nat s m]
  rfl

/-- An exact finite conjugate bound for a shifted component value. -/
noncomputable def Relation.auxiliaryComponentHouseBound (R : Relation) (c : ℤ)
    (pivot : Fin R.n) (ν : R.NonPivot pivot → ℕ) {L : ℕ}
    (η : R.Column L → 𝓞 R.CoefficientField) (sample : ℕ) : ℝ :=
  let s : Fin (sample + 1) := ⟨sample, Nat.lt_add_one sample⟩
  ∑ m, house ((∏ i : R.NonPivot pivot,
      R.scaledDirection c pivot m i ^ ν i) *
      algebraMap (𝓞 R.CoefficientField) R.CoefficientField (η m) *
      R.sampleFactor s m)

theorem Relation.auxiliaryComponentHouseBound_nonneg (R : Relation) (c : ℤ)
    (pivot : Fin R.n) (ν : R.NonPivot pivot → ℕ) {L : ℕ}
    (η : R.Column L → 𝓞 R.CoefficientField) (sample : ℕ) :
    0 ≤ R.auxiliaryComponentHouseBound c pivot ν η sample := by
  unfold Relation.auxiliaryComponentHouseBound
  apply Finset.sum_nonneg
  intro m hm
  exact house_nonneg _

theorem Relation.auxiliaryComponentInteger_house_le (R : Relation) (c : ℤ)
    (hint : ∀ i, IsIntegral ℤ (R.scaledCoeff c i)) (pivot : Fin R.n)
    (ν : R.NonPivot pivot → ℕ) {L : ℕ}
    (η : R.Column L → 𝓞 R.CoefficientField) (sample : ℕ) :
    house (algebraMap (𝓞 R.CoefficientField) R.CoefficientField
      (R.auxiliaryComponentInteger c hint pivot ν η sample)) ≤
      R.auxiliaryComponentHouseBound c pivot ν η sample := by
  let s : Fin (sample + 1) := ⟨sample, Nat.lt_add_one sample⟩
  change house (∑ m, (∏ i : R.NonPivot pivot,
      R.scaledDirection c pivot m i ^ ν i) *
      algebraMap (𝓞 R.CoefficientField) R.CoefficientField (η m) *
      R.sampleFactor s m) ≤ _
  simpa [Relation.auxiliaryComponentHouseBound, s] using
    house_sum_le_sum_house (Finset.univ : Finset (R.Column L))
      (fun m => (∏ i : R.NonPivot pivot,
        R.scaledDirection c pivot m i ^ ν i) *
        algebraMap (𝓞 R.CoefficientField) R.CoefficientField (η m) *
        R.sampleFactor s m)

/-- **Asymmetric algebraic-integer discreteness.**  One distinguished embedding may be tiny while
the other conjugates are controlled only by the house.  If their norm-product upper bound is below
one, the algebraic integer must vanish. -/
theorem algebraicInteger_eq_zero_of_distinguished_mul_house_pow_lt_one
    {K : Type*} [Field K] [NumberField K] (σ : K →+* ℂ) (x : 𝓞 K)
    (hsmall : ‖σ (algebraMap (𝓞 K) K x)‖ *
      house (algebraMap (𝓞 K) K x) ^ (Module.finrank ℚ K - 1) < 1) :
    x = 0 := by
  by_contra hx
  have hxK : algebraMap (𝓞 K) K x ≠ 0 := by
    simpa only [ne_eq, FaithfulSMul.algebraMap_eq_zero_iff]
  have hnormLower : 1 ≤ ‖Algebra.norm ℚ (algebraMap (𝓞 K) K x)‖ := by
    rw [← Algebra.coe_norm_int, Int.norm_cast_rat]
    rw [← Int.norm_cast_real]
    simp only [Real.norm_eq_abs]
    norm_cast
    exact Int.one_le_abs (Algebra.norm_ne_zero_iff.mpr hx)
  have hnormUpper := norm_norm_le_norm_mul_house_pow
    (algebraMap (𝓞 K) K x) σ
  exact (not_lt_of_ge (hnormLower.trans hnormUpper)) hsmall

/-- The asymmetric norm criterion specialized to a shifted Baker component. -/
theorem Relation.auxiliaryComponent_eq_zero_of_distinguished_mul_house_pow_lt_one
    (R : Relation) (c : ℤ) (hint : ∀ i, IsIntegral ℤ (R.scaledCoeff c i))
    (pivot : Fin R.n) (ν : R.NonPivot pivot → ℕ) {L : ℕ}
    (η : R.Column L → 𝓞 R.CoefficientField) (sample : ℕ)
    (hsmall : ‖R.auxiliaryComponent c pivot ν η sample‖ *
      house (algebraMap (𝓞 R.CoefficientField) R.CoefficientField
        (R.auxiliaryComponentInteger c hint pivot ν η sample)) ^
          (Module.finrank ℚ R.CoefficientField - 1) < 1) :
    R.auxiliaryComponent c pivot ν η sample = 0 := by
  let x := R.auxiliaryComponentInteger c hint pivot ν η sample
  have hsmall' : ‖R.coeffEmbedding (algebraMap (𝓞 R.CoefficientField)
      R.CoefficientField x)‖ *
      house (algebraMap (𝓞 R.CoefficientField) R.CoefficientField x) ^
        (Module.finrank ℚ R.CoefficientField - 1) < 1 := by
    rw [show R.coeffEmbedding (algebraMap (𝓞 R.CoefficientField)
        R.CoefficientField x) = R.integralCoeffEmbedding x by
      rfl]
    rw [show R.integralCoeffEmbedding x = R.auxiliaryComponent c pivot ν η sample by
      exact R.integralCoeffEmbedding_auxiliaryComponentInteger c hint pivot ν η sample]
    exact hsmall
  have hx : x = 0 :=
    algebraicInteger_eq_zero_of_distinguished_mul_house_pow_lt_one
      R.coeffEmbedding x hsmall'
  rw [← R.integralCoeffEmbedding_auxiliaryComponentInteger c hint pivot ν η sample]
  change R.integralCoeffEmbedding x = 0
  rw [hx, map_zero]

/-- Extrapolation-facing discreteness criterion: it is enough to combine a distinguished analytic
bound with the explicit finite conjugate bound `auxiliaryComponentHouseBound`. -/
theorem Relation.auxiliaryComponent_eq_zero_of_norm_mul_houseBound_pow_lt_one
    (R : Relation) (c : ℤ) (hint : ∀ i, IsIntegral ℤ (R.scaledCoeff c i))
    (pivot : Fin R.n) (ν : R.NonPivot pivot → ℕ) {L : ℕ}
    (η : R.Column L → 𝓞 R.CoefficientField) (sample : ℕ)
    (hsmall : ‖R.auxiliaryComponent c pivot ν η sample‖ *
      (R.auxiliaryComponentHouseBound c pivot ν η sample) ^
        (Module.finrank ℚ R.CoefficientField - 1) < 1) :
    R.auxiliaryComponent c pivot ν η sample = 0 := by
  apply R.auxiliaryComponent_eq_zero_of_distinguished_mul_house_pow_lt_one
    c hint pivot ν η sample
  apply lt_of_le_of_lt _ hsmall
  gcongr
  · exact house_nonneg _
  exact R.auxiliaryComponentInteger_house_le c hint pivot ν η sample

end GaloisForLFunctions.RHTower.BakerProof
