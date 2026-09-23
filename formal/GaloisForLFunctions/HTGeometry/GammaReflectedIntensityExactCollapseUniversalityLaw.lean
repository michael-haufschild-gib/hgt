import GaloisForLFunctions.HTGeometry.GammaReflectedFrequencyObservability
import GaloisForLFunctions.HTGeometry.ScalarLogCurrentReconstruction
import GaloisForLFunctions.HTGeometry.UnivMeroFieldInstances

/-!
# Exact collapse locus of reflected Gamma intensity

For the opposite-orientation Gamma clock, reflected intensity is a quotient of two thermal
reflection products.  The corpus previously recorded integer separation as one sufficient
collapse mechanism.  The complete orbit analysis has a second component: both weights may lie on
their individual thermal half-lattices even when their difference is not integral.

This module proves that these are the only two mechanisms.  Outside their union, either one
thermal reflection product is HT against a DA one, one of the four signed Gamma charges is exposed,
or the two surviving orbit charges form the square of a nonintegral Veneziano ratio.
-/

open Filter Set Topology Function Complex
open scoped BigOperators Differential

namespace GaloisForLFunctions

open Bottcher Polynomial

noncomputable section

open scoped UnivMeroFieldInstances

private theorem gammaReflectionProductMero_ne_zero_exact (h : ℂ) :
    gammaReflectionProductMero h ≠ 0 := by
  exact mul_ne_zero (gammaShiftMero_ne_zero h)
    (by
      rw [gammaNegativeShiftMero_reflection]
      exact mul_ne_zero (gammaReflectionGaugeMero_ne_zero h)
        (inv_ne_zero (gammaShiftMero_ne_zero (1 - h))))

/-- Every reflected opposite-shift intensity is nonzero. -/
theorem gammaOppositeShiftIntensityMero_ne_zero (a b : ℂ) :
    gammaOppositeShiftIntensityMero a b ≠ 0 := by
  rw [gammaOppositeShiftIntensityMero_eq_reflectionProduct_div]
  exact div_ne_zero (gammaReflectionProductMero_ne_zero_exact a)
    (gammaReflectionProductMero_ne_zero_exact b)

/-- Reflected intensity is a multiplicative pair-groupoid cocycle in its two weights. -/
theorem gammaOppositeShiftIntensityMero_cocycle (a b c : ℂ) :
    gammaOppositeShiftIntensityMero a c =
      gammaOppositeShiftIntensityMero a b *
        gammaOppositeShiftIntensityMero b c := by
  simp_rw [gammaOppositeShiftIntensityMero_eq_reflectionProduct_div]
  field_simp [gammaReflectionProductMero_ne_zero_exact]

/-- Integer separation in either direction makes reflected intensity DA. -/
theorem differentialAlgebraicOver_gammaOppositeShiftIntensityMero_of_integerDifference
    (a b : ℂ) (hDifference : ∃ k : ℤ, b - a = (k : ℂ)) :
    DifferentialAlgebraicOver (RatFunc ℂ)
      (gammaOppositeShiftIntensityMero a b) := by
  obtain ⟨k, hk⟩ := hDifference
  cases k with
  | ofNat n =>
      have hb : b = a + (n : ℂ) := by
        norm_num at hk
        linear_combination hk
      rw [hb, gammaOppositeShiftIntensityMero_eq_integerShiftGauge]
      exact differentialAlgebraicOver_gammaReflectionIntegerShiftGaugeMero a n
  | negSucc n =>
      have ha : a = b + ((n + 1 : ℕ) : ℂ) := by
        rw [Int.cast_negSucc] at hk
        push_cast at hk ⊢
        linear_combination -hk
      rw [gammaOppositeShiftIntensityMero_eq_reflectionProduct_div, ha]
      have hDA : DifferentialAlgebraicOver (RatFunc ℂ)
          (gammaReflectionIntegerShiftGaugeMero b (n + 1))⁻¹ :=
        HTGeometry.differentialAlgebraicOver_inv
          (differentialAlgebraicOver_gammaReflectionIntegerShiftGaugeMero b (n + 1))
      rw [← gammaReflectionProductMero_div_add_nat] at hDA
      convert hDA using 1
      field_simp [gammaReflectionProductMero_ne_zero_exact]

/-- The second collapse mechanism: both thermal weights are individually exceptional. -/
theorem differentialAlgebraicOver_gammaOppositeShiftIntensityMero_of_integerWeights
    (a b : ℂ) (ha : ∃ k : ℤ, 1 - 2 * a = (k : ℂ))
    (hb : ∃ k : ℤ, 1 - 2 * b = (k : ℂ)) :
    DifferentialAlgebraicOver (RatFunc ℂ)
      (gammaOppositeShiftIntensityMero a b) := by
  rw [gammaOppositeShiftIntensityMero_eq_reflectionProduct_div]
  exact HTGeometry.differentialAlgebraicOver_div
    ((differentialAlgebraicOver_gammaReflectionProductMero_iff_integerWeight a).2 ha)
    ((differentialAlgebraicOver_gammaReflectionProductMero_iff_integerWeight b).2 hb)

/-- The four signed positive-orientation Gamma factors left after Euler reflection. -/
def gammaOppositeShiftIntensityOrbitProductMero (a b : ℂ) :
    meroField Set.univ :=
  gammaFintypeOrbitProductMero
    ![a, 1 - b, 1 - a, b]
    ![(1 : ℤ), 1, -1, -1]

/-- Nonzero DA gauge in the reflected-intensity orbit normal form. -/
def gammaOppositeShiftIntensityReflectionGaugeMero (a b : ℂ) :
    meroField Set.univ :=
  gammaReflectionGaugeMero a / gammaReflectionGaugeMero b

theorem gammaOppositeShiftIntensityReflectionGaugeMero_ne_zero (a b : ℂ) :
    gammaOppositeShiftIntensityReflectionGaugeMero a b ≠ 0 := by
  exact div_ne_zero (gammaReflectionGaugeMero_ne_zero a)
    (gammaReflectionGaugeMero_ne_zero b)

theorem differentialAlgebraicOver_gammaOppositeShiftIntensityReflectionGaugeMero
    (a b : ℂ) :
    DifferentialAlgebraicOver (RatFunc ℂ)
      (gammaOppositeShiftIntensityReflectionGaugeMero a b) := by
  exact HTGeometry.differentialAlgebraicOver_div
    (differentialAlgebraicOver_gammaReflectionGaugeMero a)
    (differentialAlgebraicOver_gammaReflectionGaugeMero b)

/-- Euler reflection displays intensity as a DA gauge times four signed Gamma-orbit charges. -/
theorem gammaOppositeShiftIntensityMero_reflectionOrbitNormalForm (a b : ℂ) :
    gammaOppositeShiftIntensityMero a b =
      gammaOppositeShiftIntensityReflectionGaugeMero a b *
        gammaOppositeShiftIntensityOrbitProductMero a b := by
  rw [gammaOppositeShiftIntensityMero_eq_reflectionProduct_div]
  unfold gammaReflectionProductMero
  rw [gammaNegativeShiftMero_reflection, gammaNegativeShiftMero_reflection]
  unfold gammaOppositeShiftIntensityReflectionGaugeMero
    gammaOppositeShiftIntensityOrbitProductMero gammaFintypeOrbitProductMero
  simp [Fin.prod_univ_four]
  field_simp [gammaReflectionGaugeMero_ne_zero, gammaShiftMero_ne_zero]

private theorem hypertranscendentalOver_gammaOppositeShiftIntensityMero_of_leftWeightOnly
    (a b : ℂ) (ha : ∃ k : ℤ, 1 - 2 * a = (k : ℂ))
    (hb : ∀ k : ℤ, 1 - 2 * b ≠ (k : ℂ)) :
    HypertranscendentalOver (RatFunc ℂ)
      (gammaOppositeShiftIntensityMero a b) := by
  rw [gammaOppositeShiftIntensityMero_eq_reflectionProduct_div, div_eq_mul_inv, mul_comm]
  exact (HTGeometry.hypertranscendentalOver_mul_differentialAlgebraic_iff
    ((differentialAlgebraicOver_gammaReflectionProductMero_iff_integerWeight a).2 ha)
    (gammaReflectionProductMero_ne_zero_exact a)).2
      ((HTGeometry.hypertranscendentalOver_inv_iff).2
        ((hypertranscendentalOver_gammaReflectionProductMero_iff_nonintegerWeight b).2 hb))

private theorem hypertranscendentalOver_gammaOppositeShiftIntensityMero_of_rightWeightOnly
    (a b : ℂ) (ha : ∀ k : ℤ, 1 - 2 * a ≠ (k : ℂ))
    (hb : ∃ k : ℤ, 1 - 2 * b = (k : ℂ)) :
    HypertranscendentalOver (RatFunc ℂ)
      (gammaOppositeShiftIntensityMero a b) := by
  rw [gammaOppositeShiftIntensityMero_eq_reflectionProduct_div]
  exact (HTGeometry.hypertranscendentalOver_div_differentialAlgebraic_iff
    ((differentialAlgebraicOver_gammaReflectionProductMero_iff_integerWeight b).2 hb)
    (gammaReflectionProductMero_ne_zero_exact b)).2
      ((hypertranscendentalOver_gammaReflectionProductMero_iff_nonintegerWeight a).2 ha)

private theorem hypertranscendentalOver_gammaOppositeShiftIntensityOrbitProductMero_of_exposed
    (a b : ℂ)
    (hDifference : ∀ k : ℤ, b - a ≠ (k : ℂ))
    (ha : ∀ k : ℤ, 1 - 2 * a ≠ (k : ℂ))
    (hSum : ∀ k : ℤ, a + b ≠ (k : ℂ)) :
    HypertranscendentalOver (RatFunc ℂ)
      (gammaOppositeShiftIntensityOrbitProductMero a b) := by
  let shifts : Fin 4 → ℂ := ![a, 1 - b, 1 - a, b]
  let charges : Fin 4 → ℤ := ![(1 : ℤ), 1, -1, -1]
  have hproduct : HypertranscendentalOver (RatFunc ℂ)
      (gammaFintypeOrbitProductMero shifts charges) := by
    apply hypertranscendentalOver_gammaFintypeOrbitProductMero shifts charges 0
    · norm_num [charges]
    · intro i hi q
      fin_cases i
      · exact (hi rfl).elim
      · intro hq
        change 1 - b - a = (q : ℂ) at hq
        apply hSum (1 - q)
        calc
          a + b = 1 - (1 - b - a) := by ring
          _ = 1 - (q : ℂ) := by rw [hq]
          _ = ((1 - q : ℤ) : ℂ) := by push_cast; ring
      · intro hq
        apply ha q
        change 1 - a - a = (q : ℂ) at hq
        linear_combination hq
      · simpa [shifts] using hDifference q
  simpa [gammaOppositeShiftIntensityOrbitProductMero, shifts, charges] using hproduct

private theorem hypertranscendentalOver_gammaOppositeShiftIntensityMero_of_exposed
    (a b : ℂ)
    (hDifference : ∀ k : ℤ, b - a ≠ (k : ℂ))
    (ha : ∀ k : ℤ, 1 - 2 * a ≠ (k : ℂ))
    (hSum : ∀ k : ℤ, a + b ≠ (k : ℂ)) :
    HypertranscendentalOver (RatFunc ℂ)
      (gammaOppositeShiftIntensityMero a b) := by
  rw [gammaOppositeShiftIntensityMero_reflectionOrbitNormalForm, mul_comm]
  exact (HTGeometry.hypertranscendentalOver_mul_differentialAlgebraic_iff
    (differentialAlgebraicOver_gammaOppositeShiftIntensityReflectionGaugeMero a b)
    (gammaOppositeShiftIntensityReflectionGaugeMero_ne_zero a b)).2
      (hypertranscendentalOver_gammaOppositeShiftIntensityOrbitProductMero_of_exposed
        a b hDifference ha hSum)

/-- On the reflected diagonal `b=1-a`, the surviving nonneutral orbit is exactly a square. -/
theorem gammaOppositeShiftIntensityMero_one_sub_reflectionNormalForm (a : ℂ) :
    gammaOppositeShiftIntensityMero a (1 - a) =
      gammaOppositeShiftIntensityReflectionGaugeMero a (1 - a) *
        reducedVenezianoAmplitudeMero a (1 - 2 * a) ^ (2 : ℕ) := by
  rw [gammaOppositeShiftIntensityMero_reflectionOrbitNormalForm]
  unfold gammaOppositeShiftIntensityOrbitProductMero gammaFintypeOrbitProductMero
    reducedVenezianoAmplitudeMero
  simp [Fin.prod_univ_four]
  have harg : a + (1 - 2 * a) = 1 - a := by ring
  rw [harg]
  ring_nf ; simp

private theorem hypertranscendentalOver_gammaOppositeShiftIntensityMero_one_sub
    (a : ℂ) (ha : ∀ k : ℤ, 1 - 2 * a ≠ (k : ℂ)) :
    HypertranscendentalOver (RatFunc ℂ)
      (gammaOppositeShiftIntensityMero a (1 - a)) := by
  rw [gammaOppositeShiftIntensityMero_one_sub_reflectionNormalForm, mul_comm]
  apply (HTGeometry.hypertranscendentalOver_mul_differentialAlgebraic_iff
    (differentialAlgebraicOver_gammaOppositeShiftIntensityReflectionGaugeMero a (1 - a))
    (gammaOppositeShiftIntensityReflectionGaugeMero_ne_zero a (1 - a))).2
  exact HTGeometry.hypertranscendentalOver_pow_of_pos (N := 2)
    ((hypertranscendentalOver_reducedVenezianoAmplitudeMero_iff_nonintegerShift
      a (1 - 2 * a)).2 ha) (by norm_num)

private theorem hypertranscendentalOver_gammaOppositeShiftIntensityMero_of_integerSum
    (a b : ℂ) (ha : ∀ k : ℤ, 1 - 2 * a ≠ (k : ℂ))
    (hSum : ∃ k : ℤ, a + b = (k : ℂ)) :
    HypertranscendentalOver (RatFunc ℂ)
      (gammaOppositeShiftIntensityMero a b) := by
  obtain ⟨k, hk⟩ := hSum
  have hDifference : ∃ q : ℤ, b - (1 - a) = (q : ℂ) := by
    refine ⟨k - 1, ?_⟩
    calc
      b - (1 - a) = a + b - 1 := by ring
      _ = (k : ℂ) - 1 := by rw [hk]
      _ = ((k - 1 : ℤ) : ℂ) := by push_cast; ring
  have hDA : DifferentialAlgebraicOver (RatFunc ℂ)
      (gammaOppositeShiftIntensityMero (1 - a) b) :=
    differentialAlgebraicOver_gammaOppositeShiftIntensityMero_of_integerDifference
      (1 - a) b hDifference
  rw [gammaOppositeShiftIntensityMero_cocycle a (1 - a) b]
  exact (HTGeometry.hypertranscendentalOver_mul_differentialAlgebraic_iff
    hDA (gammaOppositeShiftIntensityMero_ne_zero (1 - a) b)).2
      (hypertranscendentalOver_gammaOppositeShiftIntensityMero_one_sub a ha)

/-- **Exact reflected-intensity collapse locus.**  Differential-algebraic collapse occurs exactly
on the union of the relative integer-shift diagonal and the product of the two absolute thermal
half-lattices. -/
theorem differentialAlgebraicOver_gammaOppositeShiftIntensityMero_iff_exactCollapse
    (a b : ℂ) :
    DifferentialAlgebraicOver (RatFunc ℂ)
        (gammaOppositeShiftIntensityMero a b) ↔
      (∃ k : ℤ, b - a = (k : ℂ)) ∨
        ((∃ k : ℤ, 1 - 2 * a = (k : ℂ)) ∧
          ∃ k : ℤ, 1 - 2 * b = (k : ℂ)) := by
  constructor
  · intro hDA
    by_cases hDifference : ∃ k : ℤ, b - a = (k : ℂ)
    · exact Or.inl hDifference
    · right
      by_cases ha : ∃ k : ℤ, 1 - 2 * a = (k : ℂ)
      · by_cases hb : ∃ k : ℤ, 1 - 2 * b = (k : ℂ)
        · exact ⟨ha, hb⟩
        · push Not at hb
          exact (hypertranscendentalOver_gammaOppositeShiftIntensityMero_of_leftWeightOnly
            a b ha hb hDA).elim
      · push Not at ha
        by_cases hb : ∃ k : ℤ, 1 - 2 * b = (k : ℂ)
        · exact (hypertranscendentalOver_gammaOppositeShiftIntensityMero_of_rightWeightOnly
            a b ha hb hDA).elim
        · push Not at hb
          by_cases hSum : ∃ k : ℤ, a + b = (k : ℂ)
          · exact (hypertranscendentalOver_gammaOppositeShiftIntensityMero_of_integerSum
              a b ha hSum hDA).elim
          · push Not at hDifference hSum
            exact (hypertranscendentalOver_gammaOppositeShiftIntensityMero_of_exposed
              a b hDifference ha hSum hDA).elim
  · rintro (hDifference | ⟨ha, hb⟩)
    · exact differentialAlgebraicOver_gammaOppositeShiftIntensityMero_of_integerDifference
        a b hDifference
    · exact differentialAlgebraicOver_gammaOppositeShiftIntensityMero_of_integerWeights
        a b ha hb

/-- Complementary HT classification of reflected opposite-shift intensity. -/
theorem hypertranscendentalOver_gammaOppositeShiftIntensityMero_iff_exactNoncollapse
    (a b : ℂ) :
    HypertranscendentalOver (RatFunc ℂ)
        (gammaOppositeShiftIntensityMero a b) ↔
      (∀ k : ℤ, b - a ≠ (k : ℂ)) ∧
        ((∀ k : ℤ, 1 - 2 * a ≠ (k : ℂ)) ∨
          ∀ k : ℤ, 1 - 2 * b ≠ (k : ℂ)) := by
  rw [HypertranscendentalOver,
    differentialAlgebraicOver_gammaOppositeShiftIntensityMero_iff_exactCollapse]
  push Not
  constructor
  · rintro ⟨hDifference, hWeights⟩
    refine ⟨hDifference, ?_⟩
    by_cases ha : ∃ k : ℤ, 1 - 2 * a = (k : ℂ)
    · exact Or.inr (hWeights ha)
    · left
      push Not at ha
      exact ha
  · rintro ⟨hDifference, ha | hb⟩
    · refine ⟨hDifference, ?_⟩
      rintro ⟨k, hk⟩
      exact (ha k hk).elim
    · exact ⟨hDifference, fun _ => hb⟩

end

end GaloisForLFunctions
