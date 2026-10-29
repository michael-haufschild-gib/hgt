import GaloisForLFunctions.HTGeometry.NumberFieldUnitLogFundamentalDomain
import GaloisForLFunctions.HTGeometry.NumberFieldArchimedeanBalancedMean
import GaloisForLFunctions.HTGeometry.NumberFieldArchimedeanCanonicalDeterminant
import GaloisForLFunctions.HTGeometry.BorisovGabberVasiuDeterminant
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# The exact radial and unit-logarithmic Jacobian

Independent place logarithms are `q - P(l)`, where `P` completes weighted
unit-logarithmic coordinates to a profile of weighted mean zero. The inverse
recovers `q` by weighted averaging. Its matrix is diagonal plus rank one,
giving absolute determinant `[K:ℚ] / 2^r₂` for the forward map.

Splitting the distinguished coordinate preserves product Lebesgue measure.
Consequently nonnegative and complex integrals acquire the exact density
`2^r₂ / [K:ℚ]`; absolute integrability is preserved in both directions.
-/

noncomputable section
open NumberField NumberField.InfinitePlace NumberField.Units.dirichletUnitTheorem
open MeasureTheory Set Matrix
open scoped Classical ENNReal
namespace GaloisForLFunctions.HTGeometry
variable {K : Type*} [Field K] [NumberField K]

/-- Completing the retained coordinates recovers every weighted-zero profile. -/
theorem numberFieldWeightedLogProfile_complete (f : InfinitePlace K → ℝ)
    (hf : ∑ v, (mult v : ℝ) * f v = 0) :
    numberFieldWeightedLogProfile (fun v => (mult v.1 : ℝ) * f v.1) = f := by
  funext v
  by_cases hv : v = w₀
  · subst v
    rw [numberFieldWeightedLogProfile_apply_eq]
    rw [Fintype.sum_eq_add_sum_subtype_ne _ w₀] at hf
    apply (div_eq_iff mult_coe_ne_zero).2
    linarith only [hf]
  · rw [numberFieldWeightedLogProfile_apply_ne _ ⟨v, hv⟩]
    exact mul_div_cancel_left₀ _ mult_coe_ne_zero

/-- The completed logarithmic profile has weighted mean zero. -/
theorem numberFieldWeightedPlaceMean_weightedLogProfile (x : logSpace K) :
    numberFieldWeightedPlaceMean (numberFieldWeightedLogProfile x) = 0 := by
  rw [numberFieldWeightedPlaceMean, sum_mult_numberFieldWeightedLogProfile, zero_div]

private def radialLogMap : (InfinitePlace K → ℝ) →ₗ[ℝ] (InfinitePlace K → ℝ) :=
  (LinearMap.pi fun _ : InfinitePlace K =>
    (LinearMap.proj (w₀ : InfinitePlace K) : (InfinitePlace K → ℝ) →ₗ[ℝ] ℝ)) -
    (numberFieldWeightedLogProfile (K := K)).comp
      (LinearMap.pi fun v : {v : InfinitePlace K // v ≠ w₀} =>
        (LinearMap.proj v.1 : (InfinitePlace K → ℝ) →ₗ[ℝ] ℝ))

private def radialLogInverse (z : InfinitePlace K → ℝ) (v : InfinitePlace K) : ℝ :=
  if v = w₀ then numberFieldWeightedPlaceMean z
  else (mult v : ℝ) * (numberFieldWeightedPlaceMean z - z v)

private theorem radialLogInverse_left (x : InfinitePlace K → ℝ) :
    radialLogInverse (radialLogMap x) = x := by
  change (fun v => if v = w₀ then numberFieldWeightedPlaceMean
      (fun v => x w₀ - numberFieldWeightedLogProfile (fun w => x w.1) v)
    else (mult v : ℝ) * (numberFieldWeightedPlaceMean
      (fun v => x w₀ - numberFieldWeightedLogProfile (fun w => x w.1) v) -
      (x w₀ - numberFieldWeightedLogProfile (fun w => x w.1) v))) = x
  have hm : numberFieldWeightedPlaceMean
      (fun v => x w₀ - numberFieldWeightedLogProfile (fun w => x w.1) v) = x w₀ := by
    rw [numberFieldWeightedPlaceMean_sub, numberFieldWeightedPlaceMean_const,
      numberFieldWeightedPlaceMean_weightedLogProfile, sub_zero]
  funext v
  by_cases hv : v = w₀
  · simp only [hv, ite_true, hm]
  · simp only [hv, ite_false, hm, sub_sub_cancel]
    rw [numberFieldWeightedLogProfile_apply_ne _ ⟨v, hv⟩]
    exact mul_div_cancel₀ _ mult_coe_ne_zero

private theorem radialLogInverse_right (z : InfinitePlace K → ℝ) :
    radialLogMap (radialLogInverse z) = z := by
  change (fun v => (if w₀ = w₀ then numberFieldWeightedPlaceMean z
      else (mult (w₀ : InfinitePlace K) : ℝ) * (numberFieldWeightedPlaceMean z - z w₀)) -
    numberFieldWeightedLogProfile (fun w => if w.1 = w₀ then numberFieldWeightedPlaceMean z
      else (mult w.1 : ℝ) * (numberFieldWeightedPlaceMean z - z w.1)) v) = z
  have hz : ∑ v, (mult v : ℝ) * (numberFieldWeightedPlaceMean z - z v) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
      numberFieldWeightedPlaceMean, numberFieldInfinitePlaceWeight]
    exact sub_eq_zero.mpr (mul_div_cancel₀ _
      (ne_of_gt (numberFieldInfinitePlaceWeight_pos (K := K))))
  have hp := numberFieldWeightedLogProfile_complete _ hz
  funext v
  simp only [ite_true]
  have hret : (fun w : {w : InfinitePlace K // w ≠ w₀} =>
      if w.1 = w₀ then numberFieldWeightedPlaceMean z
      else (mult w.1 : ℝ) * (numberFieldWeightedPlaceMean z - z w.1)) =
      (fun w => (mult w.1 : ℝ) * (numberFieldWeightedPlaceMean z - z w.1)) := by
    funext w
    exact if_neg w.2
  rw [hret, hp]
  exact sub_sub_cancel _ _

/-- The radial logarithm and weighted unit coordinates parametrize independent place logarithms. -/
def numberFieldRadialLogEquiv :
    (InfinitePlace K → ℝ) ≃ₗ[ℝ] (InfinitePlace K → ℝ) where
  toLinearMap := radialLogMap
  invFun := radialLogInverse
  left_inv := radialLogInverse_left
  right_inv := radialLogInverse_right

/-- The distinguished input coordinate is the radial logarithm. -/
theorem numberFieldRadialLogEquiv_apply (x : InfinitePlace K → ℝ) (v : InfinitePlace K) :
    numberFieldRadialLogEquiv x v =
      x w₀ - numberFieldWeightedLogProfile (fun w => x w.1) v := rfl

/-- Weighted averaging recovers the radial logarithm; weighted differences recover the other coordinates. -/
theorem numberFieldRadialLogEquiv_symm_apply (z : InfinitePlace K → ℝ) (v : InfinitePlace K) :
    numberFieldRadialLogEquiv.symm z v =
      if v = w₀ then numberFieldWeightedPlaceMean z
      else (mult v : ℝ) * (numberFieldWeightedPlaceMean z - z v) := rfl

private theorem weightedPlaceMean_single (w : InfinitePlace K) :
    numberFieldWeightedPlaceMean (Pi.single w 1) =
      (mult w : ℝ) / numberFieldInfinitePlaceWeight (K := K) := by
  simp [numberFieldWeightedPlaceMean, Pi.single_apply, mul_ite]

private theorem radialLogInverse_toMatrix :
    LinearMap.toMatrix' ((numberFieldRadialLogEquiv (K := K)).symm :
      (InfinitePlace K → ℝ) →ₗ[ℝ] (InfinitePlace K → ℝ)) =
      Matrix.diagonal (fun v => if v = w₀ then 0 else -(mult v : ℝ)) +
        vecMulVec (fun v => if v = w₀ then 1 / numberFieldInfinitePlaceWeight (K := K)
          else (mult v : ℝ) / numberFieldInfinitePlaceWeight (K := K))
          (fun v => (mult v : ℝ)) := by
  ext v w
  rw [LinearMap.toMatrix'_apply]
  simp only [LinearEquiv.coe_coe, numberFieldRadialLogEquiv_symm_apply,
    weightedPlaceMean_single, Matrix.add_apply, Matrix.diagonal_apply, Matrix.vecMulVec_apply]
  by_cases hv : v = w₀
  · simp only [hv, ite_true, ite_self, zero_add]
    ring
  · by_cases hvw : v = w
    · subst w
      simp only [hv, ite_false, ite_true, Pi.single_eq_same]
      ring
    · simp only [hv, hvw, ite_false, Pi.single_eq_of_ne hvw, zero_add, sub_zero]
      ring

private theorem det_radialLogInverse :
    LinearMap.det ((numberFieldRadialLogEquiv (K := K)).symm :
      (InfinitePlace K → ℝ) →ₗ[ℝ] (InfinitePlace K → ℝ)) =
      ((mult (w₀ : InfinitePlace K) : ℝ) / numberFieldInfinitePlaceWeight (K := K)) *
        ∏ v ∈ Finset.univ.erase (w₀ : InfinitePlace K), -(mult v : ℝ) := by
  rw [← LinearMap.det_toMatrix', radialLogInverse_toMatrix,
    bgv_det_diagonal_add_vecMulVec]
  have hz : (∏ v : InfinitePlace K, if v = w₀ then (0 : ℝ) else -(mult v : ℝ)) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ (w₀ : InfinitePlace K)) (if_pos rfl)
  rw [hz, zero_add, Finset.sum_eq_single (w₀ : InfinitePlace K)]
  · simp only [ite_true]
    rw [one_div_mul_eq_div]
    congr 1
    apply Finset.prod_congr rfl
    intro v hv
    exact if_neg (Finset.mem_erase.mp hv).1
  · intro v _ hv
    have hz' : (∏ j ∈ Finset.univ.erase v,
        if j = w₀ then (0 : ℝ) else -(mult j : ℝ)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hv, Finset.mem_univ _⟩) (if_pos rfl)
    rw [hz', mul_zero]
  · intro h
    exact (h (Finset.mem_univ _)).elim

/-- The inverse radial/logarithmic map has exact absolute determinant `∏ mult / Σ mult`. -/
theorem abs_det_numberFieldRadialLogEquiv_symm :
    |LinearMap.det ((numberFieldRadialLogEquiv (K := K)).symm :
      (InfinitePlace K → ℝ) →ₗ[ℝ] (InfinitePlace K → ℝ))| =
      (∏ v : InfinitePlace K, (mult v : ℝ)) / numberFieldInfinitePlaceWeight (K := K) := by
  rw [det_radialLogInverse, abs_mul, abs_div,
    abs_of_pos (Nat.cast_pos.mpr mult_pos),
    abs_of_pos numberFieldInfinitePlaceWeight_pos, Finset.abs_prod]
  simp_rw [abs_neg, abs_of_nonneg (Nat.cast_nonneg _ : (0 : ℝ) ≤ _)]
  rw [div_mul_eq_mul_div, mul_comm, Finset.prod_erase_mul _ _ (Finset.mem_univ _)]

/-- Place multiplicities multiply to one factor two for each complex place. -/
theorem prod_numberFieldInfinitePlace_mult :
    (∏ v : InfinitePlace K, (mult v : ℝ)) = 2 ^ nrComplexPlaces K := by
  rw [prod_eq_prod_mul_prod]
  simp only [mult_isReal, mult_isComplex, Nat.cast_one, Nat.cast_ofNat,
    Finset.prod_const_one, Finset.prod_const, Finset.card_univ, one_mul]

/-- Exact Jacobian of the radial/logarithmic parametrization. -/
theorem abs_det_numberFieldRadialLogEquiv :
    |LinearMap.det (numberFieldRadialLogEquiv (K := K) :
      (InfinitePlace K → ℝ) →ₗ[ℝ] (InfinitePlace K → ℝ))| =
      (Module.finrank ℚ K : ℝ) / 2 ^ nrComplexPlaces K := by
  have h := abs_det_numberFieldRadialLogEquiv_symm (K := K)
  rw [LinearEquiv.det_coe_symm, abs_inv, prod_numberFieldInfinitePlace_mult,
    numberFieldInfinitePlaceWeight_eq_finrank] at h
  apply inv_injective
  simpa only [inv_div] using h

/-- Pushforward of Lebesgue measure under the actual radial/logarithmic map. -/
theorem map_numberFieldRadialLogEquiv_volume :
    Measure.map (numberFieldRadialLogEquiv (K := K)) volume =
      ENNReal.ofReal ((2 : ℝ) ^ nrComplexPlaces K / Module.finrank ℚ K) • volume := by
  have h := Measure.map_linearMap_addHaar_eq_smul_addHaar
    (volume : Measure (InfinitePlace K → ℝ))
    (numberFieldRadialLogEquiv (K := K)).isUnit_det'.ne_zero
  simpa only [LinearEquiv.coe_coe, abs_inv, abs_det_numberFieldRadialLogEquiv, inv_div] using h

/-- Separate the distinguished place coordinate from the weighted unit-log coordinates. -/
def numberFieldRadialLogSplit : (InfinitePlace K → ℝ) ≃ᵐ (ℝ × logSpace K) :=
  (Homeomorph.funSplitAt ℝ (w₀ : InfinitePlace K)).toMeasurableEquiv

/-- Separating one place coordinate preserves the product Lebesgue measure. -/
theorem measurePreserving_numberFieldRadialLogSplit :
    MeasurePreserving (numberFieldRadialLogSplit (K := K)) volume volume := by
  letI : Fintype {v : InfinitePlace K // v = w₀} := Subtype.fintype (fun v => v = w₀)
  letI : Unique {v : InfinitePlace K // v = w₀} :=
    { default := ⟨w₀, rfl⟩, uniq := fun v => Subtype.ext v.2 }
  have hs : MeasurePreserving
      (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : InfinitePlace K => ℝ) (fun v => v = w₀))
      (volume : Measure (InfinitePlace K → ℝ))
      ((volume : Measure ({v : InfinitePlace K // v = w₀} → ℝ)).prod
        (volume : Measure (logSpace K))) := by
    simpa only [volume_pi] using
      (measurePreserving_piEquivPiSubtypeProd (fun _ : InfinitePlace K => (volume : Measure ℝ))
        (fun v => v = w₀))
  have hv := congrArg (fun inst : Fintype {v : InfinitePlace K // v = w₀} =>
    @Measure.pi {v : InfinitePlace K // v = w₀} (fun _ => ℝ) inst
      (fun _ => Real.measurableSpace) (fun _ => (volume : Measure ℝ)))
    (Subsingleton.elim (Unique.fintype : Fintype {v : InfinitePlace K // v = w₀})
      (Subtype.fintype (fun v : InfinitePlace K => v = w₀)))
  have hu := measurePreserving_funUnique (volume : Measure ℝ) {v : InfinitePlace K // v = w₀}
  rw [hv] at hu
  exact (hu.prod (MeasurePreserving.id (volume : Measure (logSpace K)))).comp hs

/-- Independent logarithms expressed in radial and unit-log coordinates. -/
def numberFieldRadialLogParam (p : ℝ × logSpace K) (v : InfinitePlace K) : ℝ :=
  p.1 - numberFieldWeightedLogProfile p.2 v

private theorem radialLogParam_eq_comp :
    numberFieldRadialLogParam (K := K) =
      (numberFieldRadialLogEquiv (K := K)) ∘ (numberFieldRadialLogSplit (K := K)).symm := by
  funext p v
  have hq : (numberFieldRadialLogSplit (K := K)).symm p w₀ = p.1 :=
    congrArg (fun z : ℝ × logSpace K => z.1)
      ((numberFieldRadialLogSplit (K := K)).apply_symm_apply p)
  have hl : (fun w : {w : InfinitePlace K // w ≠ w₀} =>
      (numberFieldRadialLogSplit (K := K)).symm p w.1) = p.2 :=
    congrArg (fun z : ℝ × logSpace K => z.2)
      ((numberFieldRadialLogSplit (K := K)).apply_symm_apply p)
  rw [Function.comp_apply, numberFieldRadialLogEquiv_apply, hq, hl]
  rfl

/-- The radial/unit-log product measure has exact density `2^r₂/[K:ℚ]` in place logarithms. -/
theorem map_numberFieldRadialLogParam_volume :
    Measure.map (numberFieldRadialLogParam (K := K)) volume =
      ENNReal.ofReal ((2 : ℝ) ^ nrComplexPlaces K / Module.finrank ℚ K) • volume := by
  have hc : Continuous (numberFieldRadialLogEquiv (K := K) :
      (InfinitePlace K → ℝ) → (InfinitePlace K → ℝ)) :=
    (numberFieldRadialLogEquiv (K := K)).continuous_of_finiteDimensional
  rw [radialLogParam_eq_comp, ← Measure.map_map hc.measurable
    (numberFieldRadialLogSplit (K := K)).symm.measurable,
    (measurePreserving_numberFieldRadialLogSplit (K := K)).symm.map_eq,
    map_numberFieldRadialLogEquiv_volume]

/-- The radial/unit-log parametrization is a measurable embedding. -/
theorem measurableEmbedding_numberFieldRadialLogParam :
    MeasurableEmbedding (numberFieldRadialLogParam (K := K)) := by
  rw [radialLogParam_eq_comp]
  have he : MeasurableEmbedding (numberFieldRadialLogEquiv (K := K) :
      (InfinitePlace K → ℝ) → (InfinitePlace K → ℝ)) :=
    (numberFieldRadialLogEquiv (K := K)).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv.measurableEmbedding
  exact he.comp (numberFieldRadialLogSplit (K := K)).symm.measurableEmbedding

private theorem radialLogDensity_pos :
    0 < (2 : ℝ) ^ nrComplexPlaces K / Module.finrank ℚ K := by
  have hn : 0 < (Module.finrank ℚ K : ℝ) := by
    rw [← numberFieldInfinitePlaceWeight_eq_finrank]
    exact numberFieldInfinitePlaceWeight_pos
  exact div_pos (pow_pos zero_lt_two _) hn

/-- Nonnegative integration in radial/unit-log coordinates has the exact arithmetic Jacobian. -/
theorem lintegral_numberFieldRadialLogParam (f : (InfinitePlace K → ℝ) → ℝ≥0∞) :
    (∫⁻ p : ℝ × logSpace K, f (numberFieldRadialLogParam p)) =
      ENNReal.ofReal ((2 : ℝ) ^ nrComplexPlaces K / Module.finrank ℚ K) * ∫⁻ z, f z := by
  rw [← measurableEmbedding_numberFieldRadialLogParam.lintegral_map,
    map_numberFieldRadialLogParam_volume, lintegral_smul_measure, smul_eq_mul]

/-- Absolute integrability is preserved by the radial/unit-log parametrization. -/
theorem integrable_numberFieldRadialLogParam_iff (f : (InfinitePlace K → ℝ) → ℂ) :
    Integrable (fun p : ℝ × logSpace K => f (numberFieldRadialLogParam p)) ↔ Integrable f := by
  change Integrable (f ∘ numberFieldRadialLogParam) ↔ _
  rw [← measurableEmbedding_numberFieldRadialLogParam.integrable_map_iff,
    map_numberFieldRadialLogParam_volume]
  exact integrable_smul_measure ((ENNReal.ofReal_pos.mpr radialLogDensity_pos).ne')
    ENNReal.ofReal_ne_top

/-- Complex integration in radial/unit-log coordinates has the same exact Jacobian. -/
theorem integral_numberFieldRadialLogParam (f : (InfinitePlace K → ℝ) → ℂ) :
    (∫ p : ℝ × logSpace K, f (numberFieldRadialLogParam p)) =
      (((2 : ℝ) ^ nrComplexPlaces K / Module.finrank ℚ K : ℝ) : ℂ) * ∫ z, f z := by
  rw [← measurableEmbedding_numberFieldRadialLogParam.integral_map,
    map_numberFieldRadialLogParam_volume, integral_smul_measure,
    ENNReal.toReal_ofReal radialLogDensity_pos.le, Complex.real_smul]

end GaloisForLFunctions.HTGeometry