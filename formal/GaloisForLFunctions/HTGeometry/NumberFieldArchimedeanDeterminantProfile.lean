import GaloisForLFunctions.HTGeometry.NumberFieldArchimedeanLeadingMinorDescent

/-!
# Orbit-invariant archimedean determinant profile

The product of all Jacobi weights at one infinite place is the determinant of the local positive
form.  Consequently the place-only term produced by double-centering logarithmic Jacobi weights is
the normalized centered log-determinant profile.  Special-linear congruence preserves this profile
exactly at every real and complex place.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix NumberField NumberField.InfinitePlace
open scoped Classical ComplexOrder NumberField BigOperators

noncomputable section

variable {K : Type*} [Field K] [NumberField K]
variable {n : ℕ}

/-- Positive real determinant of a local archimedean form. -/
def numberFieldArchimedeanDet
    (A : numberFieldArchimedeanPositiveForms K n) (w : InfinitePlace K) : ℝ :=
  if hw : w.IsReal then
    (A.1.1 ⟨w, hw⟩ : Matrix (Fin n) (Fin n) ℝ).det
  else
    (A.1.2 ⟨w, InfinitePlace.not_isReal_iff_isComplex.mp hw⟩ :
      Matrix (Fin n) (Fin n) ℂ).det.re

omit [NumberField K] in
/-- The local determinant is the product of all simultaneous Jacobi weights. -/
theorem numberFieldArchimedeanDet_eq_prod_weight
    {A : numberFieldArchimedeanPositiveForms K n}
    (J : NumberFieldArchimedeanJacobiData A) (w : InfinitePlace K) :
    numberFieldArchimedeanDet A w =
      ∏ i, numberFieldArchimedeanJacobiWeight J i w := by
  classical
  rw [numberFieldArchimedeanDet]
  split_ifs with hw
  · rw [← J.realJacobiData_form ⟨w, hw⟩, JacobiData.det_form]
    simp [numberFieldArchimedeanJacobiWeight,
      NumberFieldArchimedeanJacobiData.realJacobiData, hw]
  · let wc : {w : InfinitePlace K // w.IsComplex} :=
      ⟨w, InfinitePlace.not_isReal_iff_isComplex.mp hw⟩
    rw [← J.complexJacobiData_form wc, ComplexJacobiData.det_form]
    simp [numberFieldArchimedeanJacobiWeight,
      NumberFieldArchimedeanJacobiData.complexJacobiData, hw, wc]
    norm_cast

omit [NumberField K] in
/-- Every local archimedean determinant is strictly positive. -/
theorem numberFieldArchimedeanDet_pos
    {A : numberFieldArchimedeanPositiveForms K n}
    (J : NumberFieldArchimedeanJacobiData A) (w : InfinitePlace K) :
    0 < numberFieldArchimedeanDet A w := by
  rw [numberFieldArchimedeanDet_eq_prod_weight J w]
  exact Finset.prod_pos fun i _ => numberFieldArchimedeanJacobiWeight_pos J i w

omit [NumberField K] in
/-- Sum of logarithmic Jacobi weights is the logarithm of the local determinant. -/
theorem sum_log_numberFieldArchimedeanJacobiWeight
    {A : numberFieldArchimedeanPositiveForms K n}
    (J : NumberFieldArchimedeanJacobiData A) (w : InfinitePlace K) :
    ∑ i, Real.log (numberFieldArchimedeanJacobiWeight J i w) =
      Real.log (numberFieldArchimedeanDet A w) := by
  rw [numberFieldArchimedeanDet_eq_prod_weight J w,
    Real.log_prod (fun i _ => (numberFieldArchimedeanJacobiWeight_pos J i w).ne')]

omit [NumberField K] in
/-- The local determinant profile is invariant under integral special-linear congruence. -/
theorem numberFieldArchimedeanDet_smul
    (A : numberFieldArchimedeanPositiveForms K n)
    (g : Matrix.SpecialLinearGroup (Fin n) (𝓞 K))
    (w : InfinitePlace K) :
    numberFieldArchimedeanDet (g • A) w = numberFieldArchimedeanDet A w := by
  classical
  rw [numberFieldArchimedeanDet, numberFieldArchimedeanDet]
  split_ifs with hw
  · let G := numberFieldRealOrderMatrixAt ⟨w, hw⟩
      (g : Matrix (Fin n) (Fin n) (𝓞 K))
    change (G * (A.1.1 ⟨w, hw⟩ : Matrix (Fin n) (Fin n) ℝ) *
      Matrix.conjTranspose G).det = _
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose,
      numberFieldRealSpecialLinearAt_det]
    simp
  · let wc : {w : InfinitePlace K // w.IsComplex} :=
      ⟨w, InfinitePlace.not_isReal_iff_isComplex.mp hw⟩
    let G := numberFieldComplexOrderMatrixAt wc
      (g : Matrix (Fin n) (Fin n) (𝓞 K))
    change (G * (A.1.2 wc : Matrix (Fin n) (Fin n) ℂ) *
      Matrix.conjTranspose G).det.re = _
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose,
      numberFieldComplexSpecialLinearAt_det]
    simp [wc]

/-- Weighted place mean commutes with a finite coordinate sum. -/
theorem sum_numberFieldWeightedPlaceMean {ι : Type*} [Fintype ι]
    (f : ι → InfinitePlace K → ℝ) :
    ∑ i, numberFieldWeightedPlaceMean (f i) =
      numberFieldWeightedPlaceMean (fun w => ∑ i, f i w) := by
  classical
  simp_rw [numberFieldWeightedPlaceMean]
  rw [← Finset.sum_div]
  apply congrArg (fun x : ℝ => x / numberFieldInfinitePlaceWeight (K := K))
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  rw [Finset.mul_sum]

/-- Double-centering equals coordinate sum minus its weighted place mean, divided by coordinate
count. -/
theorem numberFieldCenteredPlaceProfileAverage_apply {m : ℕ}
    (f : Fin (m + 1) → InfinitePlace K → ℝ) (w : InfinitePlace K) :
    numberFieldCenteredPlaceProfileAverage f w =
      ((∑ i, f i w) -
        numberFieldWeightedPlaceMean (fun v => ∑ i, f i v)) / (m + 1 : ℝ) := by
  rw [numberFieldCenteredPlaceProfileAverage]
  simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply,
    numberFieldCenteredPlaceProfile]
  rw [Finset.sum_sub_distrib, sum_numberFieldWeightedPlaceMean]
  ring

/-- The place-only centered Jacobi term is the normalized centered log-determinant profile. -/
theorem numberFieldCenteredJacobiProfile_eq_detProfile {m : ℕ}
    {A : numberFieldArchimedeanPositiveForms K (m + 1)}
    (J : NumberFieldArchimedeanJacobiData A) (w : InfinitePlace K) :
    numberFieldCenteredPlaceProfileAverage
        (fun i v => Real.log (numberFieldArchimedeanJacobiWeight J i v)) w =
      (Real.log (numberFieldArchimedeanDet A w) -
        numberFieldWeightedPlaceMean
          (fun v => Real.log (numberFieldArchimedeanDet A v))) / (m + 1 : ℝ) := by
  rw [numberFieldCenteredPlaceProfileAverage_apply]
  have hfun : (fun v => ∑ i,
      Real.log (numberFieldArchimedeanJacobiWeight J i v)) =
      fun v => Real.log (numberFieldArchimedeanDet A v) := by
    funext v
    exact sum_log_numberFieldArchimedeanJacobiWeight J v
  rw [sum_log_numberFieldArchimedeanJacobiWeight J w, hfun]

/-- The centered place term of simultaneous Jacobi data is an orbit invariant. -/
theorem numberFieldCenteredJacobiProfile_smul {m : ℕ}
    {A : numberFieldArchimedeanPositiveForms K (m + 1)}
    (J : NumberFieldArchimedeanJacobiData A)
    (g : Matrix.SpecialLinearGroup (Fin (m + 1)) (𝓞 K))
    (J' : NumberFieldArchimedeanJacobiData (g • A))
    (w : InfinitePlace K) :
    numberFieldCenteredPlaceProfileAverage
        (fun i v => Real.log (numberFieldArchimedeanJacobiWeight J' i v)) w =
      numberFieldCenteredPlaceProfileAverage
        (fun i v => Real.log (numberFieldArchimedeanJacobiWeight J i v)) w := by
  rw [numberFieldCenteredJacobiProfile_eq_detProfile,
    numberFieldCenteredJacobiProfile_eq_detProfile]
  simp_rw [numberFieldArchimedeanDet_smul A g]

end

end GaloisForLFunctions.HTGeometry
