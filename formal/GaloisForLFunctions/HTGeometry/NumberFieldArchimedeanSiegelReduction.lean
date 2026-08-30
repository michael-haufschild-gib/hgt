import GaloisForLFunctions.HTGeometry.NumberFieldArchimedeanJacobiActionReduction

namespace GaloisForLFunctions.HTGeometry

open Matrix NumberField
open scoped Classical NumberField

noncomputable section

variable {K : Type*} [Field K] [NumberField K]
variable {n : ℕ}

omit [NumberField K] in
theorem numberFieldArchimedeanJacobiWeight_transposeConj
    (A : numberFieldArchimedeanPositiveForms K n)
    (J : NumberFieldArchimedeanJacobiData A)
    (N : Matrix (Fin n) (Fin n) (𝓞 K)) (hdet : N.det = 1)
    (hN : IsMixedUnipotentUpper (numberFieldMixedOrderMatrix N))
    (i : Fin n) (w : InfinitePlace K) :
    numberFieldArchimedeanJacobiWeight
        (numberFieldArchimedeanJacobiTransposeConj A J N hdet hN) i w =
      numberFieldArchimedeanJacobiWeight J i w := by
  classical
  rw [numberFieldArchimedeanJacobiWeight,
    numberFieldArchimedeanJacobiWeight]
  split_ifs <;> rfl

theorem exists_numberFieldArchimedeanSiegelReductionRadius
    (K : Type*) [Field K] [NumberField K] :
    ∃ R C : ℝ, 0 < R ∧ 0 ≤ C ∧ ∀ (m : ℕ)
      (A : numberFieldArchimedeanPositiveForms K (m + 1)),
      ∃ J : NumberFieldArchimedeanJacobiData A,
        ∃ u : Fin (m + 1) → (𝓞 K)ˣ,
          ∃ hu : ∏ i, u i = 1,
            let A₁ := (numberFieldUnitSpecialLinear u hu) • A
            ∃ g₂ : Matrix.SpecialLinearGroup (Fin (m + 1)) (𝓞 K),
              ∃ J₂ : NumberFieldArchimedeanJacobiData (g₂ • A₁),
                (∀ w i j, i < j → |J₂.realU w i j| ≤ C) ∧
                (∀ w i j, i < j → ‖J₂.complexU w i j‖ ≤ C) ∧
                ∀ i w,
                        Real.exp (-(2 * (m + 1 : ℝ) * R)) *
                              (Real.exp (numberFieldWeightedPlaceMean
                                  (fun v => Real.log
                                    (numberFieldArchimedeanJacobiWeight J i v))) *
                                Real.exp (numberFieldCenteredPlaceProfileAverage
                                  (fun j v => Real.log
                                    (numberFieldArchimedeanJacobiWeight J j v)) w)) ≤
                          numberFieldArchimedeanJacobiWeight J₂ i w ∧
                        numberFieldArchimedeanJacobiWeight J₂ i w ≤
                          Real.exp (2 * (m + 1 : ℝ) * R) *
                              (Real.exp (numberFieldWeightedPlaceMean
                                  (fun v => Real.log
                                    (numberFieldArchimedeanJacobiWeight J i v))) *
                                Real.exp (numberFieldCenteredPlaceProfileAverage
                                  (fun j v => Real.log
                                    (numberFieldArchimedeanJacobiWeight J j v)) w)) := by
  obtain ⟨R, hR, hbalance⟩ :=
    exists_numberFieldArchimedeanJacobiUnitConj_balancingRadius (K := K)
  obtain ⟨C, hC, hreduce⟩ :=
    exists_numberFieldArchimedeanJacobi_sizeReductionRadius K
  refine ⟨R, C, hR, hC, ?_⟩
  intro m A
  obtain ⟨J, u, hu, J₁, hbounds⟩ := hbalance m A
  obtain ⟨N, hdet, hN, hreal, hcomplex⟩ := hreduce (m + 1)
    ((numberFieldUnitSpecialLinear u hu) • A) J₁
  let g₂ := numberFieldTransposeSpecialLinear N hdet
  let J₂ : NumberFieldArchimedeanJacobiData
      (g₂ • ((numberFieldUnitSpecialLinear u hu) • A)) :=
    numberFieldArchimedeanJacobiTransposeConj
      ((numberFieldUnitSpecialLinear u hu) • A) J₁ N hdet hN
  refine ⟨J, u, hu, g₂, J₂, hreal, hcomplex, ?_⟩
  intro i w
  rw [show numberFieldArchimedeanJacobiWeight J₂ i w =
      numberFieldArchimedeanJacobiWeight J₁ i w by
    exact numberFieldArchimedeanJacobiWeight_transposeConj
      ((numberFieldUnitSpecialLinear u hu) • A) J₁ N hdet hN i w]
  exact hbounds i w

end

end GaloisForLFunctions.HTGeometry
