import GaloisForLFunctions.HTGeometry.NumberFieldArchimedeanJacobiUnitConj

/-!
# Unconditional determinant-one unit reduction of Jacobi weights

For every positive archimedean form, simultaneous real/complex Jacobi data and a product-one unit
diagonal are constructed internally.  The transformed form receives transported Jacobi data whose
weights obey the uniform field-only balancing bounds.
-/

namespace GaloisForLFunctions.HTGeometry

open NumberField
open scoped Classical NumberField

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

theorem exists_numberFieldArchimedeanJacobiUnitConj_balancingRadius :
    ∃ R : ℝ, 0 < R ∧ ∀ (m : ℕ)
      (A : numberFieldArchimedeanPositiveForms K (m + 1)),
      ∃ J : NumberFieldArchimedeanJacobiData A,
        ∃ u : Fin (m + 1) → (𝓞 K)ˣ,
          ∃ hu : ∏ i, u i = 1,
            ∃ J' : NumberFieldArchimedeanJacobiData
                ((numberFieldUnitSpecialLinear u hu) • A),
              ∀ i w,
                Real.exp (-(2 * (m + 1 : ℝ) * R)) *
                      (Real.exp (numberFieldWeightedPlaceMean
                          (fun v => Real.log (numberFieldArchimedeanJacobiWeight J i v))) *
                        Real.exp (numberFieldCenteredPlaceProfileAverage
                          (fun j v => Real.log
                            (numberFieldArchimedeanJacobiWeight J j v)) w)) ≤
                  numberFieldArchimedeanJacobiWeight J' i w ∧
                numberFieldArchimedeanJacobiWeight J' i w ≤
                  Real.exp (2 * (m + 1 : ℝ) * R) *
                      (Real.exp (numberFieldWeightedPlaceMean
                          (fun v => Real.log (numberFieldArchimedeanJacobiWeight J i v))) *
                        Real.exp (numberFieldCenteredPlaceProfileAverage
                          (fun j v => Real.log
                            (numberFieldArchimedeanJacobiWeight J j v)) w)) := by
  obtain ⟨R, hR, hbalance⟩ :=
    exists_numberFieldArchimedeanJacobi_balancingRadius (K := K)
  refine ⟨R, hR, ?_⟩
  intro m A
  obtain ⟨J, u, hu, hbounds⟩ := hbalance m A
  let J' : NumberFieldArchimedeanJacobiData
      ((numberFieldUnitSpecialLinear u hu) • A) :=
    numberFieldArchimedeanJacobiUnitConj A J u hu
  refine ⟨J, u, hu, J', ?_⟩
  intro i w
  rw [show numberFieldArchimedeanJacobiWeight J' i w =
      numberFieldArchimedeanJacobiWeight J i w *
        (w (((u i : 𝓞 K) : K))) ^ 2 by
    exact numberFieldArchimedeanJacobiWeight_unitConj A J u hu i w]
  exact hbounds i w

end

end GaloisForLFunctions.HTGeometry
