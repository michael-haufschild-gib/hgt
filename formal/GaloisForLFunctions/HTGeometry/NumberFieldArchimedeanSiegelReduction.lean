import GaloisForLFunctions.HTGeometry.NumberFieldArchimedeanJacobiActionReduction

/-!
# Siegel-set reduction of positive archimedean forms over a number field

Combines determinant-one Dirichlet-unit balancing of Jacobi weights with integral size reduction of
the unipotent Jacobi coordinates. Every positive archimedean form over `K` in dimension `m + 1` is
moved by a product-one unit diagonal and then by an element of `SL_{m+1}(𝓞 K)` to a form whose
Jacobi data has bounded unipotent part and weights that are, up to a factor `exp(± 2(m+1)R)`,
determined by the weighted place mean and the centered place profile average of the original log
weights. This is a reduction-theory (Siegel set) statement with constants depending only on `K`.

## Main results

- `numberFieldArchimedeanJacobiWeight_transposeConj`: acting by `Nᵀ` as in the size reduction
  leaves all Jacobi weights unchanged.
- `exists_numberFieldArchimedeanSiegelReductionRadius`: there are `R > 0` and `C ≥ 0` depending
  only on `K` such that every positive archimedean form `A` in dimension `m + 1` has Jacobi data `J`,
  units `u` with `∏ uᵢ = 1`, `g₂ ∈ SL_{m+1}(𝓞 K)` and Jacobi data `J₂` for `g₂ • (diag u • A)` with
  all strictly upper unipotent entries at most `C` and each weight `J₂(i, w)` within a factor
  `exp(± 2(m+1)R)` of `exp(mean_v log J(i, v)) · exp(centered profile average at w)`.

## Hypotheses

The main theorem is unconditional; all Jacobi data, units and integral matrices are constructed.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix NumberField
open scoped Classical NumberField

noncomputable section

variable {K : Type*} [Field K] [NumberField K]
variable {n : ℕ}

omit [NumberField K] in
/-- The transpose-conjugated Jacobi data has the same weights at every coordinate and place. -/
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

/-- Siegel-set reduction over `K`: field-only constants `R > 0`, `C ≥ 0` such that each positive
archimedean form, after a product-one unit diagonal and an `SL_{m+1}(𝓞 K)` element, has Jacobi
data with unipotent entries at most `C` and weights balanced to within `exp(± 2(m+1)R)`. -/
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
